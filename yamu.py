import asyncio
import hashlib
import html
import logging
import os
import re
import shutil
import tempfile
import time
from http.cookiejar import MozillaCookieJar
from functools import partial
from pathlib import Path
from typing import Any, Awaitable, Callable, List, Sequence, Tuple
from urllib.parse import urlparse

import requests
from aiogram import Bot, Dispatcher, F, Router, types
from aiogram.client.default import DefaultBotProperties
from aiogram.client.session.aiohttp import AiohttpSession
from aiogram.client.telegram import TelegramAPIServer
from aiogram.enums import MessageEntityType, ParseMode
from aiogram.exceptions import TelegramBadRequest, TelegramNetworkError
from aiogram.filters import Command, CommandStart
from aiogram.types import ReplyKeyboardRemove
from aiogram.utils.chat_action import ChatActionSender
from dotenv import load_dotenv
from yt_dlp import YoutubeDL
from yt_dlp.extractor.yandexmusic import YandexMusicBaseIE, YandexMusicTrackIE

load_dotenv()
router = Router()

YANDEX_MUSIC_DOMAINS = (
    "music.yandex.ru",
    "music.yandex.com",
    "music.yandex.kz",
    "music.yandex.by",
    "music.yandex.ua",
)
SOURCE_LABEL = "Yandex Music"

TELEGRAM_CAPTION_LIMIT = 1024
MAX_TELEGRAM_FILE_BYTES = 2 * 1024 * 1024 * 1024
REQUEST_TIMEOUT_SEC = 2 * 60 * 60
NETWORK_RETRY_ATTEMPTS = 3
NETWORK_RETRY_BACKOFF_SEC = 3
DOWNLOAD_RETRY_ATTEMPTS = 3
DOWNLOAD_RETRY_BACKOFF_SEC = 2
PREVIEW_MIN_EXPECTED_SECONDS = 90
PREVIEW_RATIO_THRESHOLD = 0.55
PREVIEW_HARD_MAX_SECONDS = 35
ALBUM_PREVIEW_RECOVERY_ROUNDS = 6
ALBUM_PREVIEW_COOKIES_RETRIES = 3
ALBUM_PREVIEW_ANON_RETRIES = 1
ALBUM_PREVIEW_ROUND_BACKOFF_SEC = 2

AUDIO_EXTS = {".mp3", ".m4a", ".aac", ".ogg", ".opus", ".flac", ".wav", ".webm"}
WINDOWS_INVALID_FILENAME_RE = re.compile(r'[<>:"/\\|?*\x00-\x1f]')
TRACK_WITH_ALBUM_RE = re.compile(r"/album/(?P<album>\d+)/track/(?P<track>\d+)")
TRACK_ONLY_RE = re.compile(r"/track/(?P<track>\d+)")
ALBUM_ONLY_RE = re.compile(r"^/album/(?P<album>\d+)/?$")
TRAILING_TRACK_ID_RE = re.compile(r"-(?P<track>\d+)(?::\d+)?$")

YANDEX_AUTH_ERROR_MARKERS = ("captcha", "403", "forbidden", "login")
YANDEX_INVALID_COOKIES_MARKERS = (
    "cookie does not start from magic-byte",
    "invalid cookie",
)
TRANSIENT_NETWORK_ERROR_MARKERS = (
    "timed out",
    "connection aborted",
    "connection reset",
    "connectionreseterror",
    "winerror 10054",
    "transporterror",
    "temporarily unavailable",
    "remote end closed connection",
    "max retries exceeded",
    "internal server error",
    "api.music.yandex.net",
    "argument of type 'bool' is not iterable",
)

_YTDLP_YANDEX_PATCHED = False


def _human_size(num_bytes: int) -> str:
    if num_bytes < 1024:
        return f"{num_bytes} B"
    units = ["KB", "MB", "GB", "TB"]
    value = float(num_bytes)
    for unit in units:
        value /= 1024.0
        if value < 1024.0:
            return f"{value:.2f} {unit}"
    return f"{value:.2f} PB"


def _format_iec_size(num_bytes: float | int | None) -> str:
    if not num_bytes or num_bytes <= 0:
        return "?"
    units = ["B", "KiB", "MiB", "GiB", "TiB"]
    value = float(num_bytes)
    for unit in units:
        if value < 1024.0 or unit == units[-1]:
            if unit == "B":
                return f"{int(value)}{unit}"
            return f"{value:.2f}{unit}"
        value /= 1024.0
    return f"{value:.2f}PiB"


def _format_iec_speed(bytes_per_sec: float | int | None) -> str:
    if not bytes_per_sec or bytes_per_sec <= 0:
        return "?"
    return f"{_format_iec_size(bytes_per_sec)}/s"


def _format_eta_clock(eta_sec: float | int | None) -> str:
    if eta_sec is None:
        return "??:??"
    sec = max(0, int(eta_sec))
    minutes, seconds = divmod(sec, 60)
    hours, minutes = divmod(minutes, 60)
    if hours:
        return f"{hours:02d}:{minutes:02d}:{seconds:02d}"
    return f"{minutes:02d}:{seconds:02d}"


def _build_yt_dlp_progress_line(data: dict[str, Any]) -> str | None:
    status = data.get("status")
    if status == "downloading":
        downloaded = data.get("downloaded_bytes") or 0
        total = data.get("total_bytes") or data.get("total_bytes_estimate") or 0
        speed = data.get("speed")
        eta = data.get("eta")

        if total and total > 0:
            percent = (float(downloaded) / float(total)) * 100.0
            return (
                f"[download] {percent:5.1f}% of {_format_iec_size(total)} "
                f"at {_format_iec_speed(speed)} ETA {_format_eta_clock(eta)}"
            )

        return (
            f"[download] {_format_iec_size(downloaded)} downloaded "
            f"at {_format_iec_speed(speed)} ETA {_format_eta_clock(eta)}"
        )

    if status == "finished":
        total = data.get("total_bytes") or data.get("downloaded_bytes") or 0
        return f"[download] 100.0% of {_format_iec_size(total)} at ? ETA 00:00"

    return None


def _normalize_candidate_url(raw: str) -> str | None:
    candidate = raw.strip().strip("<>()[]{}\"'.,!?")
    if not candidate:
        return None
    if candidate.startswith("www."):
        return f"https://{candidate}"
    if candidate.startswith(("http://", "https://")):
        return candidate
    return None


def _extract_url_from_entities(
    text: str, entities: Sequence[types.MessageEntity] | None
) -> str | None:
    if not text or not entities:
        return None

    for entity in entities:
        if entity.type == MessageEntityType.TEXT_LINK and entity.url:
            return entity.url

        if entity.type == MessageEntityType.URL:
            piece = text[entity.offset : entity.offset + entity.length]
            normalized = _normalize_candidate_url(piece)
            if normalized:
                return normalized

    return None


def extract_url_from_message(message: types.Message) -> str | None:
    content_sources = (
        (message.text or "", message.entities),
        (message.caption or "", message.caption_entities),
    )

    for text, entities in content_sources:
        if not text:
            continue

        url = _extract_url_from_entities(text, entities)
        if url:
            return url

        for part in text.split():
            normalized = _normalize_candidate_url(part)
            if normalized:
                return normalized

    return None


def is_yandex_music_url(url: str) -> bool:
    parsed = urlparse(url)
    host = (parsed.netloc or "").lower()
    host = host[4:] if host.startswith("www.") else host
    return any(domain in host for domain in YANDEX_MUSIC_DOMAINS)


def local_bot_api_url() -> str:
    for key in ("LOCAL_BOT_API_URL", "BOT_API_LOCAL_URL", "TELEGRAM_LOCAL_API_URL"):
        val = (os.getenv(key) or "").strip()
        if not val:
            continue

        parsed = urlparse(val)
        host = (parsed.hostname or "").lower()

        if parsed.scheme not in {"http", "https"}:
            raise RuntimeError(
                f"{key} must start with http:// or https://. Current value: {val}"
            )
        if not host:
            raise RuntimeError(f"{key} is invalid: {val}")
        if host == "api.telegram.org" or host.endswith(".telegram.org"):
            raise RuntimeError(
                "Local mode is required. Do not use api.telegram.org; "
                "set LOCAL_BOT_API_URL to your own telegram-bot-api server."
            )

        return val.rstrip("/")

    raise RuntimeError("Set LOCAL_BOT_API_URL in .env, example: http://127.0.0.1:8081")


def build_local_session() -> AiohttpSession:
    base_url = local_bot_api_url()
    api_server = TelegramAPIServer.from_base(base_url, is_local=True)
    return AiohttpSession(api=api_server, timeout=REQUEST_TIMEOUT_SEC)


def cookies_path_for_yandex_music() -> str | None:
    for key in ("COOKIES_YANDEX_MUSIC", "COOKIES_YANDEX", "YANDEX_MUSIC_COOKIES"):
        path_from_env = (os.getenv(key) or "").strip()
        if path_from_env and Path(path_from_env).is_file():
            return path_from_env

    local = Path("cookies_yandex_music.txt")
    if local.is_file():
        return str(local)

    return None


def _cookies_file_looks_invalid(path: str) -> bool:
    try:
        text = Path(path).read_text(encoding="utf-8", errors="ignore").lower()
    except Exception:
        return False

    return ("\tsessionid2\t" in text) and ("fakesign" in text)


def _collect_paths_from_dir(tmp_dir: Path) -> List[Path]:
    return [path for path in tmp_dir.rglob("*") if path.is_file()]


def _collect_paths_from_ytdlp_info(info: dict) -> List[Path]:
    paths: set[Path] = set()

    def add_from(obj: dict | None) -> None:
        if not obj:
            return

        if obj.get("_filename"):
            paths.add(Path(obj["_filename"]))

        for item in obj.get("requested_downloads") or []:
            file_path = item.get("filepath") or item.get("_filename")
            if file_path:
                paths.add(Path(file_path))

    add_from(info)
    for entry in info.get("entries") or []:
        add_from(entry)

    return [path for path in paths if path.exists()]


def pick_caption_from_info(info: dict | None) -> str | None:
    if not info:
        return None

    for key in ("title", "description"):
        value = (info.get(key) or "").strip()
        if value:
            return value

    for entry in info.get("entries") or []:
        if not isinstance(entry, dict):
            continue
        for key in ("title", "description"):
            value = (entry.get(key) or "").strip()
            if value:
                return value

    return None


def pick_thumbnail_from_info(info: dict | None) -> str | None:
    if not info:
        return None

    thumb = (info.get("thumbnail") or "").strip()
    if thumb:
        return thumb

    for entry in info.get("entries") or []:
        if not isinstance(entry, dict):
            continue
        thumb = (entry.get("thumbnail") or "").strip()
        if thumb:
            return thumb

    return None


def pick_duration_from_info(info: dict | None) -> float | None:
    if not info:
        return None

    duration = info.get("duration")
    if isinstance(duration, (int, float)) and duration > 0:
        return float(duration)

    for entry in info.get("entries") or []:
        if not isinstance(entry, dict):
            continue
        duration = entry.get("duration")
        if isinstance(duration, (int, float)) and duration > 0:
            return float(duration)

    return None


def _probe_audio_duration_seconds(path: Path) -> float | None:
    try:
        from mutagen import File as MutagenFile
    except Exception:
        return None

    try:
        audio = MutagenFile(path)
        if not audio or not getattr(audio, "info", None):
            return None
        length = float(getattr(audio.info, "length", 0.0) or 0.0)
        if length <= 0:
            return None
        return length
    except Exception:
        return None


def _format_mm_ss(seconds: float | int | None) -> str:
    if not seconds:
        return "00:00"
    total = max(0, int(round(float(seconds))))
    minutes, sec = divmod(total, 60)
    hours, minutes = divmod(minutes, 60)
    if hours:
        return f"{hours:02d}:{minutes:02d}:{sec:02d}"
    return f"{minutes:02d}:{sec:02d}"


def _build_preview_warning(files: Sequence[Path], info: dict | None) -> str | None:
    if len(files) != 1 or not is_audio(files[0]):
        return None

    expected = pick_duration_from_info(info)
    if not expected or expected < PREVIEW_MIN_EXPECTED_SECONDS:
        return None

    actual = _probe_audio_duration_seconds(files[0])
    if not actual:
        return None

    if actual >= expected * PREVIEW_RATIO_THRESHOLD:
        return None

    return (
        f"Only a preview was downloaded: {_format_mm_ss(actual)} of {_format_mm_ss(expected)}.\n"
        "Yandex returned a short demo fragment (usually due account/cookies access limits)."
    )


def _looks_like_album_url(url: str) -> bool:
    path = urlparse(url).path or ""
    return bool(ALBUM_ONLY_RE.fullmatch(path))


def _album_id_from_url(url: str) -> str | None:
    path = urlparse(url).path or ""
    match = ALBUM_ONLY_RE.fullmatch(path)
    if not match:
        return None
    return match.group("album")


def _track_id_from_file(path: Path) -> str | None:
    stem = path.stem
    alt = re.search(r"-(?P<track>\d+)-\d+$", stem)
    if alt:
        return alt.group("track")

    match = TRAILING_TRACK_ID_RE.search(stem)
    if match:
        return match.group("track")

    numbers = re.findall(r"\d+", stem)
    if not numbers:
        return None
    if len(numbers) >= 2 and len(numbers[-1]) >= 7 and len(numbers[-2]) >= 7:
        return numbers[-2]
    return numbers[-1]


def _track_id_from_text(value: Any) -> str | None:
    if value is None:
        return None
    text = str(value).strip()
    if not text:
        return None

    direct = re.fullmatch(r"(?P<track>\d+)(?::\d+)?", text)
    if direct:
        return direct.group("track")

    path = urlparse(text).path or ""
    match = TRACK_WITH_ALBUM_RE.search(path) or TRACK_ONLY_RE.search(path)
    if match:
        return match.group("track")

    return None


def _entry_duration_seconds(entry: dict[str, Any]) -> float | None:
    duration = entry.get("duration")
    if isinstance(duration, (int, float)) and duration > 0:
        return float(duration)
    return None


def _entry_track_ref_url(
    entry: dict[str, Any], host: str, fallback_album_id: str | None
) -> tuple[str, float | None] | None:
    duration = _entry_duration_seconds(entry)

    for key in ("webpage_url", "url"):
        raw = entry.get(key)
        if not isinstance(raw, str) or not raw.strip():
            continue
        path = urlparse(raw).path or ""
        full = TRACK_WITH_ALBUM_RE.search(path)
        if full:
            track_id = full.group("track")
            album_id = full.group("album")
            ref = f"https://{host}/album/{album_id}/track/{track_id}"
            return ref, duration

        track_only = TRACK_ONLY_RE.search(path)
        if track_only and fallback_album_id:
            track_id = track_only.group("track")
            ref = f"https://{host}/album/{fallback_album_id}/track/{track_id}"
            return ref, duration

    track_id = _track_id_from_text(entry.get("id")) or _track_id_from_text(
        entry.get("track_id")
    )
    if track_id and fallback_album_id:
        ref = f"https://{host}/album/{fallback_album_id}/track/{track_id}"
        return ref, duration

    return None


def _collect_album_track_refs(
    info: dict | None, host: str, fallback_album_id: str | None
) -> dict[str, tuple[str, float | None]]:
    refs: dict[str, tuple[str, float | None]] = {}
    if not isinstance(info, dict):
        return refs
    for entry in info.get("entries") or []:
        if not isinstance(entry, dict):
            continue
        ref_data = _entry_track_ref_url(entry, host, fallback_album_id)
        if not ref_data:
            continue
        ref_url, duration = ref_data
        track_id = _track_id_from_text(ref_url)
        if not track_id:
            continue
        if track_id in refs:
            continue
        refs[track_id] = (ref_url, duration)
    return refs


def _collect_album_track_refs_from_page(
    host: str, album_id: str
) -> dict[str, tuple[str, float | None]]:
    page_url = f"https://{host}/album/{album_id}"
    try:
        resp = requests.get(
            page_url,
            timeout=20,
            headers={
                "Accept-Language": "ru-RU,ru;q=0.9,en;q=0.8",
                "User-Agent": (
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/122.0.0.0 Safari/537.36"
                ),
            },
        )
        resp.raise_for_status()
    except Exception as exc:
        logging.warning("Failed to parse album page for track refs: %s", exc)
        return {}

    body = (resp.text or "").replace("\\/", "/")
    matches = re.findall(rf"/album/{album_id}/track/(\d+)", body)
    refs: dict[str, tuple[str, float | None]] = {}
    for track_id in matches:
        if track_id in refs:
            continue
        refs[track_id] = (
            f"https://{host}/album/{album_id}/track/{track_id}",
            None,
        )
    return refs


def _is_preview_by_duration(actual: float | None, expected: float | None) -> bool:
    if not actual or not expected:
        return False
    if expected < PREVIEW_MIN_EXPECTED_SECONDS:
        return False
    return actual < expected * PREVIEW_RATIO_THRESHOLD


def _is_preview_file(path: Path, expected: float | None) -> bool:
    actual = _probe_audio_duration_seconds(path)
    if _is_preview_by_duration(actual, expected):
        return True
    if expected is None and actual and actual <= PREVIEW_HARD_MAX_SECONDS:
        return True
    return False


def _build_album_preview_fallback_warning(
    skipped: int, replaced: int, total_preview: int
) -> str | None:
    if skipped <= 0:
        return None

    replaced_note = (
        f"{replaced}/{total_preview} preview track(s) recovered."
        if replaced
        else "No preview tracks recovered."
    )
    return (
        f"{replaced_note}\n"
        f"Skipped {skipped} track(s): Yandex returned only short preview fragments.\n"
        "Refresh Yandex cookies/account access and retry to get full tracks."
    )


def _recover_album_preview_tracks(
    source_url: str,
    files: Sequence[Path],
    info: dict | None,
    cookies_file: str | None,
    emit_progress: Callable[[str, bool], None],
) -> tuple[List[Path], str | None]:
    if not _looks_like_album_url(source_url):
        return list(files), None

    host = _yandex_music_host_from_url(source_url)
    album_id = _album_id_from_url(source_url)
    track_refs = _collect_album_track_refs(info, host, album_id)
    if not track_refs and album_id:
        track_refs = _collect_album_track_refs_from_page(host, album_id)
    if not track_refs:
        audio_files = [path for path in files if path.exists() and is_audio(path)]
        if audio_files and all(_is_preview_file(path, None) for path in audio_files):
            raise RuntimeError(
                "Yandex returned only short preview fragments for this album. "
                "Refresh Yandex cookies/account access and try again."
            )
        return list(files), None

    logging.info(
        "Album preview check: files=%s refs=%s source=%s",
        len(files),
        len(track_refs),
        source_url,
    )

    indexed: list[tuple[Path, str, float | None]] = []
    ordered_track_ids = list(track_refs.keys())
    audio_index = 0
    for path in files:
        if not path.exists() or not is_audio(path):
            indexed.append((path, "", None))
            continue
        track_id = _track_id_from_file(path) or ""
        if not track_id and audio_index < len(ordered_track_ids):
            track_id = ordered_track_ids[audio_index]
        expected = track_refs.get(track_id, ("", None))[1] if track_id else None
        indexed.append((path, track_id, expected))
        audio_index += 1

    preview_indices = [
        idx
        for idx, (path, track_id, expected) in enumerate(indexed)
        if track_id and path.exists() and _is_preview_file(path, expected)
    ]
    if not preview_indices:
        return [path for path, _, _ in indexed if path.exists()], None

    logging.warning(
        "Album preview detected: %s/%s track(s) look like 30s previews",
        len(preview_indices),
        len(track_refs),
    )

    emit_progress(
        f"[preview] detected {len(preview_indices)} short album track(s), retrying via direct API...",
        force=True,
    )

    replaced = 0
    unresolved: set[int] = set(preview_indices)

    for round_no in range(1, ALBUM_PREVIEW_RECOVERY_ROUNDS + 1):
        if not unresolved:
            break

        logging.info(
            "Album preview recovery round %s/%s: pending %s track(s)",
            round_no,
            ALBUM_PREVIEW_RECOVERY_ROUNDS,
            len(unresolved),
        )
        emit_progress(
            f"[preview] recovery round {round_no}/{ALBUM_PREVIEW_RECOVERY_ROUNDS}: "
            f"pending {len(unresolved)} track(s)...",
            force=True,
        )

        round_unresolved: set[int] = set()
        for idx in sorted(unresolved):
            old_path, track_id, expected = indexed[idx]
            ref_url, _ = track_refs.get(track_id, ("", None))
            if not ref_url and album_id:
                ref_url = f"https://{host}/album/{album_id}/track/{track_id}"
            if not ref_url:
                round_unresolved.add(idx)
                continue

            replacement: Path | None = None
            mode_plans: list[tuple[str | None, int]] = []
            if cookies_file:
                mode_plans.append((cookies_file, ALBUM_PREVIEW_COOKIES_RETRIES))
            mode_plans.append((None, ALBUM_PREVIEW_ANON_RETRIES))

            for attempt_cookies, mode_retries in mode_plans:
                for mode_try in range(1, mode_retries + 1):
                    try:
                        dl_files, dl_info = _download_yandex_track_via_api(
                            url=ref_url,
                            tmp_dir=old_path.parent,
                            cookies_file=attempt_cookies,
                            emit_progress=emit_progress,
                        )
                        if not dl_files:
                            continue

                        candidate = dl_files[0]
                        candidate_expected = expected
                        if not candidate_expected:
                            duration = (
                                dl_info.get("duration")
                                if isinstance(dl_info, dict)
                                else None
                            )
                            if isinstance(duration, (int, float)) and duration > 0:
                                candidate_expected = float(duration)
                        if _is_preview_file(candidate, candidate_expected):
                            candidate.unlink(missing_ok=True)
                            continue

                        replacement = candidate
                        break
                    except Exception as exc:
                        logging.warning(
                            "Direct API fallback failed for album track %s "
                            "(round=%s, cookies=%s, try=%s/%s): %s",
                            track_id,
                            round_no,
                            bool(attempt_cookies),
                            mode_try,
                            mode_retries,
                            exc,
                        )

                        if _is_yandex_auth_error(exc) and not attempt_cookies:
                            break

                        should_retry_mode = _is_transient_network_error(
                            exc
                        ) or _is_yandex_auth_error(exc)
                        if mode_try >= mode_retries or not should_retry_mode:
                            break

                        time.sleep(0.7 * mode_try)

                if replacement is not None:
                    break

            if replacement is None:
                round_unresolved.add(idx)
                continue

            if old_path != replacement:
                old_path.unlink(missing_ok=True)
            indexed[idx] = (replacement, track_id, expected)
            replaced += 1

        unresolved = round_unresolved
        if unresolved and round_no < ALBUM_PREVIEW_RECOVERY_ROUNDS:
            delay = ALBUM_PREVIEW_ROUND_BACKOFF_SEC * round_no
            emit_progress(
                f"[preview] waiting {delay}s before next retry round "
                f"({len(unresolved)} track(s) still pending)...",
                force=True,
            )
            time.sleep(delay)

    skipped = 0
    final_files: list[Path] = []
    for idx, (path, _, _) in enumerate(indexed):
        if idx in unresolved:
            path.unlink(missing_ok=True)
            skipped += 1
            continue
        if path.exists():
            final_files.append(path)

    if not final_files:
        raise RuntimeError(
            "Yandex returned only short preview fragments for this album. "
            "Refresh Yandex cookies/account access and try again."
        )

    warning = _build_album_preview_fallback_warning(
        skipped=skipped,
        replaced=replaced,
        total_preview=len(preview_indices),
    )
    return final_files, warning


def download_cover_image(thumbnail_url: str | None, tmp_dir: Path) -> Path | None:
    if not thumbnail_url:
        return None

    url = thumbnail_url.strip()
    if not url:
        return None
    if url.startswith("//"):
        url = "https:" + url

    try:
        resp = requests.get(
            url,
            timeout=20,
            stream=True,
            headers={"User-Agent": "Mozilla/5.0"},
        )
        resp.raise_for_status()
    except Exception as exc:
        logging.warning("Failed to download cover image: %s", exc)
        return None

    content_type = (resp.headers.get("Content-Type") or "").lower()
    ext = ".jpg"
    if "png" in content_type:
        ext = ".png"
    elif "webp" in content_type:
        ext = ".webp"

    target = tmp_dir / f"cover{ext}"
    total = 0
    limit = 10 * 1024 * 1024
    try:
        with target.open("wb") as fh:
            for chunk in resp.iter_content(chunk_size=64 * 1024):
                if not chunk:
                    continue
                total += len(chunk)
                if total > limit:
                    raise RuntimeError("cover image is too large")
                fh.write(chunk)
    except Exception as exc:
        logging.warning("Failed to save cover image: %s", exc)
        try:
            target.unlink(missing_ok=True)
        except Exception:
            pass
        return None
    finally:
        resp.close()

    return target if target.exists() else None


def _yandex_music_host_from_url(url: str) -> str:
    parsed = urlparse(url)
    host = (parsed.netloc or "music.yandex.ru").lower()
    if host.startswith("www."):
        host = host[4:]
    return host or "music.yandex.ru"


def _resolve_track_ids_from_url_or_page(
    session: requests.Session,
    host: str,
    url: str,
) -> tuple[str, str, str]:
    parsed = urlparse(url)
    path = parsed.path or ""

    m = TRACK_WITH_ALBUM_RE.search(path)
    if m:
        album_id = m.group("album")
        track_id = m.group("track")
        ref_url = f"https://{host}/album/{album_id}/track/{track_id}"
        return ref_url, track_id, album_id

    m = TRACK_ONLY_RE.search(path)
    if not m:
        raise RuntimeError("Direct Yandex API mode supports track links only.")
    track_id = m.group("track")

    page_url = f"https://{host}/track/{track_id}"
    resp = session.get(page_url, timeout=20, allow_redirects=True)
    body = resp.text or ""
    low_url = (resp.url or "").lower()
    low_body = body.lower()
    if "showcaptcha" in low_url or "showcaptcha" in low_body:
        raise RuntimeError("Yandex requested captcha for this session.")

    found = re.search(rf"album/(\d+)/track/{track_id}", body)
    if found:
        album_id = found.group(1)
        ref_url = f"https://{host}/album/{album_id}/track/{track_id}"
        return ref_url, track_id, album_id

    found = TRACK_WITH_ALBUM_RE.search(urlparse(resp.url).path or "")
    if found and found.group("track") == track_id:
        album_id = found.group("album")
        ref_url = f"https://{host}/album/{album_id}/track/{track_id}"
        return ref_url, track_id, album_id

    raise RuntimeError("Unable to resolve album id for track URL.")


def _join_artist_names(raw_artists: Any) -> str | None:
    if not isinstance(raw_artists, list):
        return None
    names: list[str] = []
    for artist in raw_artists:
        if not isinstance(artist, dict):
            continue
        name = (artist.get("name") or "").strip()
        if name:
            names.append(name)
    if not names:
        return None
    return ", ".join(names)


def _extract_track_payload_track(payload: dict[str, Any]) -> dict[str, Any]:
    track = payload.get("track")
    if isinstance(track, dict):
        return track
    return payload


def _download_yandex_track_via_api(
    url: str,
    tmp_dir: Path,
    cookies_file: str | None,
    emit_progress: Callable[[str, bool], None],
) -> tuple[List[Path], dict[str, Any]]:
    host = _yandex_music_host_from_url(url)
    session = requests.Session()
    session.headers.update(
        {
            "Accept-Language": "ru-RU,ru;q=0.9,en;q=0.8",
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/122.0.0.0 Safari/537.36"
            ),
        }
    )

    if cookies_file:
        cookie_jar = MozillaCookieJar(cookies_file)
        cookie_jar.load(ignore_discard=True, ignore_expires=True)
        session.cookies.update(cookie_jar)

    ref_url, track_id, album_id = _resolve_track_ids_from_url_or_page(
        session, host, url
    )
    emit_progress("[api] Resolved track metadata source...", force=True)

    api_headers = {
        "Referer": ref_url,
        "X-Requested-With": "XMLHttpRequest",
        "X-Retpath-Y": ref_url,
    }

    track_resp = session.get(
        f"https://{host}/handlers/track.jsx",
        params={"track": f"{track_id}:{album_id}"},
        headers=api_headers,
        timeout=20,
    )
    track_resp.raise_for_status()
    track_payload = track_resp.json()
    if isinstance(track_payload, dict) and (
        track_payload.get("type") == "captcha" or "captcha" in track_payload
    ):
        raise RuntimeError("Yandex requested captcha for this session.")
    track = _extract_track_payload_track(
        track_payload if isinstance(track_payload, dict) else {}
    )
    if not isinstance(track, dict):
        raise RuntimeError("Unexpected track payload from Yandex.")

    emit_progress("[api] Getting direct audio URL...", force=True)
    dl_resp = session.get(
        f"https://{host}/api/v2.1/handlers/track/{track_id}:{album_id}/web-album_track-track-track-main/download/m",
        params={"hq": 1},
        headers={"X-Retpath-Y": ref_url},
        timeout=20,
    )
    dl_resp.raise_for_status()
    download_data = dl_resp.json()
    src_url = (download_data.get("src") or "").strip()
    if not src_url:
        raise RuntimeError("Yandex download API returned empty source URL.")
    if src_url.startswith("//"):
        src_url = "https:" + src_url

    fd_resp = session.get(src_url, params={"format": "json"}, timeout=20)
    fd_resp.raise_for_status()
    fd_data = fd_resp.json()
    path = fd_data.get("path") or ""
    sig = fd_data.get("s") or ""
    ts = fd_data.get("ts") or ""
    media_host = fd_data.get("host") or "api.music.yandex.net"
    if not path or not sig or not ts:
        raise RuntimeError("Yandex location API returned incomplete metadata.")

    key = hashlib.md5(("XGRlBW9FXlekgbPrRHuSiA" + path[1:] + sig).encode()).hexdigest()
    mp3_url = f"https://{media_host}/get-mp3/{key}/{ts + path}?track-id={track_id}"

    artist_name = _join_artist_names(track.get("artists"))
    title = (track.get("title") or f"track-{track_id}").strip()
    display_title = f"{artist_name} - {title}" if artist_name else title
    stem = _sanitize_filename_stem(display_title, f"track-{track_id}")
    out_path = tmp_dir / f"{stem}-{track_id}.mp3"

    emit_progress("[download] Starting direct audio download...", force=True)
    media_resp = session.get(mp3_url, timeout=60, stream=True)
    media_resp.raise_for_status()
    total = int(media_resp.headers.get("Content-Length") or 0)
    downloaded = 0
    with out_path.open("wb") as out_fh:
        for chunk in media_resp.iter_content(chunk_size=64 * 1024):
            if not chunk:
                continue
            out_fh.write(chunk)
            downloaded += len(chunk)
            if total > 0:
                percent = (downloaded / total) * 100.0
                emit_progress(
                    f"[download] {percent:5.1f}% of {_format_iec_size(total)}",
                    force=False,
                )
    emit_progress(
        f"[download] 100.0% of {_format_iec_size(total or downloaded)}",
        force=True,
    )

    cover_uri = (track.get("coverUri") or "").strip()
    thumbnail = ""
    if cover_uri:
        thumbnail = cover_uri.replace("%%", "orig")
        if not thumbnail.startswith("http"):
            thumbnail = "https://" + thumbnail

    duration_sec: float | None = None
    duration_ms = track.get("durationMs")
    if isinstance(duration_ms, (int, float)) and duration_ms > 0:
        duration_sec = float(duration_ms) / 1000.0

    info = {
        "id": track_id,
        "title": display_title,
        "duration": duration_sec,
        "thumbnail": thumbnail,
    }
    return [out_path], info


def _looks_like_track_url(url: str) -> bool:
    path = urlparse(url).path or ""
    return bool(TRACK_WITH_ALBUM_RE.search(path) or TRACK_ONLY_RE.search(path))


def _has_any_marker(text: str, markers: Sequence[str]) -> bool:
    low = (text or "").lower()
    return any(marker in low for marker in markers)


def _is_yandex_auth_error(exc: Exception) -> bool:
    return _has_any_marker(str(exc), YANDEX_AUTH_ERROR_MARKERS)


def _is_yandex_invalid_cookies_error(exc: Exception) -> bool:
    return _has_any_marker(str(exc), YANDEX_INVALID_COOKIES_MARKERS)


def _is_transient_network_error(exc: Exception) -> bool:
    return _has_any_marker(str(exc), TRANSIENT_NETWORK_ERROR_MARKERS)


def _patch_ytdlp_yandexmusic_https() -> None:
    global _YTDLP_YANDEX_PATCHED
    if _YTDLP_YANDEX_PATCHED:
        return

    orig_download_json = YandexMusicBaseIE._download_json
    orig_real_extract = YandexMusicTrackIE._real_extract

    def patched_download_json(self: Any, *args: Any, **kwargs: Any) -> Any:
        if (
            args
            and isinstance(args[0], str)
            and args[0].startswith("//api.music.yandex.net/")
        ):
            args = ("https:" + args[0],) + args[1:]
        return orig_download_json(self, *args, **kwargs)

    def patched_real_extract(self: Any, url: str) -> Any:
        info = orig_real_extract(self, url)
        if (
            isinstance(info, dict)
            and isinstance(info.get("url"), str)
            and info["url"].startswith("http://api.music.yandex.net/")
        ):
            info["url"] = "https://" + info["url"][len("http://") :]
        return info

    YandexMusicBaseIE._download_json = patched_download_json
    YandexMusicTrackIE._real_extract = patched_real_extract
    _YTDLP_YANDEX_PATCHED = True


def _single_line_text(text: str | None) -> str:
    if not text:
        return ""
    normalized = text.replace("\r\n", "\n").replace("\r", "\n")
    normalized = re.sub(r"[ \t]+", " ", normalized)
    normalized = re.sub(r"\n{2,}", "\n", normalized).strip()
    for line in normalized.split("\n"):
        line = line.strip()
        if line:
            return line
    return normalized


def _sanitize_filename_stem(stem: str, fallback: str) -> str:
    cleaned = WINDOWS_INVALID_FILENAME_RE.sub("", stem)
    cleaned = re.sub(r"\s+", " ", cleaned).strip().rstrip(".")
    if not cleaned:
        return fallback
    return cleaned[:120]


def build_telegram_audio_title(
    path: Path, fallback_text: str | None = None
) -> str | None:
    stem = path.stem.replace("_", " ")
    stem = re.sub(r"-\d{4,}$", "", stem)
    stem = re.sub(r"\s+", " ", stem).strip(" .-_")
    if not stem:
        stem = _single_line_text(fallback_text)
    if not stem:
        return None
    if len(stem) > 64:
        stem = stem[:61].rstrip() + "..."
    return stem


def is_audio(path: Path) -> bool:
    return path.suffix.lower() in AUDIO_EXTS


def clean_caption(text: str) -> str:
    text = re.sub(r"[ \t]+", " ", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()


def build_media_caption(url: str, caption_text: str | None) -> str:
    safe_url = html.escape(url, quote=True)
    base = f'Source: <a href="{safe_url}">{SOURCE_LABEL}</a>'
    extra = clean_caption(caption_text or "")
    if not extra:
        return base

    full = f"{base}\n{html.escape(extra)}"
    if len(full) <= TELEGRAM_CAPTION_LIMIT:
        return full

    low, high = 0, len(extra)
    best = base
    while low <= high:
        mid = (low + high) // 2
        truncated = extra[:mid].rstrip()
        suffix = "..." if mid < len(extra) else ""
        candidate = f"{base}\n{html.escape(truncated)}{suffix}"
        if len(candidate) <= TELEGRAM_CAPTION_LIMIT:
            best = candidate
            low = mid + 1
        else:
            high = mid - 1
    return best


def download_yandex_music(
    url: str,
    progress_callback: Callable[[str], None] | None = None,
) -> Tuple[List[Path], Path, str | None, Path | None, str | None]:
    _patch_ytdlp_yandexmusic_https()
    tmp_dir = Path(tempfile.mkdtemp(prefix="yamu_"))
    last_progress_emit = 0.0
    last_progress_line = ""

    def emit_progress(line: str, force: bool = False) -> None:
        nonlocal last_progress_emit, last_progress_line
        if not progress_callback or not line:
            return
        now = time.monotonic()
        if not force:
            if line == last_progress_line and (now - last_progress_emit) < 2:
                return
            if (now - last_progress_emit) < 0.9:
                return
        last_progress_emit = now
        last_progress_line = line
        progress_callback(line)

    cookies_file = cookies_path_for_yandex_music()
    if cookies_file and _cookies_file_looks_invalid(cookies_file):
        logging.info(
            "Yandex cookies file has masked sessionid2 signature: %s. "
            "Will still try cookies first, then fallback to no-cookies on API errors.",
            cookies_file,
        )
        emit_progress(
            "[auth] cookies include masked session signature; trying authenticated mode..."
        )

    ydl_opts = {
        "outtmpl": str(tmp_dir / "%(title).180B-%(id)s.%(ext)s"),
        "noplaylist": False,
        "quiet": True,
        "retries": 2,
        "fragment_retries": 2,
        "socket_timeout": 20,
        "source_address": "0.0.0.0",
        "windowsfilenames": True,
        "format": "bestaudio/best",
        "http_headers": {
            "Accept-Language": "ru-RU,ru;q=0.9,en;q=0.8",
            "Referer": "https://music.yandex.ru/",
            "Origin": "https://music.yandex.ru",
        },
        "progress_hooks": [
            lambda data: (
                emit_progress(
                    _build_yt_dlp_progress_line(data) or "",
                    force=(data.get("status") == "finished"),
                )
            )
        ],
    }
    if shutil.which("ffmpeg"):
        ydl_opts["writethumbnail"] = True
        ydl_opts["postprocessors"] = [
            {"key": "FFmpegThumbnailsConvertor", "format": "jpg"},
            {"key": "EmbedThumbnail", "already_have_thumbnail": False},
            {"key": "FFmpegMetadata"},
        ]

    use_cookies = bool(cookies_file)

    if _looks_like_track_url(url):
        direct_attempts = [cookies_file] if use_cookies else []
        direct_attempts.append(None)
        for direct_cookies in direct_attempts:
            try:
                files, direct_info = _download_yandex_track_via_api(
                    url=url,
                    tmp_dir=tmp_dir,
                    cookies_file=direct_cookies,
                    emit_progress=emit_progress,
                )
                caption_text = pick_caption_from_info(direct_info)
                cover_path = download_cover_image(
                    pick_thumbnail_from_info(direct_info), tmp_dir
                )
                preview_warning = _build_preview_warning(files, direct_info)
                return files, tmp_dir, caption_text, cover_path, preview_warning
            except Exception as exc:
                if direct_cookies:
                    logging.warning(
                        "Direct API track mode with cookies failed: %s", exc
                    )
                    emit_progress(
                        "[api] direct mode with cookies failed, trying anonymous mode..."
                    )
                else:
                    logging.warning(
                        "Direct API track mode without cookies failed: %s", exc
                    )
                for stale in list(tmp_dir.glob("*")):
                    if stale.is_file():
                        stale.unlink(missing_ok=True)

    info: dict | None = None
    last_exc: Exception | None = None
    for attempt in range(1, DOWNLOAD_RETRY_ATTEMPTS + 1):
        try:
            run_opts = dict(ydl_opts)
            if use_cookies and cookies_file:
                run_opts["cookies"] = cookies_file
            with YoutubeDL(run_opts) as ydl:
                info = ydl.extract_info(url, download=True)
            break
        except Exception as exc:
            last_exc = exc
            if use_cookies and _is_yandex_invalid_cookies_error(exc):
                use_cookies = False
                emit_progress(
                    "[auth] cookies look invalid, retrying without cookies..."
                )
                logging.warning(
                    "Yandex Music cookies look invalid; retrying without cookies: %s",
                    exc,
                )
                continue
            if use_cookies and _has_any_marker(str(exc), ("internal server error",)):
                use_cookies = False
                emit_progress(
                    "[auth] Yandex rejected cookies, retrying without cookies..."
                )
                logging.warning(
                    "Yandex Music returned internal server error with cookies; retrying without cookies."
                )
                continue

            if _is_yandex_auth_error(exc):
                if use_cookies:
                    use_cookies = False
                    emit_progress(
                        "[auth] Yandex requested captcha with cookies, retrying without cookies..."
                    )
                    logging.warning(
                        "Yandex requested captcha with cookies; retrying without cookies."
                    )
                    continue
                raise RuntimeError(
                    "Yandex Music requested auth/captcha. Export cookies in Netscape "
                    "format and set COOKIES_YANDEX_MUSIC in .env."
                ) from exc

            if attempt >= DOWNLOAD_RETRY_ATTEMPTS or not _is_transient_network_error(
                exc
            ):
                raise

            wait_sec = DOWNLOAD_RETRY_BACKOFF_SEC * attempt
            emit_progress(
                f"[network] temporary Yandex API error ({attempt}/{DOWNLOAD_RETRY_ATTEMPTS}), "
                f"retrying in {wait_sec}s..."
            )
            time.sleep(wait_sec)

    if info is None:
        if last_exc:
            raise last_exc
        raise RuntimeError("Download failed before metadata was received.")

    files = _collect_paths_from_ytdlp_info(info)
    if not files:
        files = _collect_paths_from_dir(tmp_dir)

    if not files:
        raise RuntimeError("Download failed: empty result.")

    album_preview_warning: str | None = None
    files, album_preview_warning = _recover_album_preview_tracks(
        source_url=url,
        files=files,
        info=info,
        cookies_file=cookies_file,
        emit_progress=emit_progress,
    )

    caption_text = pick_caption_from_info(info)
    cover_path = download_cover_image(pick_thumbnail_from_info(info), tmp_dir)
    preview_warning = _build_preview_warning(files, info)
    if album_preview_warning:
        preview_warning = (
            f"{preview_warning}\n\n{album_preview_warning}"
            if preview_warning
            else album_preview_warning
        )
    return files, tmp_dir, caption_text, cover_path, preview_warning


def cleanup_tmp_dir(tmp_dir: Path | None) -> None:
    if not tmp_dir:
        return
    try:
        shutil.rmtree(tmp_dir, ignore_errors=True)
    except Exception:
        pass


async def _safe_edit_status(message: types.Message, text: str) -> bool:
    try:
        await message.edit_text(text, parse_mode=None)
        return True
    except TelegramBadRequest as exc:
        low = str(exc).lower()
        if "message is not modified" in low:
            return True
        if "message to edit not found" in low:
            return False
        logging.warning("Status edit rejected: %s", exc)
        return False
    except TelegramNetworkError as exc:
        logging.warning("Status edit network error: %s", exc)
        return False
    except Exception:
        logging.exception("Unexpected status edit error")
        return False


async def _safe_delete_status(message: types.Message) -> bool:
    try:
        await message.delete()
        return True
    except TelegramBadRequest as exc:
        low = str(exc).lower()
        if "message to delete not found" in low:
            return True
        logging.warning("Status delete rejected: %s", exc)
        return False
    except TelegramNetworkError as exc:
        logging.warning("Status delete network error: %s", exc)
        return False
    except Exception:
        logging.exception("Unexpected status delete error")
        return False


async def _send_with_retry(
    operation: str,
    sender: Callable[[], Awaitable[Any]],
    attempts: int = NETWORK_RETRY_ATTEMPTS,
) -> Any:
    last_exc: Exception | None = None
    for attempt in range(1, attempts + 1):
        try:
            return await sender()
        except TelegramNetworkError as exc:
            last_exc = exc
            if attempt >= attempts:
                break
            delay = NETWORK_RETRY_BACKOFF_SEC * attempt
            logging.warning(
                "%s failed (network) attempt %s/%s: %s. Retrying in %ss.",
                operation,
                attempt,
                attempts,
                exc,
                delay,
            )
            await asyncio.sleep(delay)
    if last_exc:
        raise last_exc
    raise RuntimeError(f"{operation} failed")


async def send_media_to_chat(
    bot: Bot,
    chat_id: int,
    files: Sequence[Path],
    source_url: str,
    caption_text: str | None = None,
    status_message: types.Message | None = None,
) -> None:
    existing = sorted(
        [path for path in files if path.exists()],
        key=lambda p: p.name.lower(),
    )
    if not existing:
        raise RuntimeError("No files were produced by downloader.")

    oversized = [
        path for path in existing if path.stat().st_size > MAX_TELEGRAM_FILE_BYTES
    ]
    sendable = [path for path in existing if path not in oversized]
    if not sendable:
        details = "\n".join(
            f"- {path.name} ({_human_size(path.stat().st_size)})"
            for path in oversized[:10]
        )
        raise RuntimeError(
            "All files are larger than 2 GiB and cannot be sent.\n" + details
        )

    caption_full = build_media_caption(source_url, caption_text)
    caption_used = False

    for index, path in enumerate(sendable, start=1):
        if status_message:
            await _safe_edit_status(
                status_message,
                f"Uploading to Telegram: {index}/{len(sendable)}\n{path.name}",
            )

        cap = caption_full if not caption_used else None
        if cap:
            caption_used = True

        if is_audio(path):
            audio_title = build_telegram_audio_title(path, caption_text)
            await _send_with_retry(
                f"send_audio {index}/{len(sendable)}",
                lambda p=path, c=cap, t=audio_title: bot.send_audio(
                    chat_id,
                    types.FSInputFile(p),
                    title=t,
                    caption=c,
                    parse_mode=ParseMode.HTML if c else None,
                    request_timeout=REQUEST_TIMEOUT_SEC,
                ),
            )
            continue

        await _send_with_retry(
            f"send_document {index}/{len(sendable)}",
            lambda p=path, c=cap: bot.send_document(
                chat_id,
                types.FSInputFile(p),
                caption=c,
                parse_mode=ParseMode.HTML if c else None,
                disable_content_type_detection=True,
                request_timeout=REQUEST_TIMEOUT_SEC,
            ),
        )

    if oversized:
        lines = [
            f"Not sent (over 2 GiB): {path.name} ({_human_size(path.stat().st_size)})"
            for path in oversized[:10]
        ]
        if len(oversized) > 10:
            lines.append(f"... and {len(oversized) - 10} more files")
        await _send_with_retry(
            "send_oversized_warning",
            lambda: bot.send_message(
                chat_id,
                "\n".join(lines),
                request_timeout=REQUEST_TIMEOUT_SEC,
            ),
        )


def _trim_error_text(text: str, max_len: int = 350) -> str:
    text = (text or "").strip()
    if len(text) <= max_len:
        return text
    return text[: max_len - 3].rstrip() + "..."


def _format_pipeline_error_text(exc: Exception) -> str:
    if _is_transient_network_error(exc):
        return (
            "Failed to reach Yandex Music API.\n"
            "Check VPN/network and availability of api.music.yandex.net, then try again."
        )
    return f"Failed to download or send:\n{_trim_error_text(str(exc))}"


@router.message(CommandStart())
async def cmd_start(message: types.Message) -> None:
    await message.answer(
        "Hi! I download from Yandex Music.\n"
        "Send a track/album/playlist link from music.yandex.*\n\n"
        "Command: /help",
        reply_markup=ReplyKeyboardRemove(),
    )


@router.message(Command("help"))
async def cmd_help(message: types.Message) -> None:
    await message.answer(
        "How to use:\n"
        "1) Send a Yandex Music link\n"
        "2) Bot downloads and sends audio files\n\n"
        "Optional cookies:\n"
        "Set COOKIES_YANDEX_MUSIC in .env to a Netscape cookies.txt file "
        "if Yandex asks for captcha/login.\n"
        "Without valid account access Yandex may return only a 30-second preview.",
        reply_markup=ReplyKeyboardRemove(),
    )


@router.message(F.text | F.caption)
async def handle_link(message: types.Message) -> None:
    url = extract_url_from_message(message)
    if not url:
        return

    if not is_yandex_music_url(url):
        await message.answer("Supported links: music.yandex.* only. Command /help")
        return

    try:
        await message.delete()
    except Exception:
        pass

    chat_id = message.chat.id
    status = await message.bot.send_message(
        chat_id,
        "Link accepted. Starting download...",
        parse_mode=None,
        request_timeout=REQUEST_TIMEOUT_SEC,
    )

    tmp_dir: Path | None = None
    try:
        loop = asyncio.get_running_loop()
        progress_state = {"line": ""}

        def on_download_progress(line: str) -> None:
            progress_state["line"] = line

        await _safe_edit_status(status, "Downloading from Yandex Music...")
        async with ChatActionSender.upload_document(bot=message.bot, chat_id=chat_id):
            download_job = partial(download_yandex_music, url, on_download_progress)
            download_task = loop.run_in_executor(None, download_job)
            last_status_line = ""
            while True:
                done, _ = await asyncio.wait({download_task}, timeout=1.0)
                if done:
                    files, tmp_dir, caption_text, cover_path, preview_warning = (
                        download_task.result()
                    )
                    break

                line = progress_state["line"]
                if line and line != last_status_line:
                    last_status_line = line
                    await _safe_edit_status(
                        status,
                        f"Downloading from Yandex Music...\n{line}",
                    )

        if progress_state["line"]:
            await _safe_edit_status(
                status,
                f"Download complete.\n{progress_state['line']}\nUploading...",
            )
        else:
            await _safe_edit_status(
                status, f"Download complete. Uploading {len(files)} file(s)..."
            )

        await send_media_to_chat(
            message.bot,
            chat_id,
            files,
            url,
            caption_text,
            status_message=status,
        )
        if cover_path and cover_path.exists():
            try:
                await _send_with_retry(
                    "send_cover_photo",
                    lambda p=cover_path: message.bot.send_photo(
                        chat_id,
                        types.FSInputFile(p),
                        request_timeout=REQUEST_TIMEOUT_SEC,
                    ),
                )
            except Exception as exc:
                logging.warning("Sending cover photo failed: %s", exc)

        if preview_warning:
            await _send_with_retry(
                "send_preview_warning",
                lambda t=preview_warning: message.bot.send_message(
                    chat_id,
                    t,
                    parse_mode=None,
                    request_timeout=REQUEST_TIMEOUT_SEC,
                ),
            )

        await _safe_delete_status(status)

    except Exception as exc:
        logging.exception("Yandex Music pipeline failed")
        error_text = _format_pipeline_error_text(exc)
        updated = await _safe_edit_status(status, error_text)
        if not updated:
            await _send_with_retry(
                "send_error_message",
                lambda: message.bot.send_message(
                    chat_id,
                    error_text,
                    parse_mode=None,
                    request_timeout=REQUEST_TIMEOUT_SEC,
                ),
            )
    finally:
        cleanup_tmp_dir(tmp_dir)


async def main() -> None:
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s | %(levelname)s | %(message)s",
    )

    token = (os.getenv("BOT_TOKEN") or "").strip()
    if not token:
        raise RuntimeError("Set BOT_TOKEN in .env")

    bot = Bot(
        token=token,
        default=DefaultBotProperties(parse_mode=ParseMode.HTML),
    )

    dispatcher = Dispatcher()
    dispatcher.include_router(router)

    await bot.set_my_commands(
        [types.BotCommand(command="help", description="How to use")]
    )

    try:
        await dispatcher.start_polling(bot, handle_signals=True)
    except (KeyboardInterrupt, asyncio.CancelledError):
        pass
    finally:
        await bot.session.close()


if __name__ == "__main__":
    asyncio.run(main())
