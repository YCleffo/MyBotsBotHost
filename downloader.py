import asyncio
import html
import json
import logging
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from http.cookiejar import MozillaCookieJar
from contextlib import suppress
from functools import partial
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Awaitable, Callable, List, Sequence, Tuple
from urllib import request
from urllib.parse import parse_qs, urlparse

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
from PIL import Image
from yt_dlp import YoutubeDL
import yamu

load_dotenv()
router = Router()

SUPPORTED_DOMAINS = {
    "instagram": ("instagram.com", "instagr.am"),
    "tiktok": ("tiktok.com", "vm.tiktok.com", "vt.tiktok.com"),
    "youtube": ("youtube.com", "youtu.be"),
    "yandex_music": (
        "music.yandex.ru",
        "music.yandex.com",
        "music.yandex.kz",
        "music.yandex.by",
        "music.yandex.ua",
    ),
}
SOURCE_LABELS = {
    "instagram": "Instagram",
    "tiktok": "TikTok",
    "youtube": "YouTube",
    "yandex_music": "Yandex Music",
}

TELEGRAM_CAPTION_LIMIT = 1024
TELEGRAM_TEXT_LIMIT = 4096
MAX_TELEGRAM_FILE_BYTES = 2 * 1024 * 1024 * 1024
MEDIA_GROUP_CHUNK_SIZE = 10
REQUEST_TIMEOUT_SEC = 2 * 60 * 60
STATUS_UPDATE_INTERVAL_SEC = 2
NETWORK_RETRY_ATTEMPTS = 3
NETWORK_RETRY_BACKOFF_SEC = 3
YANDEX_ALBUM_RETRY_ATTEMPTS = 5
YANDEX_ALBUM_RETRY_BACKOFF_SEC = 4
LOGS_DIR = Path("logs")
LOG_ROTATING_FILE = "downloader.log"
LOG_ROTATING_MAX_BYTES = 50 * 1024 * 1024
LOG_ROTATING_BACKUP_COUNT = 20

PHOTO_EXTS = {".jpg", ".jpeg", ".png"}
WINDOWS_INVALID_FILENAME_RE = re.compile(r'[<>:"/\\|?*\x00-\x1f]')
YANDEX_TRACK_WITH_ALBUM_RE = re.compile(r"/album/(?P<album>\d+)/track/(?P<track>\d+)")
YANDEX_TRACK_ONLY_RE = re.compile(r"/track/(?P<track>\d+)")
YANDEX_ALBUM_ONLY_RE = re.compile(r"^/album/(?P<album>\d+)/?$")
FORCED_MEDIA_MODE_RE = re.compile(r"@(?P<mode>vid)", re.IGNORECASE)

MEDIA_MODE_AUTO = "auto"
MEDIA_MODE_VIDEO_ONLY = "video_only"
MEDIA_MODE_IMAGE_ONLY = "image_only"
INLINE_MODE_PREFIXES = ("@vid",)


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


def looks_like_image(path: Path) -> bool:
    try:
        with path.open("rb") as file_obj:
            signature = file_obj.read(12)
    except Exception:
        return False

    if signature.startswith(b"\xff\xd8"):
        return True
    if signature.startswith(b"\x89PNG\r\n\x1a\n"):
        return True
    if signature[:4] == b"RIFF" and signature[8:12] == b"WEBP":
        return True
    if signature.startswith(b"GIF87a") or signature.startswith(b"GIF89a"):
        return True
    return False


def ensure_photo_file(path: Path) -> Path:
    if path.suffix.lower() in PHOTO_EXTS and looks_like_image(path):
        return path

    out_path = path.with_name(f"{path.stem}__photo.jpg")
    with Image.open(path) as image_obj:
        if image_obj.mode in ("RGBA", "LA"):
            background = Image.new("RGB", image_obj.size, (255, 255, 255))
            background.paste(image_obj, mask=image_obj.split()[-1])
            image_obj = background
        else:
            image_obj = image_obj.convert("RGB")
        image_obj.save(out_path, "JPEG", quality=92, optimize=True)
    return out_path


def log_sender(message: types.Message, url: str | None = None) -> None:
    user = message.from_user
    chat = message.chat
    raw_text = (message.text or message.caption or "").strip()
    raw_text = re.sub(r"\s+", " ", raw_text)
    if len(raw_text) > 250:
        raw_text = raw_text[:247].rstrip() + "..."
    logging.info(
        "INCOMING from_user id=%s username=@%s name=%s chat_id=%s chat_type=%s url=%s text=%s",
        user.id if user else None,
        (user.username or "") if user else None,
        f"{user.first_name or ''} {user.last_name or ''}".strip() if user else None,
        chat.id if chat else None,
        chat.type if chat else None,
        url,
        raw_text,
    )


def configure_logging() -> tuple[Path, Path]:
    LOGS_DIR.mkdir(parents=True, exist_ok=True)

    rotating_path = LOGS_DIR / LOG_ROTATING_FILE
    session_stamp = time.strftime("%Y%m%d_%H%M%S")
    session_path = LOGS_DIR / f"downloader_{session_stamp}.log"

    formatter = logging.Formatter("%(asctime)s | %(levelname)s | %(message)s")
    root = logging.getLogger()
    root.setLevel(logging.DEBUG)

    for handler in list(root.handlers):
        root.removeHandler(handler)
        with suppress(Exception):
            handler.close()

    console_handler = logging.StreamHandler()
    console_handler.setLevel(logging.INFO)
    console_handler.setFormatter(formatter)

    rotating_handler = RotatingFileHandler(
        rotating_path,
        maxBytes=LOG_ROTATING_MAX_BYTES,
        backupCount=LOG_ROTATING_BACKUP_COUNT,
        encoding="utf-8",
    )
    rotating_handler.setLevel(logging.DEBUG)
    rotating_handler.setFormatter(formatter)

    session_handler = logging.FileHandler(session_path, encoding="utf-8")
    session_handler.setLevel(logging.DEBUG)
    session_handler.setFormatter(formatter)

    root.addHandler(console_handler)
    root.addHandler(rotating_handler)
    root.addHandler(session_handler)

    logging.getLogger("asyncio").setLevel(logging.INFO)
    return rotating_path, session_path


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
            lowered = part.lower()
            for prefix in INLINE_MODE_PREFIXES:
                if not lowered.startswith(prefix):
                    continue
                suffix = part[len(prefix) :]
                normalized = _normalize_candidate_url(suffix)
                if normalized:
                    return normalized

    return None


def extract_media_mode_from_message(message: types.Message) -> str:
    content_sources = (message.text or "", message.caption or "")
    for text in content_sources:
        if not text:
            continue
        for match in FORCED_MEDIA_MODE_RE.finditer(text):
            mode_token = (match.group("mode") or "").lower()
            if mode_token == "vid":
                return MEDIA_MODE_VIDEO_ONLY
    return MEDIA_MODE_AUTO


def detect_source(url: str) -> str | None:
    parsed = urlparse(url)
    host = (parsed.netloc or "").lower()
    host = host[4:] if host.startswith("www.") else host

    for name, domains in SUPPORTED_DOMAINS.items():
        if any(domain in host for domain in domains):
            return name
    return None


def _join_artist_names(items: Any) -> str | None:
    if not isinstance(items, list):
        return None
    names: List[str] = []
    for item in items:
        if not isinstance(item, dict):
            continue
        name = (item.get("name") or "").strip()
        if name:
            names.append(name)
    if not names:
        return None
    return ", ".join(names)


def _resolve_yandex_track_ref(
    session: requests.Session,
    host: str,
    url: str,
) -> tuple[str, str, str]:
    path = urlparse(url).path or ""

    match = YANDEX_TRACK_WITH_ALBUM_RE.search(path)
    if match:
        album_id = match.group("album")
        track_id = match.group("track")
        ref_url = f"https://{host}/album/{album_id}/track/{track_id}"
        return ref_url, track_id, album_id

    match = YANDEX_TRACK_ONLY_RE.search(path)
    if not match:
        raise RuntimeError("Yandex tag enrichment supports track links only.")
    track_id = match.group("track")

    page_url = f"https://{host}/track/{track_id}"
    resp = session.get(page_url, timeout=20, allow_redirects=True)
    page = resp.text or ""
    low_page = page.lower()
    low_url = (resp.url or "").lower()
    if "showcaptcha" in low_page or "showcaptcha" in low_url:
        raise RuntimeError("Yandex returned captcha page.")

    match = re.search(rf"album/(\d+)/track/{track_id}", page)
    if not match:
        redirected_path = urlparse(resp.url).path or ""
        match = YANDEX_TRACK_WITH_ALBUM_RE.search(redirected_path)
        if not match:
            raise RuntimeError("Unable to resolve album id for track.")
    album_id = match.group("album") if "album" in match.groupdict() else match.group(1)
    ref_url = f"https://{host}/album/{album_id}/track/{track_id}"
    return ref_url, track_id, album_id


def _is_yandex_track_url(url: str) -> bool:
    path = urlparse(url).path or ""
    return bool(
        YANDEX_TRACK_WITH_ALBUM_RE.search(path) or YANDEX_TRACK_ONLY_RE.search(path)
    )


def _is_yandex_album_url(url: str) -> bool:
    path = urlparse(url).path or ""
    return bool(YANDEX_ALBUM_ONLY_RE.fullmatch(path))


def _extract_skipped_tracks_from_preview_warning(text: str | None) -> int | None:
    body = (text or "").strip()
    if not body:
        return 0

    match = re.search(r"Skipped\s+(\d+)\s+track\(s\)", body, flags=re.IGNORECASE)
    if match:
        try:
            return int(match.group(1))
        except Exception:
            return None

    if "Only a preview was downloaded" in body:
        return 1
    return None


def _download_yandex_music_with_album_retries(
    url: str,
    progress_callback: Callable[[str], None] | None = None,
) -> Tuple[List[Path], Path, str | None, Path | None, str | None]:
    if not _is_yandex_album_url(url):
        return yamu.download_yandex_music(url, progress_callback)

    best_result: tuple[List[Path], Path, str | None, Path | None, str | None] | None = (
        None
    )
    best_skipped: int | None = None
    best_files_count = -1
    last_exc: Exception | None = None

    for attempt in range(1, YANDEX_ALBUM_RETRY_ATTEMPTS + 1):
        if progress_callback:
            progress_callback(
                f"[album] attempt {attempt}/{YANDEX_ALBUM_RETRY_ATTEMPTS}: downloading and recovering tracks..."
            )

        try:
            result = yamu.download_yandex_music(url, progress_callback)
        except Exception as exc:
            last_exc = exc
            logging.warning(
                "Album download attempt %s/%s failed: %s",
                attempt,
                YANDEX_ALBUM_RETRY_ATTEMPTS,
                exc,
            )
            if attempt < YANDEX_ALBUM_RETRY_ATTEMPTS:
                delay = YANDEX_ALBUM_RETRY_BACKOFF_SEC * attempt
                if progress_callback:
                    progress_callback(
                        f"[album] attempt failed, retrying in {delay}s..."
                    )
                time.sleep(delay)
            continue

        files, tmp_dir, caption_text, cover_path, preview_warning = result
        skipped = _extract_skipped_tracks_from_preview_warning(preview_warning)
        skipped_label = "unknown" if skipped is None else str(skipped)
        logging.info(
            "Album attempt %s/%s result: files=%s skipped=%s",
            attempt,
            YANDEX_ALBUM_RETRY_ATTEMPTS,
            len(files),
            skipped_label,
        )

        if skipped == 0:
            if best_result:
                _, old_tmp_dir, _, _, _ = best_result
                if old_tmp_dir != tmp_dir:
                    cleanup_tmp_dir(old_tmp_dir)
            return result

        is_better = False
        if best_result is None:
            is_better = True
        elif skipped is not None and best_skipped is None:
            is_better = True
        elif (
            skipped is not None and best_skipped is not None and skipped < best_skipped
        ):
            is_better = True
        elif skipped == best_skipped and len(files) > best_files_count:
            is_better = True

        if is_better:
            if best_result:
                _, old_tmp_dir, _, _, _ = best_result
                if old_tmp_dir != tmp_dir:
                    cleanup_tmp_dir(old_tmp_dir)
            best_result = result
            best_skipped = skipped
            best_files_count = len(files)
        else:
            cleanup_tmp_dir(tmp_dir)

        if attempt < YANDEX_ALBUM_RETRY_ATTEMPTS:
            delay = YANDEX_ALBUM_RETRY_BACKOFF_SEC * attempt
            if progress_callback:
                progress_callback(
                    f"[album] best so far: {best_files_count} track(s), "
                    f"retrying in {delay}s for missing tracks..."
                )
            time.sleep(delay)

    if best_result:
        files, tmp_dir, caption_text, cover_path, preview_warning = best_result
        retry_note = (
            f"Downloader retries used: {YANDEX_ALBUM_RETRY_ATTEMPTS} attempt(s). "
            f"Best result: {len(files)} track(s)."
        )
        if preview_warning:
            preview_warning = f"{preview_warning}\n\n{retry_note}"
        else:
            preview_warning = retry_note
        return files, tmp_dir, caption_text, cover_path, preview_warning

    if last_exc:
        raise last_exc
    raise RuntimeError("Album download failed after retry attempts.")


def _normalize_yandex_cover_url(raw: str | None) -> str | None:
    value = (raw or "").strip()
    if not value:
        return None
    value = value.replace("%%", "orig")
    if value.startswith("//"):
        value = "https:" + value
    elif not value.startswith("http"):
        value = "https://" + value
    return value


def _extract_yandex_lyrics(payload: dict[str, Any]) -> str | None:
    lyric_obj = payload.get("lyric")
    if not isinstance(lyric_obj, dict):
        return None

    for key in ("fullLyrics", "lyrics", "text", "value"):
        value = lyric_obj.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()

    for key in ("lyrics", "lines", "chunks"):
        value = lyric_obj.get(key)
        if isinstance(value, list):
            parts = [str(item).strip() for item in value if str(item).strip()]
            if parts:
                return "\n".join(parts)

    return None


def _download_cover_bytes(url: str, timeout_sec: int = 20) -> tuple[bytes, str] | None:
    try:
        resp = requests.get(
            url,
            timeout=timeout_sec,
            stream=True,
            headers={"User-Agent": "Mozilla/5.0"},
        )
        resp.raise_for_status()
    except Exception:
        return None

    content_type = (resp.headers.get("Content-Type") or "").lower()
    mime = "image/jpeg"
    if "png" in content_type:
        mime = "image/png"
    elif "webp" in content_type:
        mime = "image/webp"

    try:
        data = resp.content
    finally:
        resp.close()

    if not data:
        return None
    return data, mime


def _load_cover_from_path(path: Path | None) -> tuple[bytes, str] | None:
    if not path or not path.exists():
        return None
    suffix = path.suffix.lower()
    mime = "image/jpeg"
    if suffix == ".png":
        mime = "image/png"
    elif suffix == ".webp":
        mime = "image/webp"
    try:
        data = path.read_bytes()
    except Exception:
        return None
    if not data:
        return None
    return data, mime


def _build_yandex_track_tags(
    track: dict[str, Any],
    payload: dict[str, Any],
    source_url: str,
) -> dict[str, str]:
    album = None
    albums = track.get("albums")
    if isinstance(albums, list):
        for item in albums:
            if isinstance(item, dict):
                album = item
                break

    artist = _join_artist_names(track.get("artists")) or ""
    album_artist = (
        _join_artist_names(album.get("artists")) if isinstance(album, dict) else ""
    )
    title = (track.get("title") or "").strip()
    album_title = (album.get("title") or "").strip() if isinstance(album, dict) else ""
    genre = (album.get("genre") or "").strip() if isinstance(album, dict) else ""
    year = album.get("year") if isinstance(album, dict) else None

    track_no = ""
    disc_no = ""
    if isinstance(album, dict):
        pos = album.get("trackPosition")
        if isinstance(pos, dict):
            idx = pos.get("index")
            vol = pos.get("volume")
            if isinstance(idx, (int, float)) and idx > 0:
                track_no = str(int(idx))
            if isinstance(vol, (int, float)) and vol > 0:
                disc_no = str(int(vol))

    tags: dict[str, str] = {
        "title": title,
        "artist": artist,
        "album": album_title,
        "albumartist": album_artist or artist,
        "genre": genre,
        "tracknumber": track_no,
        "discnumber": disc_no,
        "comment": f"Source: {source_url}",
        "url": source_url,
    }
    if isinstance(year, (int, float)) and year > 0:
        tags["date"] = str(int(year))

    cover_url = _normalize_yandex_cover_url(track.get("coverUri"))
    if cover_url:
        tags["cover_url"] = cover_url

    lyrics = _extract_yandex_lyrics(payload)
    if lyrics:
        tags["lyrics"] = lyrics

    return tags


def _fetch_yandex_track_tags(source_url: str) -> dict[str, str] | None:
    parsed = urlparse(source_url)
    host = (parsed.netloc or "").lower()
    host = host[4:] if host.startswith("www.") else host
    if not any(domain in host for domain in SUPPORTED_DOMAINS["yandex_music"]):
        return None

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

    cookies_file = yamu.cookies_path_for_yandex_music()
    if cookies_file and Path(cookies_file).is_file():
        jar = MozillaCookieJar(cookies_file)
        jar.load(ignore_discard=True, ignore_expires=True)
        session.cookies.update(jar)

    last_exc: Exception | None = None
    for attempt in range(1, 4):
        try:
            ref_url, track_id, album_id = _resolve_yandex_track_ref(
                session, host, source_url
            )
            headers = {
                "Referer": ref_url,
                "X-Requested-With": "XMLHttpRequest",
                "X-Retpath-Y": ref_url,
            }
            resp = session.get(
                f"https://{host}/handlers/track.jsx",
                params={"track": f"{track_id}:{album_id}"},
                headers=headers,
                timeout=20,
            )
            resp.raise_for_status()
            payload = resp.json()
            if isinstance(payload, dict) and (
                payload.get("type") == "captcha" or "captcha" in payload
            ):
                raise RuntimeError("Yandex requested captcha while reading metadata.")

            track = payload.get("track") if isinstance(payload, dict) else None
            if not isinstance(track, dict):
                return None
            return _build_yandex_track_tags(track, payload, source_url)
        except Exception as exc:
            last_exc = exc
            if attempt >= 3:
                break
            time.sleep(0.8 * attempt)
    if last_exc:
        raise last_exc
    return None


def _write_mp3_id3_tags(
    path: Path,
    tags_map: dict[str, str],
    cover_blob: tuple[bytes, str] | None = None,
) -> None:
    from mutagen.id3 import (
        APIC,
        COMM,
        TALB,
        TCON,
        TDRC,
        TIT2,
        TPE1,
        TPE2,
        TPOS,
        TRCK,
        USLT,
        WXXX,
        ID3,
        ID3NoHeaderError,
    )

    try:
        tags = ID3(str(path))
    except ID3NoHeaderError:
        tags = ID3()

    for key in list(tags.keys()):
        if key.startswith("APIC"):
            del tags[key]

    if cover_blob:
        cover_data, cover_mime = cover_blob
        tags.add(
            APIC(
                encoding=3,
                mime=cover_mime,
                type=3,
                desc="Cover",
                data=cover_data,
            )
        )

    def _set_text(frame_id: str, frame_cls: Any, value: str | None) -> None:
        tags.delall(frame_id)
        cleaned = (value or "").strip()
        if cleaned:
            tags.add(frame_cls(encoding=3, text=[cleaned]))

    _set_text("TIT2", TIT2, tags_map.get("title"))
    _set_text("TPE1", TPE1, tags_map.get("artist"))
    _set_text("TALB", TALB, tags_map.get("album"))
    _set_text("TPE2", TPE2, tags_map.get("albumartist"))
    _set_text("TCON", TCON, tags_map.get("genre"))
    _set_text("TDRC", TDRC, tags_map.get("date"))
    _set_text("TRCK", TRCK, tags_map.get("tracknumber"))
    _set_text("TPOS", TPOS, tags_map.get("discnumber"))

    tags.delall("COMM")
    comment = (tags_map.get("comment") or "").strip()
    if comment:
        tags.add(COMM(encoding=3, lang="eng", desc="", text=[comment]))

    tags.delall("WXXX")
    source_url = (tags_map.get("url") or "").strip()
    if source_url:
        tags.add(WXXX(encoding=3, desc="Source", url=source_url))

    tags.delall("USLT")
    lyrics_text = (tags_map.get("lyrics") or "").strip()
    if lyrics_text:
        tags.add(USLT(encoding=3, lang="eng", desc="", text=lyrics_text))

    tags.save(str(path), v2_version=3)


def _apply_yandex_audio_tags(
    source_url: str,
    files: Sequence[Path],
    cover_path: Path | None = None,
) -> int:
    mp3_files = [
        path for path in files if path.exists() and path.suffix.lower() == ".mp3"
    ]
    if not mp3_files:
        return 0

    tags_map: dict[str, str] | None = None
    if _is_yandex_track_url(source_url):
        try:
            tags_map = _fetch_yandex_track_tags(source_url)
        except Exception as exc:
            logging.warning(
                "Failed to fetch Yandex tags, fallback to minimal ID3 tags: %s", exc
            )
    elif _is_yandex_album_url(source_url):
        logging.info("Yandex album link detected: applying fallback ID3 tags per file.")

    cover_blob = _load_cover_from_path(cover_path)
    if not cover_blob and tags_map:
        cover_url = (tags_map.get("cover_url") or "").strip()
        if cover_url:
            cover_blob = _download_cover_bytes(cover_url)

    updated = 0
    for path in mp3_files:
        try:
            if tags_map:
                _write_mp3_id3_tags(path, tags_map, cover_blob=cover_blob)
                updated += 1
            else:
                fallback_title = re.sub(r"-\d{4,}$", "", path.stem).strip()
                fallback_tags = {
                    "title": fallback_title,
                    "comment": f"Source: {source_url}",
                    "url": source_url,
                }
                _write_mp3_id3_tags(path, fallback_tags, cover_blob=cover_blob)
                updated += 1
        except Exception:
            logging.exception("Failed to apply ID3 tags for %s", path)
    return updated


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


def is_youtube_gallery_url(url: str) -> bool:
    parsed = urlparse(url)
    host = (parsed.netloc or "").lower()
    host = host[4:] if host.startswith("www.") else host

    if "youtube.com" not in host:
        return False

    path = (parsed.path or "").lower()
    query = parse_qs(parsed.query or "")

    if path.startswith("/post/"):
        return True
    if "/community" in path and "lb" in query:
        return True

    return False


def _extract_json_object_after_marker(text: str, marker: str) -> dict | None:
    marker_pos = text.find(marker)
    if marker_pos == -1:
        return None

    start = text.find("{", marker_pos)
    if start == -1:
        return None

    depth = 0
    in_string = False
    escaped = False

    for index in range(start, len(text)):
        char = text[index]

        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            continue

        if char == '"':
            in_string = True
            continue

        if char == "{":
            depth += 1
            continue

        if char == "}":
            depth -= 1
            if depth == 0:
                raw = text[start : index + 1]
                try:
                    return json.loads(raw)
                except Exception:
                    return None

    return None


def _pick_largest_thumbnail_url(thumbnails: Sequence[dict]) -> str | None:
    best_url = None
    best_area = -1

    for thumb in thumbnails:
        if not isinstance(thumb, dict):
            continue

        url = thumb.get("url")
        if not url:
            continue

        width = int(thumb.get("width") or 0)
        height = int(thumb.get("height") or 0)
        area = width * height
        if area >= best_area:
            best_area = area
            best_url = url

    return best_url


def _extract_youtube_post_image_urls(data: object) -> List[str]:
    urls: List[str] = []
    seen: set[str] = set()
    stack: List[object] = [data]

    while stack:
        node = stack.pop()

        if isinstance(node, dict):
            image_renderer = node.get("backstageImageRenderer")
            if isinstance(image_renderer, dict):
                image = image_renderer.get("image") or {}
                thumbnails = (
                    image.get("thumbnails") if isinstance(image, dict) else None
                )
                if isinstance(thumbnails, list):
                    largest = _pick_largest_thumbnail_url(thumbnails)
                    if largest and largest not in seen:
                        seen.add(largest)
                        urls.append(largest)

            for value in node.values():
                if isinstance(value, (dict, list)):
                    stack.append(value)

        elif isinstance(node, list):
            for value in node:
                if isinstance(value, (dict, list)):
                    stack.append(value)

    return urls


def _extract_youtube_post_text(data: object) -> str | None:
    stack: List[object] = [data]
    while stack:
        node = stack.pop()

        if isinstance(node, dict):
            if "backstagePostRenderer" in node:
                post = node["backstagePostRenderer"]
                content = post.get("contentText") or {}
                runs = content.get("runs") or []
                parts = []
                for item in runs:
                    text = item.get("text")
                    if text:
                        parts.append(text)
                extracted = "".join(parts).strip()
                if extracted:
                    return extracted

            for value in node.values():
                if isinstance(value, (dict, list)):
                    stack.append(value)

        elif isinstance(node, list):
            for value in node:
                if isinstance(value, (dict, list)):
                    stack.append(value)

    return None


def _extension_from_content_type(content_type: str) -> str:
    low = (content_type or "").lower()
    if "png" in low:
        return ".png"
    if "webp" in low:
        return ".webp"
    if "gif" in low:
        return ".gif"
    return ".jpg"


def _download_http_bytes(
    url: str, referer: str | None = None, retries: int = 3
) -> tuple[bytes, str]:
    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/121.0 Safari/537.36"
        ),
        "Accept-Language": "ru-RU,ru;q=0.9,en;q=0.8",
    }
    if referer:
        headers["Referer"] = referer

    last_error: Exception | None = None

    for attempt in range(retries):
        try:
            req = request.Request(url, headers=headers)
            with request.urlopen(req, timeout=30) as response:
                content_type = response.headers.get("Content-Type", "")
                payload = response.read()
            return payload, content_type
        except Exception as exc:
            last_error = exc
            if attempt < retries - 1:
                time.sleep(0.8 * (attempt + 1))

    if last_error:
        raise last_error
    raise RuntimeError("HTTP download failed")


def download_youtube_post_images(url: str, tmp_dir: Path) -> List[Path]:
    payload, _ = _download_http_bytes(url)
    page_html = payload.decode("utf-8", errors="ignore")

    data = _extract_json_object_after_marker(page_html, "var ytInitialData =")
    if not data:
        return []

    image_urls = _extract_youtube_post_image_urls(data)
    files: List[Path] = []

    for index, image_url in enumerate(image_urls, start=1):
        image_payload, content_type = _download_http_bytes(image_url, referer=url)
        ext = _extension_from_content_type(content_type)
        path = tmp_dir / f"youtube_post_{index:02d}{ext}"
        path.write_bytes(image_payload)
        files.append(path)

    return files


def download_youtube_post_caption(url: str) -> str | None:
    try:
        payload, _ = _download_http_bytes(url)
        page_html = payload.decode("utf-8", errors="ignore")
        data = _extract_json_object_after_marker(page_html, "var ytInitialData =")
        return _extract_youtube_post_text(data) if data else None
    except Exception:
        logging.exception("Failed to extract youtube post caption")
        return None


def cookies_path_for_instagram() -> str | None:
    path_from_env = os.getenv("COOKIES_INSTAGRAM")
    if path_from_env and Path(path_from_env).is_file():
        return path_from_env

    local = Path("cookies_instagram.txt")
    if local.is_file():
        return str(local)

    return None


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


def _strip_video_id_suffix(stem: str) -> str:
    cleaned = re.sub(r"-[A-Za-z0-9_-]{11}$", "", stem)
    return cleaned.strip(" _-")


def _sanitize_filename_stem(stem: str, fallback: str) -> str:
    cleaned = WINDOWS_INVALID_FILENAME_RE.sub("", stem)
    cleaned = re.sub(r"\s+", " ", cleaned).strip().rstrip(".")
    if not cleaned:
        return fallback
    return cleaned[:120]


def _make_unique_path(directory: Path, stem: str, suffix: str) -> Path:
    candidate = directory / f"{stem}{suffix}"
    counter = 2
    while candidate.exists():
        candidate = directory / f"{stem}_{counter:02d}{suffix}"
        counter += 1
    return candidate


def _build_audio_title(video_path: Path, title_hint: str | None, index: int) -> str:
    from_filename = _strip_video_id_suffix(video_path.stem)
    if from_filename:
        return from_filename[:80]

    from_hint = _single_line_text(title_hint)
    if from_hint:
        return from_hint[:80]

    return f"audio_from_video_{index:02d}"


def extract_audio_tracks_from_videos(
    files: Sequence[Path],
    tmp_dir: Path,
    source: str,
    title_hint: str | None = None,
    progress_callback: Callable[[str], None] | None = None,
) -> List[Path]:
    if source not in {"youtube", "instagram", "tiktok"}:
        return []

    video_files = [path for path in files if path.exists() and is_video(path)]
    if not video_files:
        return []

    ffmpeg_bin = shutil.which("ffmpeg")
    if not ffmpeg_bin:
        logging.warning("ffmpeg is not available. Skip audio extraction for videos.")
        return []

    extracted: List[Path] = []
    for index, video_path in enumerate(video_files, start=1):
        if progress_callback:
            progress_callback(
                f"[postprocess] extracting audio {index}/{len(video_files)}"
            )

        audio_title = _build_audio_title(video_path, title_hint, index)
        safe_stem = _sanitize_filename_stem(
            audio_title, f"audio_from_video_{index:02d}"
        )
        output_mp3 = _make_unique_path(tmp_dir, safe_stem, ".mp3")
        output_m4a = _make_unique_path(tmp_dir, safe_stem, ".m4a")

        extraction_attempts = [
            (
                output_mp3,
                [
                    ffmpeg_bin,
                    "-y",
                    "-i",
                    str(video_path),
                    "-vn",
                    "-map",
                    "a:0",
                    "-c:a",
                    "libmp3lame",
                    "-q:a",
                    "2",
                    "-metadata",
                    f"title={audio_title}",
                    str(output_mp3),
                ],
            ),
            (
                output_m4a,
                [
                    ffmpeg_bin,
                    "-y",
                    "-i",
                    str(video_path),
                    "-vn",
                    "-map",
                    "a:0",
                    "-c:a",
                    "aac",
                    "-b:a",
                    "192k",
                    "-metadata",
                    f"title={audio_title}",
                    str(output_m4a),
                ],
            ),
        ]

        extracted_path: Path | None = None
        last_rc: int | None = None

        for output_path, cmd in extraction_attempts:
            try:
                proc = subprocess.run(
                    cmd,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    shell=False,
                    check=False,
                )
            except Exception:
                logging.exception("ffmpeg audio extraction failed for %s", video_path)
                continue

            last_rc = proc.returncode
            if (
                proc.returncode == 0
                and output_path.exists()
                and output_path.stat().st_size > 0
            ):
                extracted_path = output_path
                break
            with suppress(Exception):
                if output_path.exists():
                    output_path.unlink()

        if not extracted_path:
            logging.warning(
                "Failed to extract audio from %s (ffmpeg rc=%s).",
                video_path,
                last_rc,
            )
            continue

        extracted.append(extracted_path)

    return extracted


def _gallery_dl_download(url: str, tmp_dir: Path, cookies_file: str | None) -> None:
    cmd = [sys.executable, "-m", "gallery_dl", "-D", str(tmp_dir)]
    if cookies_file:
        cmd += ["--cookies", cookies_file]
    cmd.append(url)

    try:
        proc = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
            shell=False,
            check=False,
        )
    except FileNotFoundError as exc:
        raise RuntimeError(
            "gallery-dl is not installed. Install it with: pip install gallery-dl"
        ) from exc

    output = (proc.stdout or "").strip()
    if proc.returncode != 0:
        low = output.lower()
        if "redirect to login page" in low or "accounts/login" in low:
            raise RuntimeError(
                "Instagram requires authorization. Provide COOKIES_INSTAGRAM "
                "in Netscape cookies.txt format from a logged-in browser."
            )
        raise RuntimeError(output or "gallery-dl failed")


def pick_caption_from_info(info: dict | None) -> str | None:
    if not info:
        return None

    for key in ("description", "title"):
        value = (info.get(key) or "").strip()
        if value:
            return value

    for entry in info.get("entries") or []:
        for key in ("description", "title"):
            value = (entry.get(key) or "").strip()
            if value:
                return value

    return None


def download_media_auto(
    url: str,
    source: str,
    progress_callback: Callable[[str], None] | None = None,
) -> Tuple[List[Path], Path, str | None]:
    tmp_dir = Path(tempfile.mkdtemp(prefix="tgloader_"))
    instagram_cookies = cookies_path_for_instagram()
    caption_text: str | None = None
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

    def attach_video_audio(
        files: List[Path], current_source: str, title_hint: str | None = None
    ) -> List[Path]:
        extra_audio = extract_audio_tracks_from_videos(
            files,
            tmp_dir,
            current_source,
            title_hint=title_hint,
            progress_callback=lambda line: emit_progress(line, force=True),
        )
        if not extra_audio:
            return files

        merged = list(files)
        known = {str(path.resolve()) for path in merged if path.exists()}
        for path in extra_audio:
            key = str(path.resolve())
            if key not in known:
                known.add(key)
                merged.append(path)
        return merged

    def try_gallery_dl() -> Tuple[List[Path], Path, str | None] | None:
        if source != "instagram":
            return None
        _gallery_dl_download(url, tmp_dir, instagram_cookies)
        files = _collect_paths_from_dir(tmp_dir)
        if not files:
            return None
        return attach_video_audio(files, "instagram", caption_text), tmp_dir, None

    if source == "youtube_gallery":
        gallery_files = download_youtube_post_images(url, tmp_dir)
        caption_text = download_youtube_post_caption(url)
        if gallery_files:
            return (
                attach_video_audio(gallery_files, "youtube_gallery", caption_text),
                tmp_dir,
                caption_text,
            )
        source = "youtube"

    if source == "youtube":
        fmt = "bv*+ba/best"
        noplaylist = True
        merge = "mp4"
    elif source == "tiktok":
        fmt = "bv*+ba/best"
        noplaylist = True
        merge = "mp4"
    elif source == "instagram":
        fmt = "best"
        noplaylist = False
        merge = None
    else:
        raise RuntimeError("Unsupported source")

    ydl_opts = {
        "outtmpl": str(tmp_dir / "%(title).200B-%(id)s.%(ext)s"),
        "noplaylist": noplaylist,
        "quiet": True,
        "no_color": True,
        "retries": 5,
        "fragment_retries": 5,
        "windowsfilenames": True,
        "user_agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/121.0 Safari/537.36"
        ),
        "format": fmt,
        "js_runtimes": {"node": {}},
        "remote_components": ["ejs:github"],
    }

    if merge:
        ydl_opts["merge_output_format"] = merge

    def ydl_progress_hook(data: dict[str, Any]) -> None:
        line = _build_yt_dlp_progress_line(data)
        if not line:
            return
        emit_progress(line, force=(data.get("status") == "finished"))

    ydl_opts["progress_hooks"] = [ydl_progress_hook]

    if source == "instagram":
        ydl_opts["http_headers"] = {
            "Accept-Language": "ru-RU,ru;q=0.9,en;q=0.8",
            "Referer": "https://www.instagram.com/",
            "Origin": "https://www.instagram.com",
        }
        if instagram_cookies:
            ydl_opts["cookies"] = instagram_cookies
        else:
            result = try_gallery_dl()
            if result:
                return result

    try:
        with YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=True)

        files = _collect_paths_from_ytdlp_info(info)
        if not files:
            files = _collect_paths_from_dir(tmp_dir)

        if source == "instagram" and not files:
            result = try_gallery_dl()
            if result:
                return result

        if files:
            caption_text = pick_caption_from_info(info) or caption_text
            return (
                attach_video_audio(files, source, caption_text),
                tmp_dir,
                caption_text,
            )

    except Exception as exc:
        if source == "instagram":
            low = str(exc).lower()
            expected_markers = (
                "there is no video in this post",
                "no csrf token set",
                "unavailable for certain audiences",
                "may be inappropriate",
                "login",
                "checkpoint",
                "restricted",
                "rate limit",
            )
            if any(marker in low for marker in expected_markers):
                result = try_gallery_dl()
                if result:
                    return result

                if (
                    "unavailable for certain audiences" in low
                    or "may be inappropriate" in low
                ):
                    raise RuntimeError(
                        "Instagram restricted this content. Check fresh cookies, "
                        "18+ settings and sensitive content visibility."
                    ) from exc

            result = try_gallery_dl()
            if result:
                return result

        raise

    raise RuntimeError("Download failed: empty result.")


def cleanup_tmp_dir(tmp_dir: Path | None) -> None:
    if not tmp_dir:
        return
    try:
        shutil.rmtree(tmp_dir, ignore_errors=True)
    except Exception:
        pass


def is_image(path: Path) -> bool:
    return path.suffix.lower() in {".jpg", ".jpeg", ".png", ".webp", ".gif"}


def is_video(path: Path) -> bool:
    return path.suffix.lower() in {".mp4", ".mov", ".mkv", ".webm", ".m4v"}


def is_audio(path: Path) -> bool:
    return path.suffix.lower() in {
        ".mp3",
        ".m4a",
        ".aac",
        ".ogg",
        ".opus",
        ".flac",
        ".wav",
    }


def filter_files_by_media_mode(files: Sequence[Path], media_mode: str) -> List[Path]:
    if media_mode == MEDIA_MODE_VIDEO_ONLY:
        return [path for path in files if is_video(path)]
    if media_mode == MEDIA_MODE_IMAGE_ONLY:
        return [path for path in files if is_image(path)]
    return list(files)


def _chunks(items: List[Path], size: int = MEDIA_GROUP_CHUNK_SIZE) -> List[List[Path]]:
    return [items[index : index + size] for index in range(0, len(items), size)]


def make_source_caption(source: str, url: str, extra_text: str = "") -> str:
    source_name = SOURCE_LABELS.get(source, source.replace("_", " ").title())
    safe_url = html.escape(url, quote=True)
    caption = f'Источник: <a href="{safe_url}">{source_name}</a>'
    if extra_text:
        caption += f" {extra_text}"
    return caption


def clean_caption(text: str) -> str:
    text = re.sub(r"[ \t]+", " ", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()


def build_telegram_audio_title(
    path: Path, caption_text: str | None = None
) -> str | None:
    stem = _strip_video_id_suffix(path.stem.replace("_", " "))
    stem = re.sub(r"\s+", " ", stem).strip()

    if not stem or stem.lower().startswith("audio from video"):
        stem = _single_line_text(caption_text)

    if not stem:
        return None

    if len(stem) > 64:
        stem = stem[:61].rstrip() + "..."
    return stem


def build_media_caption(source: str, url: str, caption_text: str | None) -> str:
    base = make_source_caption(source, url)
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


def _caption_will_be_truncated(source: str, url: str, caption_text: str | None) -> bool:
    extra = clean_caption(caption_text or "")
    if not extra:
        return False
    base = make_source_caption(source, url)
    full = f"{base}\n{html.escape(extra)}"
    return len(full) > TELEGRAM_CAPTION_LIMIT


def _split_message_chunks(text: str, limit: int = TELEGRAM_TEXT_LIMIT) -> List[str]:
    content = (text or "").strip()
    if not content:
        return []
    if len(content) <= limit:
        return [content]

    chunks: List[str] = []
    rest = content
    while rest:
        if len(rest) <= limit:
            chunks.append(rest)
            break

        cut = rest.rfind("\n", 0, limit)
        if cut < int(limit * 0.6):
            cut = rest.rfind(" ", 0, limit)
        if cut < int(limit * 0.6):
            cut = limit

        chunk = rest[:cut].rstrip()
        if not chunk:
            chunk = rest[:limit]
            cut = limit
        chunks.append(chunk)
        rest = rest[cut:].lstrip()

    return chunks


async def _send_full_caption_if_needed(
    bot: Bot,
    chat_id: int,
    source: str,
    url: str,
    caption_text: str | None,
) -> None:
    if not _caption_will_be_truncated(source, url, caption_text):
        return

    full_text = clean_caption(caption_text or "")
    if not full_text:
        return

    chunks = _split_message_chunks(full_text, TELEGRAM_TEXT_LIMIT)
    for index, chunk in enumerate(chunks, start=1):
        prefix = "Полное описание:\n" if index == 1 else ""
        text_to_send = f"{prefix}{chunk}"
        await _send_with_retry(
            f"send_full_caption_part_{index}",
            lambda t=text_to_send: bot.send_message(
                chat_id,
                t,
                parse_mode=None,
                request_timeout=REQUEST_TIMEOUT_SEC,
            ),
        )


def _format_elapsed(total_seconds: float) -> str:
    seconds = max(0, int(total_seconds))
    minutes, sec = divmod(seconds, 60)
    hours, minutes = divmod(minutes, 60)
    if hours:
        return f"{hours:02d}:{minutes:02d}:{sec:02d}"
    return f"{minutes:02d}:{sec:02d}"


def _trim_error_text(text: str, max_len: int = 350) -> str:
    text = (text or "").strip()
    if len(text) <= max_len:
        return text
    return text[: max_len - 3].rstrip() + "..."


async def _safe_edit_status(message: types.Message, text: str) -> bool:
    try:
        await message.edit_text(text)
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


class StatusProgress:
    def __init__(self, status_message: types.Message, initial_phase: str) -> None:
        self._status_message = status_message
        self._phase = initial_phase
        self._detail = ""
        self._started = time.monotonic()
        self._last_render = ""
        self._closed = False
        self._task: asyncio.Task | None = None

    async def start(self) -> None:
        await self._render(force=True)
        self._task = asyncio.create_task(self._ticker())

    async def _ticker(self) -> None:
        try:
            while not self._closed:
                await asyncio.sleep(STATUS_UPDATE_INTERVAL_SEC)
                await self._render()
        except asyncio.CancelledError:
            return

    async def set_phase(self, phase: str) -> None:
        if self._closed:
            return
        if phase != self._phase:
            self._phase = phase
            await self._render(force=True)

    def set_detail_text(self, detail: str) -> None:
        if self._closed:
            return
        self._detail = (detail or "").strip()

    async def finish(self, final_text: str) -> bool:
        return await self.close(final_text=final_text)

    async def dismiss(self) -> bool:
        return await self.close(delete_message=True)

    async def close(
        self, final_text: str | None = None, delete_message: bool = False
    ) -> bool:
        if self._closed:
            return False
        self._closed = True
        if self._task:
            self._task.cancel()
            with suppress(asyncio.CancelledError):
                await self._task
        if delete_message:
            return await _safe_delete_status(self._status_message)
        if final_text is None:
            return True
        return await _safe_edit_status(self._status_message, final_text)

    def _compose_text(self) -> str:
        elapsed = _format_elapsed(time.monotonic() - self._started)
        if self._detail:
            return f"{self._phase}\n{self._detail}\nПрошло: {elapsed}"
        return f"{self._phase}\nПрошло: {elapsed}"

    async def _render(self, force: bool = False) -> None:
        if self._closed:
            return
        text = self._compose_text()
        if not force and text == self._last_render:
            return
        ok = await _safe_edit_status(self._status_message, text)
        if ok:
            self._last_render = text
        else:
            self._closed = True
            if self._task:
                self._task.cancel()


async def send_media_to_chat(
    bot: Bot,
    chat_id: int,
    files: Sequence[Path],
    source: str,
    url: str,
    caption_text: str | None = None,
    progress: StatusProgress | None = None,
    media_mode: str = MEDIA_MODE_AUTO,
) -> None:
    existing = [path for path in files if path.exists()]
    existing = filter_files_by_media_mode(existing, media_mode)
    existing = sorted(existing, key=lambda p: p.name.lower())
    if not existing:
        if media_mode == MEDIA_MODE_VIDEO_ONLY:
            raise RuntimeError("По команде @vid в этом контенте не найдено видео.")
        if media_mode == MEDIA_MODE_IMAGE_ONLY:
            raise RuntimeError("В этом контенте не найдено фото.")
        raise RuntimeError("No files were produced by downloader.")

    oversized = [
        path for path in existing if path.stat().st_size > MAX_TELEGRAM_FILE_BYTES
    ]
    sendable = [path for path in existing if path not in oversized]

    if not sendable:
        too_big_summary = "\n".join(
            f"- {path.name} ({_human_size(path.stat().st_size)})"
            for path in oversized[:10]
        )
        raise RuntimeError(
            "All files are larger than 2 GiB and cannot be sent.\n" + too_big_summary
        )

    images = [path for path in sendable if is_image(path)]
    videos = [path for path in sendable if is_video(path)]
    audios = [path for path in sendable if is_audio(path)]
    others = [
        path
        for path in sendable
        if (path not in images and path not in videos and path not in audios)
    ]
    total_to_send = len(sendable)

    photo_images: List[Path] = []
    for path in images:
        try:
            if not looks_like_image(path):
                logging.warning("Skip non-image file for photo send: %s", path)
                continue
            photo_candidate = ensure_photo_file(path)
            if (
                photo_candidate.stat().st_size <= MAX_TELEGRAM_FILE_BYTES
                and looks_like_image(photo_candidate)
            ):
                photo_images.append(photo_candidate)
        except Exception:
            logging.exception("Failed to prepare image for photo send: %s", path)

    caption_full = build_media_caption(source, url, caption_text)
    caption_used = False

    photo_chunks = _chunks(photo_images, MEDIA_GROUP_CHUNK_SIZE)
    last_chunk_index = len(photo_chunks) - 1

    for chunk_index, chunk in enumerate(photo_chunks):
        if progress:
            await progress.set_phase(
                f"Отправка фото-группы {chunk_index + 1}/{len(photo_chunks)}"
            )
        caption_for_chunk = (
            caption_full
            if (chunk_index == last_chunk_index and not caption_used)
            else None
        )
        if caption_for_chunk:
            caption_used = True

        media: list[types.InputMediaPhoto] = []
        for item_index, path in enumerate(chunk):
            cap = caption_for_chunk if (caption_for_chunk and item_index == 0) else None
            media.append(
                types.InputMediaPhoto(
                    media=types.FSInputFile(path),
                    caption=cap,
                    parse_mode=ParseMode.HTML if cap else None,
                )
            )

        try:
            await _send_with_retry(
                f"send_media_group {chunk_index + 1}/{len(photo_chunks)}",
                lambda: bot.send_media_group(
                    chat_id,
                    media,
                    request_timeout=REQUEST_TIMEOUT_SEC,
                ),
            )
        except Exception:
            logging.exception("send_media_group(photo) failed; fallback to send_photo")
            for item_index, path in enumerate(chunk):
                cap = (
                    caption_for_chunk
                    if (caption_for_chunk and item_index == 0)
                    else None
                )
                await _send_with_retry(
                    f"send_photo fallback {item_index + 1}/{len(chunk)}",
                    lambda p=path, c=cap: bot.send_photo(
                        chat_id,
                        types.FSInputFile(p),
                        caption=c,
                        parse_mode=ParseMode.HTML if c else None,
                        request_timeout=REQUEST_TIMEOUT_SEC,
                    ),
                )

    for index, path in enumerate(images):
        if progress:
            await progress.set_phase(
                f"Отправка изображения {index + 1}/{len(images)} из {total_to_send}"
            )
        cap = None if caption_used or index > 0 else caption_full
        if cap:
            caption_used = True

        await _send_with_retry(
            f"send_document image {index + 1}/{len(images)}",
            lambda p=path, c=cap: bot.send_document(
                chat_id,
                types.FSInputFile(p),
                caption=c,
                parse_mode=ParseMode.HTML if c else None,
                disable_content_type_detection=True,
                request_timeout=REQUEST_TIMEOUT_SEC,
            ),
        )

    for index, path in enumerate(videos):
        if progress:
            await progress.set_phase(
                "Отправка видео "
                f"{index + 1}/{len(videos)} ({_human_size(path.stat().st_size)})"
            )
        cap = None if caption_used else caption_full
        if cap:
            caption_used = True

        try:
            await _send_with_retry(
                f"send_video {index + 1}/{len(videos)}",
                lambda p=path, c=cap: bot.send_video(
                    chat_id,
                    types.FSInputFile(p),
                    caption=c,
                    parse_mode=ParseMode.HTML if c else None,
                    supports_streaming=True,
                    request_timeout=REQUEST_TIMEOUT_SEC,
                ),
            )
        except Exception:
            logging.exception("send_video failed; fallback to send_document: %s", path)
            await _send_with_retry(
                f"send_document video-fallback {index + 1}/{len(videos)}",
                lambda p=path, c=cap: bot.send_document(
                    chat_id,
                    types.FSInputFile(p),
                    caption=c,
                    parse_mode=ParseMode.HTML if c else None,
                    disable_content_type_detection=True,
                    request_timeout=REQUEST_TIMEOUT_SEC,
                ),
            )

    for index, path in enumerate(audios):
        if progress:
            await progress.set_phase(
                f"Отправка аудио {index + 1}/{len(audios)} из {total_to_send}"
            )
        cap = None if caption_used or index > 0 else caption_full
        if cap:
            caption_used = True

        audio_title = build_telegram_audio_title(path, caption_text)
        await _send_with_retry(
            f"send_audio {index + 1}/{len(audios)}",
            lambda p=path, c=cap, t=audio_title: bot.send_audio(
                chat_id,
                types.FSInputFile(p),
                title=t,
                caption=c,
                parse_mode=ParseMode.HTML if c else None,
                request_timeout=REQUEST_TIMEOUT_SEC,
            ),
        )

    for index, path in enumerate(others):
        if progress:
            await progress.set_phase(
                f"Отправка файла {index + 1}/{len(others)} из {total_to_send}"
            )
        cap = None if caption_used or index > 0 else caption_full
        if cap:
            caption_used = True

        await _send_with_retry(
            f"send_document other {index + 1}/{len(others)}",
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
            f"Не отправлено (больше 2 ГБ): {path.name} ({_human_size(path.stat().st_size)})"
            for path in oversized[:10]
        ]
        if len(oversized) > 10:
            lines.append(f"... и еще {len(oversized) - 10} файлов")
        await _send_with_retry(
            "send_oversized_warning",
            lambda: bot.send_message(
                chat_id,
                "\n".join(lines),
                request_timeout=REQUEST_TIMEOUT_SEC,
            ),
        )


@router.message(CommandStart())
async def cmd_start(message: types.Message) -> None:
    await message.answer(
        "Привет! Я скачиваю:\n"
        "- YouTube: видео и посты\n"
        "- TikTok: видео\n"
        "- Instagram: фото и видео\n\n"
        "- Yandex Music: треки, альбомы, плейлисты\n\n"
        "Команды:\n"
        "- @vid <ссылка> — отправить только видео\n"
        "\n"
        "Можно просто отправить ссылку без команды.\n",
        reply_markup=ReplyKeyboardRemove(),
    )


@router.message(Command("help"))
async def cmd_help(message: types.Message) -> None:
    await message.answer(
        "Как пользоваться:\n"
        "1) Отправь ссылку на YouTube -> загружу в лучшем доступном качестве\n"
        "2) Отправь ссылку на TikTok -> загружу и отправлю файлы\n"
        "3) Отправь ссылку на Instagram -> загружу и отправлю файлы\n"
        "4) Отправь ссылку на Yandex Music -> загружу и отправлю аудио\n"
        "5) Отправь @vid <ссылка> -> отправлю только видео\n\n",
        reply_markup=ReplyKeyboardRemove(),
    )


@router.message(F.text | F.caption)
async def handle_link(message: types.Message) -> None:
    media_mode = extract_media_mode_from_message(message)
    url = extract_url_from_message(message)
    log_sender(message, url)
    if not url:
        mode_hint = None
        if media_mode == MEDIA_MODE_VIDEO_ONLY:
            mode_hint = "@vid"
        if mode_hint:
            await message.answer(
                f"Команда {mode_hint} принята, но не вижу ссылку.\n"
                "Отправь в одном сообщении: "
                f"{mode_hint} https://..."
            )
        return

    source = detect_source(url)
    if not source:
        await message.answer(
            "Поддерживаются YouTube, TikTok, Instagram и Yandex Music. Команда /help"
        )
        return

    try:
        await message.delete()
    except Exception:
        pass

    chat_id = message.chat.id
    status_text = "Принял ссылку. Начинаю скачивание..."
    if media_mode == MEDIA_MODE_VIDEO_ONLY:
        status_text = "Принял ссылку (@vid). Начинаю скачивание видео..."
    status = await message.bot.send_message(
        chat_id,
        status_text,
        request_timeout=REQUEST_TIMEOUT_SEC,
    )
    progress = StatusProgress(status, "Скачиваю контент")
    await progress.start()

    tmp_dir: Path | None = None
    cover_path: Path | None = None
    preview_warning: str | None = None
    progress_closed = False

    try:
        if media_mode == MEDIA_MODE_VIDEO_ONLY:
            action = ChatActionSender.upload_video
        elif media_mode == MEDIA_MODE_IMAGE_ONLY:
            action = ChatActionSender.upload_photo
        elif source in {"youtube", "tiktok"}:
            action = ChatActionSender.upload_video
        elif source == "yandex_music":
            action = ChatActionSender.upload_document
        else:
            action = ChatActionSender.typing

        dl_source = (
            "youtube_gallery"
            if (source == "youtube" and is_youtube_gallery_url(url))
            else source
        )

        async with action(bot=message.bot, chat_id=chat_id):
            loop = asyncio.get_running_loop()

            def on_download_progress(line: str) -> None:
                loop.call_soon_threadsafe(progress.set_detail_text, line)

            if source == "yandex_music":

                def yandex_download_job() -> (
                    tuple[List[Path], Path, str | None, Path | None, str | None]
                ):
                    files, td, cap, cover, preview = (
                        _download_yandex_music_with_album_retries(
                            url,
                            on_download_progress,
                        )
                    )
                    tagged = _apply_yandex_audio_tags(url, files, cover_path=cover)
                    if tagged:
                        on_download_progress(
                            f"[tags] updated ID3 tags in {tagged} file(s)"
                        )
                    return files, td, cap, cover, preview

                (
                    files,
                    tmp_dir,
                    caption_text,
                    cover_path,
                    preview_warning,
                ) = await loop.run_in_executor(None, yandex_download_job)
            else:
                download_job = partial(
                    download_media_auto,
                    url,
                    dl_source,
                    on_download_progress,
                )
                files, tmp_dir, caption_text = await loop.run_in_executor(
                    None, download_job
                )

        progress.set_detail_text("")
        await progress.set_phase(f"Отправляю в Telegram: {len(files)} файл(ов)")

        await send_media_to_chat(
            message.bot,
            chat_id,
            files,
            source,
            url,
            caption_text,
            progress=progress,
            media_mode=media_mode,
        )

        await _send_full_caption_if_needed(
            message.bot,
            chat_id,
            source,
            url,
            caption_text,
        )

        if source == "yandex_music" and cover_path and cover_path.exists():
            await _send_with_retry(
                "send_cover_photo",
                lambda p=cover_path: message.bot.send_photo(
                    chat_id,
                    types.FSInputFile(p),
                    request_timeout=REQUEST_TIMEOUT_SEC,
                ),
            )

        if source == "yandex_music" and preview_warning:
            await _send_with_retry(
                "send_preview_warning",
                lambda t=preview_warning: message.bot.send_message(
                    chat_id,
                    t,
                    parse_mode=None,
                    request_timeout=REQUEST_TIMEOUT_SEC,
                ),
            )

        await progress.dismiss()
        progress_closed = True

    except Exception as exc:
        logging.exception("Download pipeline failed")
        error_text = f"Не удалось скачать или отправить:\n{_trim_error_text(str(exc))}"
        updated = await progress.finish(error_text)
        progress_closed = True
        if not updated:
            await _send_with_retry(
                "send_error_message",
                lambda: message.bot.send_message(
                    chat_id,
                    error_text,
                    request_timeout=REQUEST_TIMEOUT_SEC,
                ),
            )

    finally:
        if not progress_closed:
            await progress.dismiss()
        cleanup_tmp_dir(tmp_dir)


@router.message()
async def handle_non_link_message(message: types.Message) -> None:
    if message.text or message.caption:
        return
    if not (message.photo or message.video or message.animation or message.document):
        return
    await message.answer("Я работаю по ссылкам.\n" "Пример: @vid https://...")


async def main() -> None:
    rotating_log, session_log = configure_logging()
    logging.info("Logging initialized")
    logging.info("Rotating log file: %s", rotating_log.resolve())
    logging.info("Session log file: %s", session_log.resolve())

    token = (os.getenv("BOT_TOKEN") or "").strip()
    if not token:
        raise RuntimeError("Set BOT_TOKEN in .env")

    session = build_local_session()
    bot = Bot(
        token=token,
        session=session,
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
