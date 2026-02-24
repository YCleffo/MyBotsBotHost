FROM python:3.11-slim

ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    PIP_NO_CACHE_DIR=1

WORKDIR /app

# Системные зависимости:
# ffmpeg нужен для извлечения аудио
# nodejs нужен/желателен для yt-dlp (у тебя js_runtimes={"node": {}})
RUN apt-get update && apt-get install -y --no-install-recommends \
    ffmpeg \
    nodejs \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Устанавливаем Python-зависимости
COPY requirements.txt /app/requirements.txt
RUN pip install --upgrade pip && pip install -r /app/requirements.txt

# Копируем код проекта
COPY . /app

# Создаём пользователя (лучше не root)
RUN useradd -m appuser && chown -R appuser:appuser /app
USER appuser

# Запуск твоего основного файла
CMD ["python", "downloader.py"]