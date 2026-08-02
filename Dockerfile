# r3m_tv_bot.py 를 Railway 등 클라우드에 배포하기 위한 Dockerfile.
# 이 봇은 Playwright가 필요 없어서 가벼운 기본 파이썬 이미지만 쓰면 됩니다.

FROM python:3.11-slim

WORKDIR /app

COPY requirements.txt requirements.txt
RUN pip install --no-cache-dir -r requirements.txt

COPY r3m_tv_bot.py .
COPY r3m_tv_bot_okx.py .

# Railway가 자동으로 PORT 환경변수를 주입합니다. 봇 코드가 그 값을 그대로 읽습니다.
CMD ["python", "r3m_tv_bot.py"]
