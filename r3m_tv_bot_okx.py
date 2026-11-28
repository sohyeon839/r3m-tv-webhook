"""
zetro(ath.zetro.io) 신호 자동매매 봇 (OKX)

동작 방식
---------
ath.zetro.io 의 신호 API(/api/pub/v1/signals)를 5초마다 조회해서
새 신호가 뜨면 OKX에서 바로 진입합니다. 청산은 진입할 때 같이 걸어두는
익절(TP)/손절(SL)로 자동 처리됩니다.

안전장치
--------
- 봇을 켤 때 이미 떠 있던 신호로는 진입하지 않음
- 3분 넘게 지난 신호는 진입하지 않음
- 같은 신호로 두 번 진입하지 않음 (재시작해도 기억)
- ZETRO_API_KEY 가 없으면 신호 조회만 꺼진 채로 봇은 정상 실행

중요한 전제
------------
OKX 계정의 포지션 모드가 반드시 "단방향(one-way/net)" 모드여야 합니다.

필요 패키지
------------
pip install requests

환경 변수 (Railway Variables)
-----------------------------
OKX_API_KEY, OKX_API_SECRET, OKX_API_PASSPHRASE : OKX API 키 (Trade 권한 필요)
ZETRO_API_KEY                                    : zetro API 키 (ztk_로 시작)
TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID             : (선택) 텔레그램 알림용
"""

from __future__ import annotations

import base64
import hmac
import hashlib
import html
import json
import re
import logging
import math
import os
import threading
import time
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Optional

import requests

# ----------------------------------------------------------------------------
# 진입 설정 — 여기를 원하는 값으로 바꾸세요
# ----------------------------------------------------------------------------

# 증거금 기준 (포지션 규모 = 증거금 × 레버리지)
MARGIN_USDT = 100.0      # 진입 1번당 증거금 (모든 신호 공통)
LEVERAGE = 3             # 기본 레버리지 (신호별로 아래 규칙에서 따로 지정 가능)

# 방향별 배율 (모든 신호 공통으로 우선 적용). None이면 신호별 설정을 따름.
# 익절·손절은 "가격 기준 거리"가 같게 자동으로 맞춰져요.
# 봇이 절대 안 들어가는 종목 (직접 거래하는 종목). 예: {"BTC-USDT-SWAP", "ETH-USDT-SWAP"}
BOT_EXCLUDE_SYMBOLS: set = {"BTC-USDT-SWAP", "ETH-USDT-SWAP"}

# 코인이 아닌 종목(주식·ETF·원자재·외환 선물)은 봇이 안 들어감
# 장 시간·주말에 가격이 건너뛰어서 손절이 제대로 안 걸릴 수 있기 때문
NON_CRYPTO_BLOCK = True
NON_CRYPTO_TICKERS = {
    # 미국 주식·ETF
    "SOXL", "SOXS", "TQQQ", "SQQQ", "SPY", "QQQ", "IWM", "DIA", "GLD", "SLV", "USO", "TLT", "UVXY", "VIX",
    "TSLA", "NVDA", "AAPL", "MSFT", "AMZN", "GOOGL", "GOOG", "META", "NFLX", "AMD", "INTC", "AVGO", "ORCL",
    "MU", "SMCI", "PLTR", "COIN", "MSTR", "HOOD", "CRCL", "BABA", "TSM", "ARM", "ASML", "IBM", "UBER",
    "SHOP", "SNOW", "RBLX", "GME", "AMC", "NVDL", "TSLL", "CONL", "MSTU", "MSTX", "LABU", "TNA", "FAS",
    # 원자재·외환
    "XAU", "XAG", "XPT", "XPD", "WTI", "BRENT", "NATGAS", "COPPER", "EUR", "GBP", "JPY", "AUD", "CAD", "CHF",
}


def is_non_crypto(inst_id: str) -> bool:
    base = inst_id.split("-")[0].upper()
    if base in NON_CRYPTO_TICKERS:
        return True
    try:
        info = _executor.get_instrument(inst_id)
        cat = str(info.get("instCategory", "") or "")
        if cat and cat != "1":      # OKX가 코인이 아닌 종목으로 표시한 경우
            return True
    except Exception:  # noqa: BLE001
        pass
    return False

LONG_ENTRY_ENABLED = True   # 롱 진입 켬 (끄려면 False)
LONG_LEVERAGE = 5        # 롱 5배 (증거금 100 → 포지션 500)
# 롱일 때만 증거금을 따로 (신호 이름: 증거금)
LONG_MARGIN_OVERRIDE: dict = {}   # 롱일 때만 증거금을 따로 (예: {"아트로포스": 150.0})
SHORT_LEVERAGE = 5       # 숏 5배 (증거금 100 → 포지션 500)
TAKE_PROFIT_PCT = 0.10   # 증거금 대비 +10% 익절 (3배 → 가격 +3.33%)
STOP_LOSS_PCT = 0.05     # 증거금 대비 -5% 손절 (3배 → 가격 -1.67%)

# 종목별로 증거금을 다르게 하고 싶을 때만 추가
SYMBOL_MARGIN_OVERRIDE = {
    # "BTC-USDT-SWAP": 200.0,
}

MAX_STACK_POSITIONS = 1   # 같은 종목에 이미 포지션이 있으면 추가 진입 안 함
MAX_BOT_POSITIONS = 4     # 봇 포지션 동시 최대 개수 (숏 2 + 롱 2, 수동 제외) — 잔고 500 기준
MAX_SAME_SIDE = 2         # 같은 방향(숏끼리·롱끼리) 동시 최대 개수 — 장이 한쪽으로 쏠릴 때 한꺼번에 손절 방지
SYMBOL_MAX_STACK_OVERRIDE = {}
# 누적 성적 집계 시작 시각 (한국시간). 이 시각 이후 봇이 진입한 거래만 집계해요.
# 새로 처음부터 세고 싶으면 이 값을 바꾸세요.
STATS_START_KST = "2026-11-24 00:00"   # 11/24 0시부터 누적 성적 새로 시작

# 누적 성적에서 빼버릴 신호 (기록을 지우고 합계에서도 뺌)
STATS_EXCLUDE_SOURCES = {"클러스터"}

# ----------------------------------------------------------------------------
# 포지션 관리: 본절 손절 + 분할 익절 (모두 "가격 기준" %)
# ----------------------------------------------------------------------------
MANAGE_ENABLED = True
MANAGE_POLL_SECONDS = 3            # 3초마다 포지션 확인
# 시간 손절: 이 시간(분) 안에 본절(+1.2%)까지도 못 가면 그 가격에 정리 (신호 이름: 분)
TIME_STOP_MIN: dict = {"오라클 저항": 360}   # 오라클 저항 6시간

# 1) 본절 손절: 가격이 +1.0% 유리하게 가면 손절을 진입가 근처로 올림
BREAKEVEN_TRIGGER_PCT = 0.012     # 분할 익절과 같은 시점(+1.2%)에 본절로
BREAKEVEN_BUFFER_PCT = 0.001       # 진입가보다 0.1% 유리한 곳에 손절 (수수료 정도는 남게)

# 2) 분할 익절: 가격이 +1.2% 유리하게 가면 절반을 먼저 청산
PARTIAL_TP_TRIGGER_PCT = 0.012
PARTIAL_TP_RATIO = 0.5             # 0.5 = 절반 먼저 청산

# 3) 단계 손절: 가격이 +2.0% 유리하게 가면 손절을 +1.0% 수익 자리로 올림
#    (3배 기준 OKX 화면: +6% 도달 → 손절을 +3%로)
STEP_TRIGGER_PCT = 0.020
STEP_LOCK_PCT = 0.010

MAX_DAILY_SL_COUNT = 0    # 손절 "횟수" 한도 (0 = 사용 안 함, 아래 손실 % 한도를 사용)
# 하루(한국시간 0시 기준) 봇 실현손실이 그날 시작 잔고의 5%가 되면 신규 진입 중지, 0시 지나면 자동 재개
MAX_DAILY_LOSS_PCT = 0.05
# 같은 종목을 하루(한국시간 0시 기준)에 이 횟수만큼 손절하면 그 종목은 그날 신규 진입 중지 (0 = 사용 안 함)
MAX_SYMBOL_DAILY_SL = 2

# ----------------------------------------------------------------------------
# zetro 신호 설정
# ----------------------------------------------------------------------------

ZETRO_API_KEY = os.environ.get("ZETRO_API_KEY", "")
ZETRO_SIGNALS_URL = "https://ath.zetro.io/api/pub/v1/signals"
ZETRO_POLL_SECONDS = 5            # 5초마다 조회 (분당 12회, 한도 60회)
ZETRO_MAX_SIGNAL_AGE_SEC = 180    # 기본: 3분보다 오래된 신호는 진입 안 함

# 거래대금 필터 (zetro 스크리너의 "거래대금 100만 달러 이상"과 같은 기준)
# OKX 해당 종목의 최근 24시간 거래대금이 이보다 작으면 진입 안 함
MIN_24H_VOLUME_USD = 1_000_000

# API 조회로 들어온 신호의 실제 진입 ON/OFF
# False: 신호는 계속 조회해서 로그에만 남기고 진입은 안 함 (웹훅 확인 중이라 꺼둔 상태)
# True여도 아래 규칙 중 "api_entry": True 인 신호만 API로 진입 (지금은 아트로포스만)
ZETRO_API_ENTRY_ENABLED = True

# zetro 웹훅 수신 주소 (zetro 웹훅 설정에 넣을 주소의 뒷부분)
ZETRO_HOOK_PATH = "/zetro-hook/5472118043e07db5"

# 매매 기록지 페이지 주소 (폰 브라우저로 열기). 뒤 글자는 비밀번호 역할이라 공유하지 마세요.
REPORT_PATH = "/report/5472118043e07db5"
POSITIONS_PATH = "/positions/5472118043e07db5"   # 실시간 포지션 페이지
WEEKLY_TARGET_USD = 150.0                       # 일주일 목표 수익 (월요일 0시 ~ 일요일)
DAILY_TARGET_USD = 20.0                         # 하루 목표

# ----------------------------------------------------------------------------
# zetro 웹훅 진입 규칙 (zetro 알림 만들기에서 거래대금·위험/주의 코인 등 필터를 걸어둔 알림만 옴)
# zetro 알림 메시지에 넣는 "rule" 값과 아래 이름이 같아야 합니다.
# ----------------------------------------------------------------------------
HOOK_ENTRY_ENABLED = True

# ----------------------------------------------------------------------------
# zetro 스크리너(/screener) 진입 — 홈페이지 스크리너 화면과 같은 결과만 받음
# ----------------------------------------------------------------------------
SCREENER_ENTRY_ENABLED = True
ZETRO_SCREENER_URL = "https://ath.zetro.io/api/pub/v1/screener"
SCREENER_POLL_SECONDS = 10       # 스크리너는 15초마다 갱신 → 10초마다 확인 (분당 6회)

# 화면 스크리너 설정과 똑같이
SCREENER_FILTERS = {
    "minTurnover": "1e6",    # 거래대금 100만 달러 이상
    "weak": "hide",          # 힘 없는 장 거르기
    "noise": "hide",         # 노이즈 제거 (보통)
    "ex": "okx",             # OKX에 있는 종목만
    # show 를 안 넣으면 위험·주의 코인은 기본으로 빠짐
}

SCREENER_RULES = {
    "아트로포스": {
        "find": "atropos",          # 스크리너 조건 id에 이 글자가 들어간 것 (시작할 때 자동으로 찾음)
        "id": None,                 # 자동으로 못 찾으면 여기에 정확한 id를 적으세요
        "tf": "5m",
        "symbols": None,            # 전 종목
        "max_age_sec": 60,          # 뜬 지 1분 이내만
        "margin": 100,              # 증거금 100 USDT (규칙은 3배 기준, 실제 5배 → 포지션 500, 가격 기준 익절·손절 거리는 그대로)
        "leverage": 3,
        "tp_pct": 0.06,             # 증거금 대비 +6% 익절 (3배 → 가격 +2.0%) — 스크리너 최대수익 분석 반영
        "sl_pct": 0.05,             # 증거금 대비 -5% 손절 (3배 → 가격 -1.67%)
    },
    "오라클 저항": {
        "find": "oracle",           # 오라클 선 닿음 (oracle_touch)
        "id": None,
        "kinds": {"l3r", "s4r"},    # 3차 저항선(l3r) · 보조 4차 저항선(s4r) 닿음만 → 숏
                                    # 지지선도 넣으려면 "l3s", "s4s" 추가 (→ 롱)
        "tf": "5m",
        "symbols": None,            # 전 종목
        "max_age_sec": 180,         # 뜬 지 3분 이내만
        "margin": 100,              # 증거금 100 USDT (실제 5배 → 포지션 500). 손절 1번 약 -17.5
        "leverage": 3,              # 아래 % 는 3배 기준 (실제 5배로 들어가도 가격 기준 거리는 그대로)
        "tp_pct": 0.09,             # 가격 -3.0% 에서 익절 (숏)
        "sl_pct": 0.105,            # 가격 +3.5% 에서 손절 (저항선 위 꼬리 버티기, 큰 사고만 막음)
    },
}

HOOK_NAMES = {"cluster": "클러스터", "atropos": "아트로포스", "oracle": "오라클 저항",
              "dip_diamond": "급락매수다이아", "square": "스퀘어"}

HOOK_RULES = {
    "cluster": {            # 클러스터 저항/지지 닿음
        "enabled": False,   # ⛔ 성적 부진으로 꺼둠 (다시 켜려면 True)
        "symbols": None,
        "intervals": {"5"},
        "max_age_sec": 600,   # zetro가 보내는 time은 봉 시작 시각이라 5분봉+여유로 10분
        "leverage": 3,      # 증거금 300 × 3배 = 포지션 900 USDT
        "tp_pct": 0.10,     # 증거금 대비 +10% 익절 (3배 → 가격 +3.33%)
        "sl_pct": 0.05,     # 증거금 대비 -5% 손절 (3배 → 가격 -1.67%)
    },
    "atropos": {            # 아트로포스 (API 키가 멈췄을 때 zetro 알림으로 대신 받기)
        "margin": 100,
        "tp_pct": 0.06,     # 가격 +2.0% (3배 기준)
        "symbols": None,
        "intervals": {"5"},
        "max_age_sec": 600,   # zetro가 보내는 time은 봉 시작 시각이라 5분봉+여유로 10분
        "leverage": LEVERAGE,
    },
    "oracle": {             # 오라클 저항 (API 키가 멈췄을 때 zetro 알림으로 대신 받기)
        "margin": 100,
        "tp_pct": 0.09,       # 가격 -3.0% 익절 (3배 기준)
        "sl_pct": 0.105,      # 가격 +3.5% 손절 (3배 기준)
        "symbols": None,
        "intervals": {"5"},
        "sides": {"short"},   # 저항 닿음 → 숏만
        "max_age_sec": 600,
        "leverage": 3,
    },
    "dip_diamond": {        # 급락 매수 다이아
        "enabled": False,
        "symbols": None,
        "intervals": {"5"},
        "max_age_sec": 600,   # zetro가 보내는 time은 봉 시작 시각이라 5분봉+여유로 10분
        "leverage": 3,
    },
    "square": {             # 스퀘어 (BTC만)
        "enabled": False,
        "symbols": {"BTCUSDT"},
        "intervals": {"5"},
        "max_age_sec": 600,   # zetro가 보내는 time은 봉 시작 시각이라 5분봉+여유로 10분
        "leverage": LEVERAGE,
    },
}

# 진입할 신호 규칙
#   symbols    : 진입 허용 종목 (None이면 전 종목)
#   max_age_sec: 신호가 뜬 뒤 이 시간(초) 안에만 진입
# zetro API 신호 코드 (시작 시 받은 신호 종류 목록으로 확인한 값)
#   atropos            = 아트로포스
#   square             = 스퀘어 (kind: buy=롱 / sell=숏)
#   diamond            = 다이아 (kind: blue=급락 매수 다이아, rocket=급락 매수 로켓,
#                                 green, pink, skull 등은 다른 다이아)
#   cluster_touch      = 클러스터 (kind: res=저항 닿음, sup=지지 닿음)
#
#   type : 신호 코드 (정확히 일치)
#   kinds: 그 안의 세부 종류 (None이면 전부)
ZETRO_SIGNAL_RULES = {
    "급락매수다이아": {
        "type": "diamond",
        "kinds": {"blue"},          # 급락 매수 다이아만
        "symbols": None,            # 전 종목
        "tfs": {"5m"},
        "max_age_sec": ZETRO_MAX_SIGNAL_AGE_SEC,
        "leverage": 3,              # 증거금 300 × 3배 = 포지션 900 USDT
    },
    "아트로포스": {
        "type": "atropos",
        "kinds": None,
        "symbols": None,            # BTC 포함 전 종목
        "tfs": {"5m"},
        "max_age_sec": 60,          # 뜬 지 1분 이내만
        "leverage": 3,              # 증거금 300 × 3배 = 포지션 900 USDT
        "tp_pct": 0.10,             # 증거금 대비 +10% 익절 (3배 → 가격 +3.33%)
        "sl_pct": 0.05,             # 증거금 대비 -5% 손절 (3배 → 가격 -1.67%)
        "api_entry": False,         # 아트로포스는 아래 스크리너(/screener)로 진입
    },
    "스퀘어": {
        "type": "square",
        "kinds": None,
        "symbols": {"BTCUSDT"},     # BTC만
        "tfs": {"5m"},
        "max_age_sec": ZETRO_MAX_SIGNAL_AGE_SEC,
        "leverage": LEVERAGE,
    },
    "클러스터 저항": {
        "type": "cluster_touch",
        "kinds": {"res"},
        "symbols": None,
        "tfs": {"5m"},
        "max_age_sec": ZETRO_MAX_SIGNAL_AGE_SEC,
        "leverage": LEVERAGE,
    },
    "클러스터 지지": {
        "type": "cluster_touch",
        "kinds": {"sup"},
        "symbols": None,
        "tfs": {"5m"},
        "max_age_sec": ZETRO_MAX_SIGNAL_AGE_SEC,
        "leverage": LEVERAGE,
    },
}

# ----------------------------------------------------------------------------
# 기타
# ----------------------------------------------------------------------------

PORT = int(os.environ.get("PORT", 8789))   # Railway 상태 확인용
# Railway에 Volume을 붙이면 RAILWAY_VOLUME_MOUNT_PATH(예: /data)가 자동으로 생기고,
# 상태 파일(누적 성적, 처리한 신호 등)을 거기에 저장해서 재배포해도 안 지워져요.
STATE_DIR = Path(os.environ.get("RAILWAY_VOLUME_MOUNT_PATH") or ".")
STATE_DIR.mkdir(parents=True, exist_ok=True)
STATE_FILE = STATE_DIR / "r3m_tv_okx_state.json"
OKX_BASE_URL = "https://www.okx.com"
TD_MODE = "cross"  # 교차 마진. 격리 원하면 "isolated"

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("zetro_okx_bot")


# 봇이 거는 익절·손절 주문에 붙이는 이름표 (수동으로 건 주문과 구분하려고)
BOT_ALGO_PREFIX = "zbot"


def bot_algo_id() -> str:
    return f"{BOT_ALGO_PREFIX}{int(time.time() * 1000)}{threading.get_ident() % 1000:03d}"[:32]


def is_bot_algo(a: dict) -> bool:
    cid = str(a.get("algoClOrdId") or a.get("attachAlgoClOrdId") or "")
    return cid.startswith(BOT_ALGO_PREFIX)


class OkxApiError(RuntimeError):
    def __init__(self, data: dict):
        self.data = data
        first = (data.get("data") or [{}])[0]
        self.scode = str(first.get("sCode", ""))
        self.smsg = first.get("sMsg", "")
        super().__init__(f"OKX API 오류: {data}")


OKX_ERROR_MESSAGES = {
    "50001": "거래소 시스템 점검 중",
    "50004": "요청 시간 초과 (체결 여부 불확실 — 포지션 확인 필요)",
    "50005": "OKX API 일시 중단",
    "50011": "요청이 너무 잦음 (레이트 리밋)",
    "50013": "거래소 시스템 혼잡, 잠시 후 재시도 필요",
    "51000": "요청 파라미터 오류",
    "51001": "존재하지 않는 종목",
    "51004": "주문 수량이 한도 초과",
    "51006": "주문 가격이 허용 범위를 벗어남",
    "51008": "증거금(USDT) 부족",
    "51009": "주문 기능이 일시적으로 제한됨(거래소 측)",
    "51119": "잔고 부족으로 주문 실패",
    "51127": "사용 가능한 잔고가 0",
    "51131": "잔고 부족",
    "59100": "미체결 포지션이 있어 레버리지 변경 불가",
    "59101": "격리 모드 미체결 주문이 있어 레버리지 변경 불가",
    "59102": "설정한 레버리지가 최대 허용치 초과",
    "59103": "레버리지 대비 증거금 부족",
    "59108": "레버리지가 낮고 증거금도 부족함",
}


def format_okx_error(e: Exception) -> str:
    if isinstance(e, OkxApiError):
        known = OKX_ERROR_MESSAGES.get(e.scode)
        if known:
            return known
        if e.smsg:
            return e.smsg.strip()
    return str(e)


def notify(title: str, message: str) -> None:
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        return
    try:
        requests.post(
            f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage",
            data={"chat_id": TELEGRAM_CHAT_ID, "text": f"{title}\n{message}"},
            timeout=10,
        )
    except Exception as e:  # noqa: BLE001
        log.warning("텔레그램 알림 전송 실패: %s", e)


# ----------------------------------------------------------------------------
# 상태 저장 / 일일 통계
# ----------------------------------------------------------------------------

_state: Optional[dict] = None
_state_lock = threading.Lock()


def load_state() -> dict:
    if STATE_FILE.exists():
        try:
            return json.loads(STATE_FILE.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            log.warning("상태 파일이 손상되어 새로 시작합니다.")
    return {"positions": {}}


def save_state(state: dict) -> None:
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")


KST = timezone(timedelta(hours=9))


def _today() -> str:
    # 하루 기준을 한국시간 0시로 (손절 횟수, 승패, 누적 손익 모두)
    return datetime.now(KST).strftime("%Y-%m-%d")


def _daily(key: str, defaults: dict) -> dict:
    today = _today()
    d = _state.setdefault(key, {"date": today, **defaults})
    if d.get("date") != today:
        d.clear()
        d.update({"date": today, **defaults})
    return d


# 손실 한도로 멈춘 날 다시 돌릴 때 이 줄을 바꿔서 커밋 (새 배포 → 오늘 한도 초기화)
LIMIT_RESET_NOTE = "2026-11-26 09:2x 사용자 요청으로 다시 시작"


def reset_sl_on_new_commit() -> None:
    """GitHub에서 코드를 수정해 새로 배포됐을 때만 오늘 손절 횟수를 0으로 초기화.
    (서버 재시작·Railway 재시작처럼 코드가 그대로면 초기화 안 함)"""
    commit = os.environ.get("RAILWAY_GIT_COMMIT_SHA", "")
    if not commit:
        log.info("커밋 정보가 없어 손절 횟수 초기화 여부를 판단하지 않음")
        return
    last = _state.get("last_commit")
    _state["last_commit"] = commit
    if last and last != commit:
        d = _daily("daily_sl", {"count": 0})
        before = d.get("count", 0)
        d["count"] = 0
        base = _daily("daily_base", {"eq": None, "anchor_pnl": 0.0, "notified": False})
        base["eq"] = None          # 다음 리포트 때 현재 잔고로 기준 다시 잡음
        base["notified"] = False
        save_state(_state)
        log.info("새 코드 배포(%s → %s) — 오늘 손절 횟수 %d회 → 0회로 초기화", last[:7], commit[:7], before)
        if before:
            notify("🔄 오늘 손실 한도 초기화",
                   f"코드가 새로 배포돼서 오늘 손실 한도를 다시 시작했어요.\n"
                   f"오늘 승패·실현손익·누적 성적은 그대로예요.")
    else:
        save_state(_state)


def ensure_daily_base(eq: Optional[float] = None) -> None:
    """오늘 손실 한도 기준이 될 '오늘 시작 잔고'를 하루 한 번 기록."""
    d = _daily("daily_base", {"eq": None, "anchor_pnl": 0.0, "notified": False})
    if d.get("eq") is None and eq:
        d["eq"] = float(eq)
        d["anchor_pnl"] = _daily("daily_pnl", {"total": 0.0})["total"]
        save_state(_state)
        log.info("오늘 손실 한도 기준 잔고: %.2f USDT (한도 -%.2f)", eq, eq * MAX_DAILY_LOSS_PCT)


def daily_loss_info() -> tuple:
    """(오늘 손실액, 한도액) — 한도액이 없으면 None"""
    d = _daily("daily_base", {"eq": None, "anchor_pnl": 0.0, "notified": False})
    if not d.get("eq") or not MAX_DAILY_LOSS_PCT:
        return 0.0, None
    total = _daily("daily_pnl", {"total": 0.0})["total"] - d.get("anchor_pnl", 0.0)
    return total, d["eq"] * MAX_DAILY_LOSS_PCT


def check_daily_sl_limit() -> bool:
    if MAX_DAILY_SL_COUNT and _daily("daily_sl", {"count": 0})["count"] >= MAX_DAILY_SL_COUNT:
        return True
    loss, limit = daily_loss_info()
    return limit is not None and loss <= -limit


def maybe_notify_loss_limit() -> None:
    loss, limit = daily_loss_info()
    d = _daily("daily_base", {"eq": None, "anchor_pnl": 0.0, "notified": False})
    if limit is not None and loss <= -limit and not d.get("notified"):
        d["notified"] = True
        save_state(_state)
        notify("⛔ 오늘 자동매매 중지",
               f"오늘 손실 {loss:+.2f} USDT로 한도(-{limit:.2f}, 시작 잔고의 {MAX_DAILY_LOSS_PCT * 100:.0f}%)에 도달했어요.\n"
               f"이미 열린 포지션은 익절/손절 그대로 유지되고,\n"
               f"내일 한국시간 0시에 자동으로 다시 시작해요.")


def record_sl_hit() -> None:
    d = _daily("daily_sl", {"count": 0})
    d["count"] += 1
    save_state(_state)
    log.warning("오늘 손절 %d회째 발생", d["count"])
    if MAX_DAILY_SL_COUNT and d["count"] == MAX_DAILY_SL_COUNT:
        notify("⛔ 오늘 자동매매 중지",
               f"오늘 손절 {MAX_DAILY_SL_COUNT}회에 도달해서 신규 진입을 멈춥니다.\n"
               f"이미 열린 포지션은 익절/손절 그대로 유지되고,\n"
               f"내일 한국시간 0시에 자동으로 다시 시작해요.")


def record_symbol_sl(inst_id: str) -> int:
    """종목별 오늘 손절 횟수를 1 올리고 현재 횟수를 돌려줌."""
    d = _daily("daily_symbol_sl", {"counts": {}})
    d["counts"][inst_id] = d["counts"].get(inst_id, 0) + 1
    save_state(_state)
    cnt = d["counts"][inst_id]
    log.warning("%s 오늘 손절 %d회째", inst_id, cnt)
    if MAX_SYMBOL_DAILY_SL and cnt == MAX_SYMBOL_DAILY_SL:
        notify(f"⛔ {inst_id} 오늘 진입 중지",
               f"{inst_id} 이(가) 오늘 손절 {cnt}회에 도달해서 이 종목은 오늘 더 이상 진입하지 않아요.\n"
               f"다른 종목은 그대로 진행되고, 내일 한국시간 0시에 다시 시작해요.")
    return cnt


def symbol_sl_blocked(inst_id: str) -> bool:
    if not MAX_SYMBOL_DAILY_SL:
        return False
    d = _daily("daily_symbol_sl", {"counts": {}})
    return d["counts"].get(inst_id, 0) >= MAX_SYMBOL_DAILY_SL


def record_trade_result(success: bool) -> dict:
    d = _daily("daily_trade_stats", {"success": 0, "fail": 0})
    d["success" if success else "fail"] += 1
    save_state(_state)
    return d


def get_trade_stats() -> dict:
    return _daily("daily_trade_stats", {"success": 0, "fail": 0})


def record_win_loss(is_win: bool) -> dict:
    d = _daily("daily_win_loss", {"win": 0, "loss": 0})
    d["win" if is_win else "loss"] += 1
    save_state(_state)
    return d


def record_daily_pnl(pnl: float) -> dict:
    d = _daily("daily_pnl", {"total": 0.0})
    d["total"] += pnl
    save_state(_state)
    return d


def _stats_start_ms() -> int:
    dt = datetime.strptime(STATS_START_KST, "%Y-%m-%d %H:%M").replace(tzinfo=KST)
    return int(dt.timestamp() * 1000)


def _cum_stats() -> dict:
    """누적 성적. 시작 시각을 바꾸면 자동으로 새로 시작."""
    st = _state.setdefault("cum_stats", {})
    if st.get("start") != STATS_START_KST:
        st.clear()
        st.update({"start": STATS_START_KST, "win": 0, "loss": 0, "pnl": 0.0,
                   "best": None, "worst": None, "by_source": {}})
    return st


def merge_split_sources() -> None:
    """'아트로포스 롱', '아트로포스 숏', '아트로포스 (나누기 전)' 처럼 나뉜 기록을 신호별로 다시 합침."""
    st = _cum_stats()
    bs = st.get("by_source", {})
    for name in list(bs):
        base = name
        for suf in (" (나누기 전)", " 롱", " 숏"):
            if base.endswith(suf):
                base = base[: -len(suf)]
        if base != name:
            src = bs.pop(name)
            dst = bs.setdefault(base, {"win": 0, "loss": 0, "pnl": 0.0})
            dst["win"] += src.get("win", 0)
            dst["loss"] += src.get("loss", 0)
            dst["pnl"] += src.get("pnl", 0.0)
    save_state(_state)


def purge_excluded_sources() -> None:
    """STATS_EXCLUDE_SOURCES 에 있는 신호 기록을 누적 성적에서 지우고 합계에서도 뺌 (한 번만 적용됨)."""
    st = _cum_stats()
    for name in list(st.get("by_source", {})):
        if name in STATS_EXCLUDE_SOURCES:
            src = st["by_source"].pop(name)
            st["win"] -= src.get("win", 0)
            st["loss"] -= src.get("loss", 0)
            st["pnl"] -= src.get("pnl", 0.0)
            log.info("누적 성적에서 %s 기록 삭제 (%d승 %d패, %+.2f USDT)",
                     name, src.get("win", 0), src.get("loss", 0), src.get("pnl", 0.0))
    save_state(_state)


def record_cum_trade(source: str, pnl: float) -> dict:
    st = _cum_stats()
    if source in STATS_EXCLUDE_SOURCES:
        return st
    key = "win" if pnl >= 0 else "loss"
    st[key] += 1
    st["pnl"] += pnl
    st["best"] = pnl if st["best"] is None else max(st["best"], pnl)
    st["worst"] = pnl if st["worst"] is None else min(st["worst"], pnl)
    src = st["by_source"].setdefault(source, {"win": 0, "loss": 0, "pnl": 0.0})
    src[key] += 1
    src["pnl"] += pnl
    save_state(_state)
    return st


def format_cum_stats() -> str:
    st = _cum_stats()
    n = st["win"] + st["loss"]
    if n == 0:
        return f"📒 누적 성적 ({st['start']} 부터)\n아직 종료된 거래 없음"
    rate = st["win"] / n * 100
    lines = [
        f"📒 누적 성적 ({st['start']} 부터)",
        f"🏆 {st['win']}승 {st['loss']}패 (승률 {rate:.0f}%)",
        f"💵 누적 실현손익: {st['pnl']:+.2f} USDT",
        f"📊 거래당 평균: {st['pnl'] / n:+.2f} USDT",
        f"⬆️ 최고 {st['best']:+.2f} / ⬇️ 최저 {st['worst']:+.2f}",
    ]
    for name, src in st["by_source"].items():
        m = src["win"] + src["loss"]
        lines.append(f"  · {name}: {src['win']}승 {src['loss']}패, {src['pnl']:+.2f} USDT"
                     f" (승률 {src['win'] / m * 100:.0f}%)" if m else f"  · {name}: -")
    return "\n".join(lines)


# ----------------------------------------------------------------------------
# 매매 기록지
# ----------------------------------------------------------------------------

def _journal_day(date: str) -> dict:
    j = _state.setdefault("journal", {})
    return j.setdefault(date, {"win": 0, "be": 0, "loss": 0, "pnl": 0.0, "by_source": {},
                               "start_eq": None, "end_eq": None})


BE_MOVE_PCT = 0.009   # 평균 청산가가 진입가에서 0.9% 안쪽이면 "본절" (분할 익절 후 나머지가 진입가 근처에서 끝난 경우)


def classify_close(pnl: float, row: Optional[dict]) -> str:
    """OKX 포지션 기록으로 익절/본절/손절 구분."""
    if pnl < 0:
        return "loss"
    if pnl < 1.0:
        return "be"
    try:
        o = float(row.get("openAvgPx") or 0)
        c = float(row.get("closeAvgPx") or 0)
        if o and c:
            long_ = str(row.get("direction", "")).lower() == "long"
            move = (c - o) / o if long_ else (o - c) / o
            if move < BE_MOVE_PCT:
                return "be"
    except Exception:  # noqa: BLE001
        pass
    return "win"


def trades_csv() -> bytes:
    """거래 기록 전체를 엑셀에서 열 수 있는 CSV로 (한글 깨짐 방지 BOM 포함)"""
    import csv
    import io
    cols = [("시간(KST)", None), ("종목", "inst"), ("신호", "src"), ("방향", "side"), ("결과", "kind"),
            ("실현손익", "pnl"), ("수수료전손익", "gross"), ("수수료", "fee"), ("펀딩비", "funding"),
            ("진입가", "entry"), ("청산가", "close"), ("보유(분)", "hold_min"), ("증거금", "margin"),
            ("배율", "lev"), ("익절거리", "tp_px_pct"), ("손절거리", "sl_px_pct"), ("본절", "be"), ("절반익절", "partial"), ("단계손절", "step"), ("시간손절", "time_stop")]
    kind_ko = {"win": "익절", "be": "본절", "loss": "손절"}
    side_ko = {"S": "숏", "L": "롱"}
    with _state_lock:
        rows = list(_state.get("trade_log", []))
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow([c[0] for c in cols])
    for t in rows:
        out = []
        for name, key in cols:
            if key is None:
                out.append(datetime.fromtimestamp(t.get("t", 0) / 1000, KST).strftime("%Y-%m-%d %H:%M:%S"))
                continue
            v = t.get(key)
            if key == "kind":
                v = kind_ko.get(v, v)
            elif key == "side":
                v = side_ko.get(v, v)
            elif isinstance(v, bool):
                v = "O" if v else ""
            out.append("" if v is None else v)
        w.writerow(out)
    return ("\ufeff" + buf.getvalue()).encode("utf-8")


TRADE_LOG_MAX = 20000   # 거래 기록 최대 보관 건수 (한 달 수천 건도 넉넉히)


def journal_record(inst_id: str, source: str, side: Optional[str], pnl: float,
                   kind: Optional[str] = None, extra: Optional[dict] = None) -> str:
    """거래 1건을 기록지에 남김. 결과 종류(익절/본절/손절)를 돌려줌."""
    kind = kind or ("loss" if pnl < 0 else ("be" if pnl < 1.0 else "win"))
    day = _journal_day(_today())
    day[kind] += 1
    day["pnl"] += pnl
    src = day["by_source"].setdefault(source, {"win": 0, "be": 0, "loss": 0, "pnl": 0.0})
    src[kind] += 1
    src["pnl"] += pnl
    log_list = _state.setdefault("trade_log", [])
    rec = {"t": int(time.time() * 1000), "inst": inst_id, "src": source,
           "side": side, "pnl": round(pnl, 4), "kind": kind}
    if extra:
        rec.update({k: v for k, v in extra.items() if v is not None})
    log_list.append(rec)
    if len(log_list) > TRADE_LOG_MAX:
        del log_list[:-TRADE_LOG_MAX]
    j = _state["journal"]
    if len(j) > 400:
        for k in sorted(j)[:-400]:
            j.pop(k, None)
    save_state(_state)
    return kind


def journal_set_equity(cash: float, total: Optional[float] = None) -> None:
    today = _today()
    day = _journal_day(today)
    if day.get("start_eq") is None:
        day["start_eq"] = round(cash, 2)
    day["end_eq"] = round(cash, 2)
    if total is not None:
        if day.get("start_total") is None:
            # 기록 첫날은 정해둔 시작 금액, 그 뒤로는 0시 직후 잔액
            day["start_total"] = (STARTING_BALANCE if (today == JOURNAL_START and STARTING_BALANCE)
                                  else round(total, 2))
        day["end_total"] = round(total, 2)
    save_state(_state)


def bot_start_balances(journal: dict) -> dict:
    """자동매매만 따로 본 '0시 잔액': 시작 금액 + 그 전날까지 봇 실현손익 합계 (수동·입출금 제외)"""
    out, run = {}, STARTING_BALANCE
    for d in sorted(k for k in journal if k >= JOURNAL_START):
        out[d] = run
        run += journal[d].get("pnl", 0.0)
    return out


def day_growth(day: dict) -> Optional[float]:
    """그날 수익률(%) = (마감 잔액 - 0시 잔액 - 입출금) / 0시 잔액"""
    st, en = day.get("start_total"), day.get("end_total")
    if not st or en is None:
        return None
    return (en - st - day.get("dep", 0.0) - day.get("wd", 0.0)) / st * 100


def sync_transfers() -> None:
    """OKX 이체 내역을 읽어서 입금(거래 계정으로 들어옴)·출금(나감)을 날짜별 기록지에 남김."""
    try:
        bills = _executor.get_transfer_bills()
    except Exception as e:  # noqa: BLE001
        if not _state.get("_transfer_warned"):
            log.warning("이체 내역 조회 실패(API 키에 읽기 권한이 있는지 확인): %s", format_okx_error(e))
            _state["_transfer_warned"] = True
        return
    new_items = []
    with _state_lock:
        seen = _state.setdefault("transfer_seen", [])
        first = not seen and not _state.get("transfer_init")
        today = _today()
        for b in sorted(bills, key=lambda x: int(x.get("ts", 0) or 0)):
            bid = str(b.get("billId", ""))
            if not bid or bid in seen:
                continue
            seen.append(bid)
            amt = float(b.get("balChg", 0) or 0)
            ts = int(b.get("ts", 0) or 0)
            date = datetime.fromtimestamp(ts / 1000, KST).strftime("%Y-%m-%d")
            if first and date != today:
                continue   # 처음 켰을 때는 오늘 것만 기록
            day = _journal_day(date)
            if amt >= 0:
                day["dep"] = round(day.get("dep", 0.0) + amt, 2)
            else:
                day["wd"] = round(day.get("wd", 0.0) + amt, 2)
            new_items.append((date, amt))
        _state["transfer_init"] = True
        if len(seen) > 500:
            del seen[:-500]
        save_state(_state)
    for date, amt in new_items:
        if amt < 0:
            notify("🏦 출금 기록 (OKX)", f"거래 계정에서 {amt:.2f} USDT 나갔어요.\n기록지 {date} 칸에 출금으로 남겼어요.")
        else:
            notify("🏦 입금 기록 (OKX)", f"거래 계정으로 +{amt:.2f} USDT 들어왔어요.\n기록지 {date} 칸에 입금으로 남겼어요.")


# 지난 날짜를 OKX 거래 내역으로 다시 계산해서 기록지에 채움 (한 번만 실행)
BACKFILL_DATES: list = []   # 지난 날짜 다시 계산 안 함

# 이 날짜 이전 기록지·거래 기록은 지움 (11/24부터 새로 기록, 자동매매만 1000으로 다시 시작)
JOURNAL_START = "2026-11-24"
STARTING_BALANCE = 1000.0   # 기록 시작할 때 잔고 (기록지 맨 위에 표시)


def purge_old_journal() -> None:
    j = _state.get("journal", {})
    for d in [d for d in j if d < JOURNAL_START]:
        j.pop(d, None)
    start_ms = int(datetime.strptime(JOURNAL_START, "%Y-%m-%d").replace(tzinfo=KST).timestamp() * 1000)
    tl = _state.get("trade_log", [])
    _state["trade_log"] = [t for t in tl if t.get("t", 0) >= start_ms]
    save_state(_state)


# 하루 기록 지우기 (한 번만 실행): 이 날짜에 봇이 켜지기 전까지 한 거래를 기록지·누적 성적·오늘 한도에서 지움
# → 그날 0시처럼 다시 시작. 다시 쓰려면 날짜와 id를 바꾸면 돼요.
WIPE_DAY = {"date": "2026-11-26", "id": "wipe-1126"}


def wipe_day_once() -> None:
    date, wid = WIPE_DAY.get("date"), WIPE_DAY.get("id")
    if not date or not wid:
        return
    with _state_lock:
        done = _state.setdefault("wiped", [])
        if wid in done:
            return
        now_ms = int(time.time() * 1000)
        d0 = int(datetime.strptime(date, "%Y-%m-%d").replace(tzinfo=KST).timestamp() * 1000)
        tl = _state.get("trade_log", [])
        gone = [t for t in tl if d0 <= t.get("t", 0) < now_ms]
        _state["trade_log"] = [t for t in tl if t not in gone]
        # 누적 성적에서 빼기
        st = _cum_stats()
        smin = _stats_start_ms()
        for t in gone:
            if t.get("t", 0) < smin or t.get("src") in STATS_EXCLUDE_SOURCES:
                continue
            pnl = float(t.get("pnl", 0.0))
            key = "win" if pnl >= 0 else "loss"
            st[key] = max(0, st.get(key, 0) - 1)
            st["pnl"] = st.get("pnl", 0.0) - pnl
            src = st.get("by_source", {}).get(t.get("src") or "기타")
            if src:
                src[key] = max(0, src.get(key, 0) - 1)
                src["pnl"] = src.get("pnl", 0.0) - pnl
                if not src.get("win") and not src.get("loss"):
                    st["by_source"].pop(t.get("src") or "기타", None)
        rest = [float(t.get("pnl", 0.0)) for t in _state["trade_log"]
                if t.get("t", 0) >= smin and t.get("src") not in STATS_EXCLUDE_SOURCES]
        st["best"] = max(rest) if rest else None
        st["worst"] = min(rest) if rest else None
        # 그날 기록지 칸: 0시 잔액·입출금은 두고 거래만 0으로
        day = _state.get("journal", {}).get(date)
        if day:
            day.update({"win": 0, "be": 0, "loss": 0, "pnl": 0.0, "by_source": {}})
        # 오늘 한도·카운터 초기화 (오늘이 그 날짜일 때)
        if _today() == date:
            for k in ("daily_pnl", "daily_sl", "daily_symbol_sl", "daily_trade_stats",
                      "daily_win_loss", "daily_base"):
                _state.pop(k, None)
        done.append(wid)
        save_state(_state)
    total = sum(float(t.get("pnl", 0.0)) for t in gone)
    log.info("%s 기록 %d건(합계 %+.2f) 지움", date, len(gone), total)
    notify("🧹 오늘 기록 초기화",
           f"{date} 거래 {len(gone)}건 (합계 {total:+.2f} USDT)을 기록지·누적 성적에서 지웠어요.\n"
           f"오늘 손실 한도도 0시처럼 다시 시작해요.\n(OKX 실제 잔고는 그대로예요)")


def backfill_journal() -> None:
    with _state_lock:
        done = set(_state.get("backfilled_v2", []))
    todo = [d for d in BACKFILL_DATES if d not in done]
    if not todo:
        return
    oldest = min(todo)
    start_ms = int(datetime.strptime(oldest, "%Y-%m-%d").replace(tzinfo=KST).timestamp() * 1000)
    rows, after = [], None
    try:
        for _ in range(30):   # 최대 3,000건
            page = _executor.get_positions_history(after)
            if not page:
                break
            rows.extend(page)
            last = min(int(r.get("uTime", 0) or 0) for r in page)
            if last < start_ms:
                break
            after = last
    except Exception as e:  # noqa: BLE001
        log.warning("지난 기록 불러오기 실패: %s", format_okx_error(e))
        return

    agg = {d: {"win": 0, "be": 0, "loss": 0, "pnl": 0.0} for d in todo}
    seen = set()
    for r in rows:
        key = (r.get("posId"), r.get("uTime"))
        if key in seen:
            continue
        seen.add(key)
        if str(r.get("type", "")) == "1":      # 부분 청산 중인 기록은 제외 (완전히 끝난 것만)
            continue
        if r.get("instId") in BOT_EXCLUDE_SYMBOLS:   # 수동 거래 종목 제외
            continue
        date = datetime.fromtimestamp(int(r.get("uTime", 0) or 0) / 1000, KST).strftime("%Y-%m-%d")
        if date not in agg:
            continue
        pnl = float(r.get("pnl", 0) or 0)
        kind = classify_close(pnl, r)
        agg[date][kind] += 1
        agg[date]["pnl"] += pnl

    with _state_lock:
        for d, a in agg.items():
            day = _journal_day(d)
            day.update(win=a["win"], be=a["be"], loss=a["loss"], pnl=round(a["pnl"], 4))
            day["backfilled"] = True
            log.info("기록지 %s 다시 계산: 익절 %d / 본절 %d / 손절 %d, %+.2f (BTC·ETH 제외)",
                     d, a["win"], a["be"], a["loss"], a["pnl"])
        _state["backfilled_v2"] = sorted(done | set(todo))
        save_state(_state)


def seed_journal_today() -> None:
    """기록지가 처음 생길 때, 오늘 이미 쌓인 성적을 오늘 칸에 넣어둠."""
    if _state.get("journal"):
        return
    wl = _daily("daily_win_loss", {"win": 0, "loss": 0})
    pnl = _daily("daily_pnl", {"total": 0.0})["total"]
    day = _journal_day(_today())
    day["win"] = wl.get("win", 0)
    day["loss"] = wl.get("loss", 0)
    day["pnl"] = pnl
    save_state(_state)


def report_url() -> str:
    domain = os.environ.get("RAILWAY_PUBLIC_DOMAIN") or "r3m-tv-webhook-production-abf1.up.railway.app"
    return f"https://{domain}{REPORT_PATH}"


def format_day_summary(date: str) -> str:
    day = _state.get("journal", {}).get(date)
    if not day:
        return f"🗓 {date}\n거래 없음"
    n = day["win"] + day["be"] + day["loss"]
    pct = (day["pnl"] / DAILY_TARGET_USD * 100) if DAILY_TARGET_USD else 0
    lines = [
        f"🗓 {date} 하루 정산",
        f"🔢 거래 {n}번",
        f"✅ 익절 {day['win']}회",
        f"➖ 본절 {day['be']}회",
        f"🛑 손절 {day['loss']}회",
        f"💵 실현손익: {day['pnl']:+.2f} USDT",
        f"🎯 하루 목표 {DAILY_TARGET_USD:g} 대비 {pct:.0f}%",
    ]
    if WEEKLY_TARGET_USD:
        dt = datetime.strptime(date, "%Y-%m-%d")
        ws = (dt - timedelta(days=dt.weekday())).strftime("%Y-%m-%d")
        wsum = sum(v.get("pnl", 0.0) for d, v in _state.get("journal", {}).items() if max(ws, JOURNAL_START) <= d <= date)
        lines.append(f"📅 이번 주 {wsum:+.2f} / 목표 {WEEKLY_TARGET_USD:.0f} ({wsum / WEEKLY_TARGET_USD * 100:.0f}%)")
    dep, wd = day.get("dep", 0.0), day.get("wd", 0.0)
    if dep or wd:
        lines.append(f"🏦 입출금: 입금 +{dep:.2f} / 출금 {wd:.2f} → 합계 {dep + wd:+.2f}")
    b_start = bot_start_balances(_state.get("journal", {})).get(date)
    if b_start:
        lines.append(f"🌅 자동매매 0시 잔액 {b_start:.2f} → 마감 {b_start + day['pnl']:.2f}"
                     f" (하루 수익률 {day['pnl'] / b_start * 100:+.2f}%)")
    acct = _state.get("last_account")
    if acct:
        lines.append(f"💰 계좌 전체 잔액: {acct['eq']:.2f} USDT (수동 포함)")
    for name, src in day["by_source"].items():
        lines.append(f"  · {name}: 익절 {src['win']}회 · 본절 {src['be']}회 · 손절 {src['loss']}회, {src['pnl']:+.2f}")
    lines.append(f"📒 기록지: {report_url()}")
    return "\n".join(lines)


def daily_close_loop():
    """한국시간 0시가 지나면 어제 하루 정산을 텔레그램으로 보냄."""
    while True:
        try:
            today = _today()
            with _state_lock:
                last = _state.get("journal_last_day")
                if last is None:
                    _state["journal_last_day"] = today
                    save_state(_state)
                    last = today
            if last != today:
                try:
                    acc = _executor.get_account_summary()
                    with _state_lock:
                        prev = _journal_day(last)
                        prev["end_total"] = round(acc["usdt_balance"], 2)
                        newd = _journal_day(today)
                        newd["start_total"] = round(acc["usdt_balance"], 2)
                        save_state(_state)
                except Exception as e:  # noqa: BLE001
                    log.warning("0시 잔액 기록 실패: %s", e)
                with _state_lock:
                    text = format_day_summary(last)
                    _state["journal_last_day"] = today
                    save_state(_state)
                notify("📒 하루 정산 (OKX)", text)
        except Exception as e:  # noqa: BLE001
            log.warning("하루 정산 오류: %s", e)
        time.sleep(60)


# ----------------------------------------------------------------------------
# 실시간 포지션 페이지
# ----------------------------------------------------------------------------

_pos_cache = {"t": 0.0, "data": None}
_pos_cache_lock = threading.Lock()
_acct_cache = {"t": 0.0, "data": None}
_algo_cache: dict = {}   # inst_id -> (time, tp, sl)


def _tpsl_of(inst_id: str, side: str) -> tuple:
    """OKX에 걸려 있는 익절가·손절가 (수동으로 건 것 포함). 15초 캐시."""
    now = time.time()
    c = _algo_cache.get(inst_id)
    if c and now - c[0] < 15:
        return c[1], c[2]
    tp = sl = None
    try:
        algos = _executor.pending_tpsl(inst_id)
        tps = [float(a["tpTriggerPx"]) for a in algos if a.get("tpTriggerPx")]
        sls = [float(a["slTriggerPx"]) for a in algos if a.get("slTriggerPx")]
        if tps:
            tp = max(tps) if side == "L" else min(tps)
        if sls:
            sl = max(sls) if side == "L" else min(sls)
    except Exception:  # noqa: BLE001
        pass
    _algo_cache[inst_id] = (now, tp, sl)
    return tp, sl


def positions_snapshot() -> dict:
    """OKX 포지션을 2초 캐시해서 돌려줌 (여러 화면에서 열어도 OKX 호출이 몰리지 않게)."""
    now = time.time()
    with _pos_cache_lock:
        if _pos_cache["data"] is not None and now - _pos_cache["t"] < 2.0:
            return _pos_cache["data"]
    raw = _executor.get_open_positions()
    acct = None
    with _pos_cache_lock:
        if _acct_cache["data"] is not None and now - _acct_cache["t"] < 10.0:
            acct = _acct_cache["data"]
    if acct is None:
        try:
            acct = _executor.get_account_summary()
            with _pos_cache_lock:
                _acct_cache.update(t=now, data=acct)
        except Exception:  # noqa: BLE001
            acct = None
    with _state_lock:
        st_pos = json.loads(json.dumps(_state.get("positions", {})))

    def f(x):
        try:
            return float(x)
        except (TypeError, ValueError):
            return None

    items = []
    for p in raw:
        inst = p.get("instId", "")
        pos = f(p.get("pos")) or 0.0
        ents = st_pos.get(inst) or []
        e = ents[0] if ents else {}
        is_bot = bool(e.get("tp_px")) and not e.get("manual")
        items.append({
            "inst": inst.replace("-USDT-SWAP", ""),
            "side": "L" if pos > 0 else "S",
            "sz": abs(pos),
            "avg": f(p.get("avgPx")),
            "mark": f(p.get("markPx")) or f(p.get("last")),
            "upl": f(p.get("upl")) or 0.0,
            "roe": (f(p.get("uplRatio")) or 0.0) * 100,
            "lever": f(p.get("lever")),
            "liq": f(p.get("liqPx")),
            "margin": f(p.get("imr")) or f(p.get("margin")),
            "notional": f(p.get("notionalUsd")),
            "bot": is_bot,
            "src": e.get("source") if is_bot else "수동",
            "tp": None,
            "sl": None,
            "be": bool(e.get("be_done")),
            "partial": bool(e.get("partial_done")),
            "step": bool(e.get("step_locked")),
            "step_ok": bool(is_bot and e.get("tp_px") and f(p.get("avgPx"))
                            and abs(e["tp_px"] - f(p.get("avgPx"))) / f(p.get("avgPx")) > STEP_TRIGGER_PCT + 0.002),
            "opened": e.get("opened_at"),
        })
    # 익절가·손절가: OKX에 걸린 주문 기준 (봇·수동 모두). 봇은 기억한 익절가를 우선
    for it, p in zip(items, raw):
        okx_tp, okx_sl = _tpsl_of(p.get("instId", ""), it["side"])
        bot_tp = (st_pos.get(p.get("instId")) or [{}])[0].get("tp_px") if it["bot"] else None
        it["tp"] = bot_tp or okx_tp
        it["sl"] = okx_sl
        if it["avg"] and it["mark"]:
            mv = (it["mark"] - it["avg"]) / it["avg"] * 100
            it["move"] = mv if it["side"] == "L" else -mv
        else:
            it["move"] = None
    items.sort(key=lambda x: -abs(x["upl"]))
    data = {
        "t": int(now * 1000),
        "items": items,
        "upl_total": round(sum(x["upl"] for x in items), 2),
        "upl_bot": round(sum(x["upl"] for x in items if x["bot"]), 2),
        "eq": acct["usdt_balance"] if acct else None,
    }
    with _pos_cache_lock:
        _pos_cache.update(t=now, data=data)
    return data


def render_positions_html() -> bytes:
    page = """<!doctype html><html lang="ko"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="theme-color" content="#ffffff"><title>통합 문서1</title>
<style>
*{box-sizing:border-box}
body{margin:0;background:#fff;color:#222;font:13px/1.3 "Malgun Gothic","맑은 고딕","Apple SD Gothic Neo","Segoe UI",sans-serif}
.bar{display:flex;align-items:center;gap:14px;padding:6px 10px;background:#f3f3f3;border-bottom:1px solid #d6d6d6;font-size:12px;color:#444;white-space:nowrap;overflow:hidden}
.bar b{font-weight:600;color:#222}
.menu span{margin-right:14px}
.fx{display:flex;align-items:center;border-bottom:1px solid #d6d6d6;font-size:12px;height:26px}
.fx .nm{width:64px;border-right:1px solid #d6d6d6;height:100%;display:flex;align-items:center;justify-content:center;color:#333}
.fx .ic{padding:0 8px;color:#888;font-style:italic;border-right:1px solid #e3e3e3;height:100%;display:flex;align-items:center}
.fx .val{padding:0 8px;color:#222;overflow:hidden;white-space:nowrap;text-overflow:ellipsis}
.grid{overflow:auto;-webkit-overflow-scrolling:touch;height:calc(100vh - 26px - 31px - 30px)}
table{border-collapse:collapse;table-layout:fixed;font-variant-numeric:tabular-nums}
th,td{border:1px solid #e1e1e1;height:22px;padding:0 6px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
thead th{background:#f3f3f3;color:#555;font-weight:400;text-align:center;position:sticky;top:0;z-index:2;border-color:#d6d6d6}
td.rn,th.rn{background:#f3f3f3;color:#555;text-align:center;width:36px;position:sticky;left:0;z-index:1;border-color:#d6d6d6}
thead th.rn{z-index:3}
td.c1{position:sticky;left:36px;background:#fff;z-index:1}
.n{text-align:right} .c{text-align:center}
.neg{color:#c00000}
.h td{background:#f7f7f7;font-weight:600}
.lbl{color:#555}
.sel{outline:2px solid #217346;outline-offset:-2px}
.up{background:#e2efda!important;transition:background .1s} .dn{background:#fce4e4!important;transition:background .1s}
td{transition:background .8s}
.tabs{position:fixed;left:0;right:0;bottom:0;height:30px;background:#f3f3f3;border-top:1px solid #d6d6d6;display:flex;align-items:flex-end;padding-left:44px;font-size:12px}
.tabs a{padding:5px 14px;color:#444;text-decoration:none;border-right:1px solid #d6d6d6}
.tabs a.on{background:#fff;color:#217346;font-weight:600;border-bottom:2px solid #217346}
.st{margin-left:auto;padding:5px 10px;color:#777}
</style></head><body>
<div class="bar"><span class="menu"><span>파일</span><span>홈</span><span>삽입</span><span>수식</span><span>데이터</span><span>보기</span></span></div>
<div class="fx"><div class="nm" id="nm">A1</div><div class="ic">fx</div><div class="val" id="fxv">=SUM(B7:B30)</div></div>
<div class="grid"><table id="t">
<colgroup><col style="width:36px"><col style="width:126px"><col style="width:96px"><col style="width:76px"><col style="width:72px"><col style="width:66px"><col style="width:52px"><col style="width:92px"><col style="width:84px"><col style="width:84px"><col style="width:84px"><col style="width:84px"><col style="width:72px"><col style="width:110px"></colgroup>
<thead><tr><th class="rn"></th><th>A</th><th>B</th><th>C</th><th>D</th><th>E</th><th>F</th><th>G</th><th>H</th><th>I</th><th>J</th><th>K</th><th>L</th><th>M</th></tr></thead>
<tbody id="tb"></tbody></table></div>
<div class="tabs"><a class="on" href="#">Sheet1</a><a href="REPORT_URL">Sheet2</a><span class="st" id="st">준비</span></div>
<script>
const DATA_URL="DATA_PATH";
let last=0, prev={};
const num=(v,d=2)=>v==null?"":(v<0?"-":"")+Math.abs(Number(v)).toLocaleString("ko-KR",{minimumFractionDigits:d,maximumFractionDigits:d});
const sgn=(v,d=2)=>v==null?"":(v>0?"+":"")+num(v,d);
const px=v=>v==null?"":(Math.abs(v)>=100?num(v,2):String(Number(Number(v).toPrecision(5))));
const ng=v=>v<0?" neg":"";
function row(i,cells,cls=""){return `<tr class="${cls}"><td class="rn">${i}</td>${cells.join("")}</tr>`}
function td(v,c=""){return `<td class="${c}">${v}</td>`}
function render(d){
  const r=[];let i=1;
  const E8=Array(11).fill(td(""));
  r.push(row(i++,[td("미실현 합계(USDT)","lbl c1"),td(sgn(d.upl_total),"n"+ng(d.upl_total)),...E8]));
  r.push(row(i++,[td("자동매매(USDT)","lbl c1"),td(sgn(d.upl_bot),"n"+ng(d.upl_bot)),...E8]));
  r.push(row(i++,[td("잔고(USDT)","lbl c1"),td(d.eq==null?"":num(d.eq),"n"),...E8]));
  r.push(row(i++,[td("건수","lbl c1"),td(String(d.items.length),"n"),...E8]));
  r.push(row(i++,Array(13).fill(td(""))));
  r.push(row(i++,["종목","미실현(USDT)","수익률(%)","가격변동(%)","익절진행(%)","구분","출처","진입가","현재가","익절가","손절가","증거금","상태"].map((h,k)=>td(h,(k?"":"c1 ")+"c")),"h"));
  d.items.forEach(p=>{
    let prog="";
    if(p.tp&&p.avg&&p.mark){const m=p.side==="L"?(p.mark-p.avg):(p.avg-p.mark);prog=(m/Math.abs(p.tp-p.avg)*100).toFixed(0);}
    const stt=p.bot?[p.be?"본절":"",p.partial?"분할":"",p.step?"확보":""].filter(Boolean).join("/"):"";
    r.push(row(i++,[
      td(p.inst,"c1"),
      `<td class="n${ng(p.upl)}" data-k="${p.inst}">${sgn(p.upl)}</td>`,
      td(sgn(p.roe),"n"+ng(p.roe)),
      td(p.move==null?"":sgn(p.move),"n"+ng(p.move||0)),
      td(prog===""?"익절 미설정":prog,(prog===""?"c lbl":"n"+ng(Number(prog)||0))),
      td(p.side==="L"?"매수":"매도","c"),td(p.bot?(p.src||"자동"):"수동","c"),
      td(px(p.avg),"n"),td(px(p.mark),"n"),td(px(p.tp),"n"),td(px(p.sl),"n"),
      td(p.margin==null?"":num(p.margin,1),"n"),td(stt,"c")
    ]));
  });
  while(i<30){r.push(row(i++,Array(13).fill(td(""))));}
  document.getElementById("tb").innerHTML=r.join("");
  document.querySelectorAll("td[data-k]").forEach(el=>{
    const k=el.dataset.k, v=d.items.find(x=>x.inst===k).upl;
    if(prev[k]!==undefined&&prev[k]!==v){el.classList.add(v>prev[k]?"up":"dn");setTimeout(()=>el.classList.remove("up","dn"),600);}
    prev[k]=v;
  });
}
async function tick(){
  try{const r=await fetch(DATA_URL,{cache:"no-store"});if(!r.ok)throw 0;const d=await r.json();last=d.t;render(d);}
  catch(e){document.getElementById("st").textContent="연결 끊김";}
}
setInterval(()=>{const s=last?Math.round((Date.now()-last)/1000):null;document.getElementById("st").textContent=s==null?"준비":(s<=5?"준비":"계산 중... ("+s+"초)");},1000);
document.getElementById("tb").addEventListener("click",e=>{
  const c=e.target.closest("td");if(!c||c.classList.contains("rn"))return;
  document.querySelectorAll(".sel").forEach(x=>x.classList.remove("sel"));c.classList.add("sel");
  const tr=c.parentElement,ci=[...tr.children].indexOf(c),ri=tr.firstElementChild.textContent;
  document.getElementById("nm").textContent=String.fromCharCode(64+ci)+ri;
  document.getElementById("fxv").textContent=c.textContent;
});
tick();setInterval(tick,3000);
</script></body></html>"""
    page = (page.replace("DATA_PATH", POSITIONS_PATH + "/data")
                .replace("REPORT_URL", REPORT_PATH))
    return page.encode("utf-8")


# 매매 기록지 아이콘 (🍀 네잎클로버, 브라우저 탭·휴대폰 홈 화면용 PNG)
REPORT_ICON_180 = base64.b64decode("iVBORw0KGgoAAAANSUhEUgAAALQAAAC0CAYAAAA9zQYyAABGHUlEQVR4Xu29WZBc53Um+N0999pX7AsJEiABkiK4ipLcorW21W7J6ojuh+4X2xETs0RMTExEz8S8zNM8zdt4IqY7Yh48stsOy+5ZLFnyIlnWQlEkAZIAAZAEiKVQQO1r7neb+M5/b1ZWoZbMqsxayPwUJQDFqsyb937/+c9/znfO0bBP8EnpWrhPLqWDbeBk8qy2jV9rOfbsIjoE/nRjrwi+q4TukPizid0kd9sJ3SFxB/VoN7nbRugOkTvYDO0idssJ3SFyB82g1cTWm3nzrdAhcwfNotWcaYmFbvVFdfDZRCus9Y4tdIfMHbQKreDSjgjdigvooIN67JRT23I5dvqmHXTQCLbjgjRtoTtk7mC3sB2uNUXo7bxBBx3sBM1yrmFCN/vCHXTQKjTDvYYJ3UEHBwENEbqZFdJBB+1AoxzcMsrR6AvtVwSBD03XoNWt3YkHk5ifWcDi0hzmFydhGhb6+0cxODiEkcPD0PV4nYcIwkB+V9O2vFUth7x3CLl+RI9qamIaV9//NcqVPGZL9zCVvw3LTEIPQ/jw0G0fQdY6hL7+UVy48Dl093TJdcl90Pbmc7QSW0U+Nn1KB5nMvjxAQNcMuZ9X3rmKsfnLKJq3UaguwHVd+J6HqlcRshiGjWTKRm+6D136YSS1k3j++ddgmOr3SQj+3ArZ2we1COWq5E1KxTIuv/9TVOwPEOgLKJSW4XkePL+Msl9CpRpgcbkMPwhhG0kYWgJ2wkbKyaFPexpnDr+G00+clNfyfQ+GYbbv4ncBm5H6U0foMAxpV2tEfu/Kr3Hz4RuYXLyFqYXbyI26cNIGAlo0P4Sha0g6JtJJC5atQ/M0LD/0YWEIRw6dQTI4jaNDL2JoZFAeVUhit8nSybWHPnRdEe7j6x8hr7+L+fxdjE9eR24kj1yfCd/jAgsR+gAvx/V8FEouJudK8MMAlqVDtzR5vZmPgeOHzmIkcwHnT34Fo0dGdnVxtgPbIvRBtM58gLFrsLiwhI/u/RpvXP0rFMybyPSbKC8H8H0DgRuChjfhmEglTCQdA7mUA0034AcuQi1AMmvAcnTcvhzicO8reOzYazgychaWbZHWCOkKtNANCYKgZv3n5+YwvfABrt74GYqJdzB6KonScoBqCQhDXS0qdRXQwhC6rsnCnF0uY2ahDNcNoek6dE2DZvjIDhiY+sjD6e6v40svfAeHDh+Ldp2V9zxo2IjU61rog0hm5RaoBzQ3N4dfvPn/4sr0nyDZp8GrGPDdAKFOfxgwDA2ZpIXeXEJIzd8LgrpHGmristJdMawQdhpYuN2Do5nfxYVnX0YmnVOEqltArcLs7CQuX/sBxpb/Pwwdc1CthPCrOhB6CElQOtXrgAvMMnXMLZcxTUsdxD+nAYEBOxugOO9jMHgRv/eN/wa9vYMI6aO3abfZDaxH6k8NoekzG7qBifFJ/P2bf4oH+o8QBqFszyQBHy8/LC3ycF8KtmWIy9GYkdXgJDUsL2gwF57FN778XyCdziHwPeg79EfrF8XVy1fx0cz3EeSuiXUl4ZpBTOqFfAUTs4XVixQaTBtwi0B39Xl89xv/NQYGRg60T70eoR8J2x1U68xAAMlx7e4/YqzyY2h6KIRWW7NCPZn5zcbITL8Z8Kohsr0h/O7L+NFP/g/Mzk4JmT3XbYZzq8Aohrq6EFcvXcWtpf8L9vCH0HX1PdkpmgA/D33rVMJCTy4R7SLqBUh23weslIal1Dt49+obqJQr0A3lax9ErMfVhuLQ+xnxw9A0A+9/8Abe+fAHSPQE8Mq6WCiSg7TIJk0M9SrLzIe+siVvDS4Otwq4pRCZ7hDVzNv45Vvfw/j9OzAtKzpkNQ8SkFv+3Mw8bs5/H2H2NnSDhz1dfa4N3IvNwM9lGhqyPOSaem0L5i4VeGphmkng6tRf4ZPxS1Ek5WASej2sIvRBs84xmeU0PzWLd2/9LarJB/BKBqAxWgB4foiUY6K/J4mEbYqbQTRqnWPopoqKVEohcgMa8vavcPXDv8PS4jJ0XYXXmrF04r9CR9ldxtsf/Snc9FVooYbCQgBozbkaa8G1YJo6smlLwn/cqCSSzQUShnBLGsz+abz34T9iamKq2Y1gX2EtZw+0heZhjpEGfr31zs8wmb+GdK8Fz1txNUjcXMZGOmHD9fjz23weNRclRGkpwMARG3nzLVx+7x+afkESny5SpVzGlWs/RTn9T7AMHb4bysLZCfj51OtryKUdmAYPlBGjZSXThQrglnXcfngFV2+8CT2iQTMLcr/iQBOa1oegL/qg9BtUwjkJzfGBicUMgO6MI2E5z2cEpDWPQTNCLM0CXUeWsWT/HW7euBlZ/cb8UVrnEDo+vvUurt78GyDQJS4uV70zPtfARW6bOtJJU6I6taBHZKmrpQB+agqL+q26X2rN/dlL1B7xQXQ34izgnVu3kdfuId1nQA818XkJ+pJdGTsKzbWIKRFCeKgUQyyXJnDlk7+E7zPjGJ2+tgBdlIX5RUwuv4PhswvwvTiu3bprjK1tLmvDtg0E9REd+u6hhtygiaXCuFyLMt6NLcj9hnrutshm7T5iK8y08I0b76BUzYtViuPJ3HoZ1bBMQ3bcrVUrzYH+aLkQINNjoJq8gqvvXYZbdWXXiK9tLVa29BC3bl7Bg6kPJJTm78xl3hQp24S5zs4h8RVfw9ziBK5eeWflPNKqLWKPcGAJHagNGlWvgFuzb8APq3DLKnnCKAbRlaEPqSnr1IYbzLAgfVUrU8W1uz9AsbwAgO6DyuStxYr/rmEhuIzUwAIKc+qg1i7Q6jIVTrejHswwuhUfy6U5jE1dqS34dtyn3YQQ+qC5G4QROcSlyhKWrZswnQB+VfmgJA4PQ8mEKSnhdtGF1phRD2aig67rmF24K9em8yC2Bso6K7o8vP8QrjmG/iM6/IAKuHZdoYpwJGxDhSvr3iaMwnihUUFZn1kVMTqIiDl8IC10nF3jn5MTD2A4ZTByRpeDWya1DXQ3lNin9e7GKkunAUwWdg+a+OT2VSwvLUtsd23EIN7KGZm59sFvMD87h+KyhzD02syfUNwuy1ztH/O+hIEGO6nBNZagxyfsA44DR2gShaSgtSvmi7j/4J4ibS0jpgjt2IY65FDA08aHRKvHa/LcAPenL+H++Mfybo+mrWPzGGLJvwEXC3ArSlzUTvDleSg0o7NEfC/UrqAjmdPhW/O1G7jtsOY+wb4ltCKuD993RVIZM5ZW2DCYyNBQLJUwPTemksdiiZVFpjvCbVbFZNt7p0UnEgC+q2HgiRlU7U/kDdcSI/YqGOGwB+6h7xAFUzo51VYIocVCR7tG/eqObg7j4R9ev44g8BDAh+tWRafCf1M/Hfi+PAtlSPY3zP3mPzOmTHkkRehMZyMSuRPMBt67dwueV4VjpTExdwsz1WuAye1ztfaBVno3QVJnejTMTdzH3Mwcevt7I0sdZSaj6xkbu4NAK8G2dVQKu3ONXDN8p7WLm4dncrRareDmRzdw5smzcs0GFbIbIKDqj8lM/k/fXxUw5PK+Kl2gFZA0cnSound7DEvV+1h2J7G0NI/5hVlMTt8Wy2HqDlx9CWXroVBedPd1x792W+ZHoIcoLAZYeDCGnHcTvf0v1H6Elo27iud6uPXxNVRsH0aSll2Y0XbE5wpGfFZBC+BVNfio4F755/jV1QCpZAqal4CFjOyKhpaEpVNmm5UiB8M062wMS9T8PStRWw/7gtDqkEchESWdPmbnHmJ86hO89/4vcXf5bSSHlpHI6PCpoBtQloa7NYX6RqXOp9gFcmxsuij8CeCbkyiEtwGsEDp2P0rFEgqlGQT29hV624FyOzRJMFWqq0OKXiWEYfoopa7hrYfXRTe+/FCD6fWIpsTWupGyu5FLDuHoodM4duIkUk4XHKMLXd1dteRWO7Th28G+ILREJ8Rn9nD53Tfw00t/DAzdBVJ8EPRPgcKcsmZrJcL75hDDMJhroutQFdDu155FvR/PMtayNwstjGLlbQzXxRBJKcVKhi6p8HJF1VrW/3cSvpynUVGaDzvHv8/Kj/jaPPIawNjN5Ozf4o2JEPryIA4lXsJrr3wThw4diWoylUBrr7GnhF6RfmqSZfvBz/8Id4v/CC9bhhFJhZWuObpNTWiYdwPil9a9ERM4mYyJ8sJ8nR+9Ei4LUEUleAALPnwvOrFuc1dZ+96bgfeZ6juH1qFQlbjP2retxcLjexz9gCI/BWBKa02P0EtOYgw/xF+88TMMJ17C55/6Lo6dOrovahX3jNDqxKzu3pXLV3Bl6vuYKl9CYFShO3QnVMhN3cxIPVcXmlsbX5ZDSsQRCn124kM/+rgfTQjzO1SiiqtUowcPtAaWlxZw++bH6Ol7Iao7jGnvw9OXYRlqp1HEWlkSzH4a0KXyJn5HL6ofVO+hWObzfUKWiMXvHd+r9SGVLEw0MXxnaHCpHYkZHcXpmfGMoaTY6spq95EnSzHgmpSlmTYjIIsYK/8DfnjpDh67+1t4/Z99W13fHlaW7xmheYjSYWB6cgZv3PhTLGUuwXQ0uEt8mCzjlycencRVbJlWhuDD4b/rSev6fMghbEsX/TPF7c0itnpe6K+yvCSTFJzy8MnorQY4mgVL0+GFASo8+fNawUKAAFU3j6nyTYTB89AMfp5oizF8OD15mLZWKw0jYko7uoVeK4W0YUfVLMCcW8KyX5F/s6Kb75M1HZiaLu9bCfjeAYwtEiP8vYRjYKAnicV8VRZ9bAT4d5JcroUxdZ8GgXptZSR4ryNDrVxDT5Mv3WCtoo+y9hHe+mQKlmPjped/G47jSKiP/323sSeE5s2iUq5YzuNX7/3fmNXeguVbqJRZdRSRw1ck5kNgXNk0NTg0baBfrUelQyu3q+rSL2U0QRe5qLVGMrkV+MD8SEecMmwYkcXi96uhj0pkKUmcHiuBnJGsEboQVDBTLYKcYMjc9Utwg/m6CIayfpruId3NuDpQjauvInDBDFgZDDkZ2LTQ0WpNGhbulhaQ9ytC9IRuos9KiRUvBy6KfhUFv4oSDxqRYm4tlB/N+6mjO5sQwyBhTtGSq5BnxVWLjm6F5wXwoqoe+bfPannlX8vClh1TJbgqyzpsR4c1PI9ffPDHcKwknj3/eViOytS2sjK+EewJodW25OPyB/+ES+N/hkQ2qsqOQsk0NrRAyYQhAqN0wlJx5djlWEedoSUVadQ2yXBSIx9/BZI30zR0mQn022k4URUKv7foVTBdzaPq+8iYDkadHFKaBU/CWjp6kZTFMFcpiaUzHR+hqySZ6prii+FZQaXK68ErT4l1VouEVjd2e3KGgx4rKfdjyM7I35V2OkSX4QA2r6+IT4rzcBn2XLlNjyC+L7yfa5Gt86rjIoGy68shslB2Ua54ogqUfiD1agI9kMp0eEDy8ALeuPbn0ujm4sVXo65T2zwkbBO7TmjVWkvD9Q8+wOWr/4DsgA63rBLU/H9axkzaVDpmy6qdyGMF3UbYqeyRJBlNZDHkZMWPXSEjMGTbQrh5r4Qu04GlGYiDX3QD+MiOJLpQ9j0suR76Rix4xfu1mkC9bgHWC5FkV+Bnho604cjiIVFlq48uwA0Dsch9QnZDuR3Rf5PfDYG07mDQzmCqmhdS8x5utJ7XS7CsXnQrPhAzjPzKpmz4QSDEXlyuolxVLlmNqtSfM5Ra0JEYHcONyR/jxNQT6B/s2yYtt4/mHc0dghaE29C95V/C67+B0KXmQllsx9Ix2JvEQHcKSdsSpVy713e8ELqtJHrNFJyoa1GM2O5zux+2s8gYTk0jUg9LM5EyLVjMnjGjrdNabu1Dxoe7lGEJEZVvuxq02nz9Oq4JlE+vJKzKr1YLopXZGhFf6ZqkzrvSjrSA4K4p55uolKy2+EPq0QPcfPAbXPnwZztkyvaw64Tmzb596xbuPrwCOxdIlx/6Z11ZR8icS6tqZYLb+EaWphVQFRrq5D7sZMR39oIVCxiD10HQt12JaKxGbSMOlP7ac4GJyYeKeBvWfsXiKU0WDN2X9T6x8lg3vxdxDKTVBoAfXZ5D5A8zOdObczDYl5TnRBcrDpCEmo9yXkN2JMB4/hLyS/lWPKamsCeE/vDW25iaHVMVzvDl4McuRtm0I4SvVWY39VG2h9ie8fAlzV3WUefF17HVAqMllYCbBniei4kHD+SijAYsNd2JnexH/F0uRS8yAq28d/Frxf0Aqa0mqfu6EhJVqncHGZxKdZvIe1O49sGV7T2UHWAPCA0U7XFYPSVJFTOCwRvDCAaJLARr5dPYAqq1I2PKW+8FG11WfBBN6ba4BnzwBEVW9cL+zbCTvYjvxlAjq7fpMnEXaeTzNAvZBaKqcgZ9erIOersTtZ2OYCy9WgxQKOZx45M3m32LHWPXCe17PkrhQ+QGDRgwkcuYcuhQ6rj2apfXgzqA7cQ2roALYyfEbBZxZIYLqOi76DaTOJLoloNr2yHt/zRkEha6c/ZKil+jVIE7RQELXl1F+S5h16McH12/iXKpBNcOkLRtDPUklTVrwEK2Clw6TIjQZ+430/KytG7bPVCppIOGYlBFNfDBY2OjWNnOVWuDtQe6zY54cigMVWRogB0lJQEEdFsOEoaJ+2VWoqhs4tb7T3OI4/bifmRV27HFvCuHQresITRKKCZUscNuYtcJXSqV4HsBkmkTDg9ChiaZqd0EPXf6zAN2RkJiDCVKyGydCMNmWIkuU1GpoeS5qAYeklFEYmuoxAPfl7HuHvrgtdCdrBIVgmvgcGzVujcBSd1An51GKfCw6JVUNKINpBZDhFDcRZ6BimUP5QoPkCr5oid2vyBg110O27IQMmmSNCRFvdtkJujn9VlpDDpp2LoOh8UEW7OvBjk4MpzFjp6Rwz/tFmrZumYQH+YWvbIih27IAZFffG26EtUodr/ZsqfPLF8iHAhBT5ohRhK5XbSKY9pMYjFe3ZW1JbwnyRdGR1i0vMvYdQvtsQVmGEj61QoZE2h3keijYHKCmTeVlaNAvTEfWnn5wEy1gIRhIa2rhEMxrOJBZQmV0JfXbdSPrncnSkEVs24B1cCJ5LRMubuYrZYwaGeRtq3oWhXWkrt+QdJKMYspOg9xp9oHdU9UZpbx6XLZF62ISqm37303wq4T2jRUfRu3KSvQUZH+zbv3wXnzTRjysKl/MBsIqcUg7Umy8fKSRBN6rJToKQr0ndmIOibbNjwo+t73SgsS6+aOwXh4ifV8CJA1bLihXSPyZn61Olgr0RRFTSqT2Xofei34CBlHp1yhWNFV722mMXcZu07okcMjSMwlRCiz2x83fr9+K420aSmfOYo9bwYaGm7/FOzMuWU5t1EQpCxgvVJja2xGdrYSoNtQZFYm0pYwsj3pFpivEVGUxJnFT2ZHpBWZaf2ic0NfxExcsPUWut33m3fCMk1YBgcauQ3ue63FrhO6p68b2S4bZlJHtaTUXu0GLZQf+rB0E6OJHLqNhBwC40TKehDdb6SJsFmAEAQiUJqsLis9CsNTkXfamMOiqtKdBK2XkoGu/ejxv2MLHP+b1nuqksdctSAHxS4rCcfO1KpR6l9HfVa111PIRB96wS2hFLiR4Kp9N5wS94xjwe3yUbhvIBEOtfvRPoJdJzQtcyo4iqkHN5FO+xwdsiukji0VNQ+UYCo13vrernItPPFf40QCrV3eU2E5fq9hEtch9EwsTSZgZwsqqhKsPzNlPaJTdFSSAgDqNqLu/JEvvfbnSeKskRDBE6+020pgya2IC8JdpZ0wLQMZk7oWG93e4+18q3Wx64QmUu4ZVGbeQk9/AdVKfNRqP0gAEtMhLSLru569Uqf3EMteGcXAFdkofVke+DZTsq3Fo7F1huCUP6t0wo07AVwAttBZWWD+Ng+1Ik+q82NUBEZDgqHDSEqaNW30mCk5uN4vL2xZDLAThD6HLOnIpFIYMc7s5KW2hXYegDfE6PBJ9PeOSufN7Vi65qEeMo9YS15F/qwvOVplRaN/8HBGBR617LxJjqZSyo1TUFWx10MzXeSGSrAdTUT1zfS0i60x0y/0jxe8IgpeVSz3etcUp/N5TuDB1dR1dFmUqDYehdkuSOpUohuPnbqw3ZfYNnad0FROsKCyv/cEluc8aGt7RbQByt1Q5oq+JA9NWxUd8ndqmowG1G7r4ZF2YCEF/sp/3okrS7fnTnEBn5TmkPdUedZ6EO1F9NlFLQcNSYm5t8ePlvCnHWLhXoDDmWdw+okTbXiam2PXCR2bk5R/FsX7h+Ck4mLMdt1kRUzqlIftHE4me5HUbTnObfSOKgSlDo3NQsjP1mC+i9m5MelfrVLarFRpjYfHq2JYTsJkhtmQC1HLam7jMzWKUDOQ7TPRnz2DU4e+2OivtRS7T2hmrgIfp089jTMnXsfSXFXq44xolmDroWSVjBsPOCmpPNlY06zKsCphgIeVPGYqBfFXVTSkMbBNrYyBCz3ML95HxS1K8oja4I9v3Fh5nR0mHajVyJkOkoaKT2+G+EBMK132VCivZZAEitoLUtkQE9dN9CdfxZFjnFa7ww+5Dew6oWMLkcqkcPaJV5Eofg6a6cOwNWhh6y8nFvDQA2Z0g+7G+rGNFcSCnnLoShq5KTsdsPKb8dgA1eQtSQNrMJEvLOGDD/9JnvFOex6SkPSJmYDh59qINrGrxDQ6dR0zXrHlslJGqTgj3UnrmL0P9FtfxuljL6kEfJt23c3QegY1AHVY4ri1HnzuzL+BXjitSOAoW7KdTFsj2EooGpOf0YNBOy3FspsRZj1IhbUXgobT6nqI8dk3MDX/Ccbn3kSQvqkKVenCN3LBm4CZRNYwcoGqIjaF+G+x76wOsiFm3CKmKwVxpZpaoFuYfiuhg2rVpUkNPeEX8eLnvoXBoQE5GLbTvdkI2l51H4372fERjN25j8v3/whB6pbM/Whl29Y4pkxV3alUX1ORCkYHbhXnJCtIK7eVZa+Hil+rQ6CbT8O0fWT6q6iWd0plBZ4LKH8ddrLSy2O9JcLrpa+95JUxVS1IVGQ754KNFq40sHE0FOccJIov4Jtf/UNYFnty7Hxk9HbRmlPKNhD3s+ODP3L8MAz7v8Klm/8RWt91uGULvuetnq+3baiqaiYUFtyytAqIFW71Fo2op9pOrZjaZULYCQ2WXZTXZwuDVoGWlj05JqrLct0pQ9lpaYQT1WMWfA/5oCwJIWY6W0JmFUSXBJluhVge68XhzDfxyld/W8jMRbTT+ec7wZ5Z6Bj1zUjm5sdx6YO/xu3pH+H4hQS8MqSHMqtcVAxKHbjisW2NQrkS1ECbGHG6RBNBt0L1elmhcay648+zucz9yiJmK8Xm/ejVtlrmI6pmlK3Niqr6R012j9iViCOC/JPWWVJCUZyw2UXKw57kbugLs5E8RWXpEExU3nmvjBP9X8PTZ34bXdlRJJLxbPG9cTVi7DmhxY5F7XTJ2qmJaYzPvI3pxeuYnP0ImUNz6Bu2UVjyZJ6fV+Gpmp1/ZONdWRgbJrKjcv9IPMGoACMdjBLwT+VKqJ9hay2SgD9KN2PRL4s8VBoFqf+LG7w1hfhw1HAiJcqihFuE2OJco1TaSMWL0tWpK1W+Mn3o2Jdd5TJJ4cDKx1gtoVWtGNiOjf6xYWpI50zMTlSRH+/FUN/jGOw+i9G+z2FweEBehH2iG2nb0G7sC0LHpGY4j537Cfa8u/XJu/Ay1+GFM5ianEI1nIfhuOgesGBYbBew4ihI80PV72SNfVTfi60Tw3BUtDFKwF4YtmbWLB2TLqp/HLXEfpRa5g6hyvj5QpRC1LoySSXJ+nqM7UBVeqjeeYajCZE2SpDH35c/GTnhNW7wpuv9F1YK1Se1VA87vgB71qm6wIVpF36F96gHg0ODMLV+mPkncerkMxgY6pd3Y7ydkxboguwH7BtCx5CxwdKHbSVtzFEU165dwlLlJgJ7ClbXLDSTk1zZB0/1MPL8qmrnusW+qiKmyo4pjq52OeSRRuKjWBrKSVXMcPL7TkoXoslSYv83jnRrUQmZbmgwLbWAygU2kLFUx89N2ntFF4JACiUaTUHSLbBENx2DpDR1dqoykUgaCAML7mIf9Oogcs5pnD373KpOSLzXas76/iBy7XPsVZRjO4hdExEOLecxMf4AxeKyvBSzcsXyfG27bRX8kCVQD+EGeRGs67kJWMmq8otVg9TWIYDEcwuzJoK5k8jYJ7jvqw6QG6xU3gs3XJK+07LoSNJNFrXsNJSxasOw9d5aGtyyUhjoPQrHyWBoeAj9g8qVkOXfxuxiq7GvCV3vW2+EWGlWKVfgeWxy2FooK+2pWSLiV7oolguYmZjGnXtXMVX4DdKj89J3WXzSRo1kBLoZ0VAv8U8fO/xVPPH4RYSeBVNP1dx2ZiDXiyArgjL9w6hQzMGNSRjvSLT+eriyC2q6gUTS2cJ1iGeSt/outw57FrZrBLXDjPiqaoSwupfxA1t5cPEpezeQTQFDvafR33MShcrzmFi4jsnKD2AnPFQkzty43ZbGBeyFZ2joNp7BxQvfkmjCXkMJq+LBpVFKKmq/u5+xrwkdQ24kbW9kGFQITEU4lIVm7FPaku9MxtYkhkZYkTGE5P0RTN3/MaxEgCp7XDdR+CsiKR7qWOuYm8bVj36GlDUAAwlkcz1Ip1NwPQ+Lc4twPRYc1Pm9USWOQZ3K4KDcJ9uxYdkbz2UL4Ur/Z3VHlXuycm/VDa73jfexMV4XB4LQMXHjm6tu+PpWTKWWAxQKRclYbRgm2CF4CIVRhRcWcWv8khzKRBrahHVW5FHxabrJWu4K3r19E3pxBEmnG5nUANKpbnmvxaVJVNz8areDsXRqnU0Hw1OnAM1AMpnE4MgwMukMAteSEKfO0WyGg2QqCdNiM8xHP7yyyAfLX14P+9qH3ggxacWvlfhwgJmZWUw+fCBteV2vjJm5u/CiXhctVC9EJNRR9hZRwQT0zCRyQy7cSiBCnZ2oY+hP6xzVwZCatB2OQi7xTrSJJxMP9mTkRdLReR/F2S5olSQS+jGkrRH0do/g6LHH0E9rrgZtwFyP3QcY+5rQyndmuCzaHiNcffcKHk59jFJ1Ep7zAHYfT/ghqlVPmovLUNnARdCu/VICBTK6B5YN6KYmcdtWQA6e9b7qRoHotYg8sjiBJI1e3FAsPyvH2RaH5NVgwC/0AaUhZM1TGB16EqceP7HqDCLtK6WiZn9Nim0E+5LQQmTqkCVYr/y6q+9ew/TyJQRdH6FSXcTyUh5BUEZoltEzpDr912SZ0UD5taq9yEN85L406yYoi6mSGYwZs8cAoxCtQL3ksj7CK8mcjYIL0UQsLoYeIym9pl0EYLFZCVVUNU+6vLKfMwlfWPBQLeow9QzS6S7YVhJGdRip4Ck8ceZZ9PT11D4KZ0dKsmVNOdl+xb4jdG08ctTV//rHb2CxcgPT03ewUL6N0TOBJDaq5UAyheK3uhyys7pRuSoWrb/t0XDPaN+uz7SJ/Y9+uGFyR0N3lFanNWTeDtTnUFfNgUODFocOmZLxrPgByoGHMqtn/CLyrosERUycYWPzi4dIHX4QYvpeBXp5FCMjJ5GxDiOJMzh16kyd5VbDQvc7sfcNodfGnO+P3cTYw3dxZ/4fkBmdRTJlil/oVQ3R2qq4QCS+34JQsc6DAh5qN8TC1mUMWWiqelmoXhyN7vL7AUphpxbUufQQcmZCWpKJjoOquKhiZ6aalyoc1iOqEeP0m6LIkMHP7cNKasj2mrh3rQQsn8bRkQs4eug8utJH0N3TJe+x32Z7P+J57bdMYaVcwt37H+DX7/4puk7eFwE5xxzIoHcGubYZ02cVN3tycMCOIoES7tATZr+KkleVfnAsOI1VbAcB/CxxVc3ZiNDsKaLS+wr804YmLcvulBdRoMJrDWIdCZV1PJQm0kpzPfVRCqO5L+HpJ76A/oFR2PYu9J7eAfYVoRcXlvDWle9j3viRGi4U9UbbSQULHwqJTCF8l8le1I+6B/wOOystexVMVgtSSd0S7fAuoN5Cn0n1S1cltgvbaN0veCXcKc1Lxcum07LimL+v9CsL93MYTX0NX/riv1Rt3PZYJroR9pTQcVKEp+l7t8dwffw/Iez9QHpIS6utqvIPtxus4DOhrvmQk5PO9huZ95oSjwcptt2qLmOykpceFtvcEGqQKVfMBEbpaJkx2OwQxQbBGsOjTre0AGNpVn24kouW/fn4+dj+gIt3s88WH04pfqSvXS4EMPU0kjiJC4f+ECOHh9XeEO6vSMieSaVikQzJvDC/iA/G/gzl9DuAXkHoGaJ7pm+8XTKvMIodhqgk09WM7HX+F/dUpseZMW3025lofJvasHdCaso0SxUPE3NF3J/KY365LK+6drTzTsEoRreZQELnLMP1dR8EBxixOfpWD54HXX4xN1UpsuhXQ6q7goL+Pi7f+Y+4f29MtXln0cVOttAWY6vP1T6I2EaX8v63rv4Fyqm34CR1LM0xBOY1XZWyGUjIjQeyRcUwUbSAWzGF/yOJnNycR4e8NQ4OgOdYYfZLnlkoYW6xjNnFshC82WkB9ahfYFygdB04mHPUzslkgo2umVa6HKgxyo1uEjGxPS9Efl61Q3OzV3Bl7M8wNXNPZZL2MMqzFntCaDVNljPuqvj1Oz/ErPY3siUX5jmru0411gIwSVEOPalA2epEGZOaD40jiVeqOpq00ZGGWboI5SvIF101vNLShRizSxVUXRYzNN9SmKRUo9vUmIl4oH2PmZTP6m7gP4uvHYYyMoNftQhRgxAJica5koBf1hD0vI033/9PWFicWqWr3mvsCaFVxAL4+O77eOfOn0sTdEmmtHilK79Rx6xbwsPqUlMquJ1YZrKHu3Ax72FhyUWVYqC6kqflQhVVVxUMNCn9ULuNxlHKNnJWAmlTjVSOO9xttvT437j7sHljM81zVu0Oukp6uUUNC8GbuPrJD0Qopgom9i4eH2PXxUn88IZhYPzeA9z48Bc4+TQXPn211pUyrQUtk7R7iRqKN4K4hwdJ0AzvuCal93Xehjl/App3BYlUAZ50WVULmX+j1XY4S9tWi7lRJE0LR5wuJHWlqIsj8lENzoa6Ff4cLbqpGxK6zGvulnPBNwQP7F6IwaM2xm+/hd/86iReePU1OUSrAUx7YicFu//OUQXyvdkruDn7c1gGKzLiR9NaSIw2DKXrppp2tTVxlCQzRCGoyNbM4fFSOFuXYdwM7PmcTFP0oyFnPQ1TS0ssvb69ESfn5vMulgvKFdnostRiUskRuhmMpR9NdIk7xNZmMr5CN4XcHPi5kQgr/tTx2DoefLm4tzvGjuC99MoajOwMZsNf1EjcpHPWcuw6oVmYubS4jLvT7yA9WkK5GN3uNt0JPjS2AONDb6TTmrKjgZCIob5RJycNw53IIm42oZVl/1S6FRY0uAtDcNlHTqPQp+65sRjV1KCXh6C7PbBZv7fOOlOxcZZX+bKgaPpZ1JszErLbqO+zkQz/VHWVG0EaT0Z7Dv/eClAVWC4A2T4dfuI+xsfGop1GSQz2CrtPaOgYu30XE9NjcJKq8Xg7wVdnkxUSoJmoMn3UI8luHE12Sy+PEScrrcFoEePQ36PQpCawupSBsXwWpUoeXlAR5ZryW9RnDfUQXcZjyJlHYdgshn30lejj8r1UQ0ZLFiQnb8X1uCs9RFY3IFgLXiub7EgLYYQS4ZitFutaiO2AfBr1NBoqxQLee/+XcKucfsW5i42YjvZg131oYi7/AIXyHOxSgDC5mYxsZ4j9RvaAYxssR+STqz3itY8z1ngQdDn482nDknHDtIjTel4OmOzqTyLW/z7XJvtY5LK96LaewJ3Jd9W877rny3dnoqW3axgpy8fS7I1Vs164o9iajqyVQEZ35ADHZAjnFbIrf7Qkmroxc1UOswhkYSy4FcxKR1QV7mvuldZAC+G5bGbD7ky34PoV2OBsxL3DnhB6sTKGojeDVMlCWXdhpepmRbcYjAhQq2FUGRmwaq5DI8uo3iflts9/00qTuBOVvKjY6knBQlOqLDPpbhwaOIJLd/4SrlEEXEX8+vfs6emBWU1iejqF3EhJ+dghp2C5SJkJHJfMptpTaJ0zBntax7q6xsGkUsGvYJqzFXVLkkuxb74jMkf9QDw3hGEF8JyHUt4l399hMmon2JPF5IWuVDq7XoB8QQ2xqRfTtBISr9U0GeNwqziLu+V56cQ575ZF19DMEJ049ttrJuFoRjQFK7KZbBKjB5h9UIWNIWnE4mkV1S9aNTaqgQdHtgoYGXwMhturmr4w9BaEkqHssdj1VI3AiKEGhTZePMuFzJ9nPz9KSHmH6Ws3LI9tABLCC4BESoeVm4FuxB9yp0tl+9gTC+3ZU+g9bKGcDyXpweycJbX87QHbGPJW5/2qvJ+aZuXJYe9wYuuG4fUgITgejq3EDH/FHvBvhhli7oEOIzEMM6HBtSdhW5p0VNV4OIwIaqeAXE8aaX8AuMEEjorl0S1IGwkZtBmPjFMWrznwGrlY59ySNHSknoUTDJoJPzYKZkO5Kxm2j4Bdd/YYe2KhVTsgFTOlVWJMlvHptT5pqxBv9TKokgkPvyoZNh66OAyoWfD12MpWxsPVxU4o4rG0LoTlbuQL83CNBWnkLiMpqB6Upo1AZcaBqSWQTDqwTOXCxOBustNIBKlL3fOD8pJM8oqjDs0ujEbAZcozr+dquHfvnnqOPDjvUaRjTwhtVocwd98FDF96xS3lqzLEnoKdttz1CLXtVgO67aRILbfzkPmwbM2Qr/i5MYDBSppcehjZTB8mHjwEgihpIiVlcRdSEjqHsOLASSaQSfZHrcda89FlB9FMOUxywW4tQ9oZJKpBo1SpYGFxQUV09jB0tzeEpqfj8QGrWrxy1UehzHG6LVDXNQiRce7AisSHvBh8sGwgOdB/WPpdT89M1nqFrbVW9JnZ7YgZ03QmV5OYtOphkNSMYTd/hGwOvH1U+XGXZZLo6LGT0iSH4yj2qnljq+5hU8iYh5A0+6LumuoSpuaKmF+uRJqApl5uW4h3+e28FYsBlKy0zlegTNXSMDw6IvNjpmbur3yWqCWB1JlqGnqTp2GE7LoPDA8fqomm6G4wxMgQ3WatF1RVjdKHEPHikiocNkIPqhJrFtd8p6G5TSBdyKJbUCy7SGcy8tPsi7JX2BNCP376PIYGjsFOs2BT3RGu8oWlMoplD7alLmsHBnRTkCw8+TPZQNF7vUa6kdAYNcU8aKlSJwrcVRP2seuA4fbBcz0sLc+qPMo6aX0tMGodS3NdOWmFEGOt5a//fhwJWvQq+KQ0j3ulBYlR8zOwgTu/6GIsumWZS060K21FfZnJYmXXw9RMEahmaqq7dj23RtD8iWiHoGUZPXwIgzdP4P3Jd5UGgAkJQ5MwHjXDEntNmDANVXYvYa86a7BTcLkwXMcHz1Syo6txDnEihqReW/FRDx7amHFjP2lxn2itdWB5ykBQyqBYKqJUXWQh32pEbbeymR4Z30Domo2lGbbRVdY77rofj+xYD9SX8Np5T3idSYm6sD0u9c4e5t1SbY5hqxGTlWRmUmW+VMbsrIsu7zR0KMHUXrkbxO4Tmg1MdODYwLP44OM3YR2eQEWKYNWhkL606xfRk3OQcti2iv0jWMOk+ti1avXzdRa9MszKEvrsVI3QajuHCH/YDH09cJhQyVci/dgM8hLTiV44VhYVt4CSPy/Jklr8WZqZq8Ad29amkmp7Dj0by1NJ5IaXRdBU8pR2m2KqjaAOftwlPMxWC3K9DCNyEVR8pXWWiM62HKqNoZqiK2fI9QPMLFUkYgTfREY7BlNrLgTaDuw6oeNmg4+feg73p1/HB/nvqQC9r0Qt9AFdL8TkbAlJu4pc1kE6wdayKvlQ62/HuxHtp82SXCyxWEMfU24eS35UFsUiA6bINROn032P7Ndxo3TGdzm+gqmPOHFD1yntjCCXG0ChOoVqsKxmwnBYfSTlUAzmVm1Bj+PuvgkzTCMMl6DJAcuXqmxeB8VIa1PrvEe8Xro8vB9xMpyxfIJ7DZdNK8i8VmYjAQzRPgNT8yUs5304WQ22ncTxgXOwIt9pO+eSVmHXfWjJiPkenISDx49ehP7wpFgxRghiBonegdbGDTAzX8L9iWVMzBZFGF9xffmiz71TYZPYmhByEOMXrSP1GlLVXHeH47+TJDxwTVUKkvaWItpoUXHX6e4aRrYrK6TcShNcI4tmQg+ykqDga9APLgauLDSVbl8NznwpeSyhUqn4tT73Tsi0avHU3lY9F66XQsnFg+kCPhlfklArEwd+NUBvZhCvfeF16XrKvh2cDLxX2HULrXwsfuAAx46cxm+98O/wo0v/K7z0ogoB+cGqekLGOKWdd8mV8F48yoNk5t9tyxALnk5aSuTTrLleBVXWxNfgYYtpaDI+apIkSYo7pQWZMKs0HKEQUTYLTcPwyGH5e9kroBQuwpHKFRUNUYtP9ezq6uqWtrfKojpwjH6E2k1Fcp1qtVD8YGLQzkjaW/nHPiaqEdGj998pYhJTl83PRFei7HqoVgMpE6PldylAYsezIJRWvGo6ro5UTkN5Jo2e7LMSgpQNqBGRTBuxJ4SOJYZsHnj+qYuYnP4O3p78P5EeDFFZMlUnfl3datWoUaHqsWw++kcUPWANYrnsy6Ey6WzcF7lRcFEwyzZVWRYfNalZ4o+WaJmrefFvVXelSKkWXVy14qNriIIiylULcHpLyi/nHGyWsUijEVVRwdBefHByEklk04OQRrlRJlFaOISBuDa8FqVlBucISPpejMIjtrt5SBw5mjywsFxBpUoCh1LY63uBkFkMiq8cGOnEpLNtmg7LNlEueOhxnsYLz3xDur6S1FvtTO3GnhBaHohk2VQ51hde+hbct2fw0eTPEFqLonVwS3GD85WNkFZkNVSWqlT1pJLasXhDty+JjI0LvUROX+XWr6pBDIlqkEw8LNYSFvwFQw0NWp7VoR9TVpcipWROR3lJLcC1vmg6k659jGQygaSVQ0HCfyvx23inWHBLtTvAT0/RUasgCycIRHrAqvRShX75SvdT1WxHk4iGWF/OLeRVGAHMpIdwYggvPP87OHz0cG1n3KkbuFO07u5sC2p7ZyLiKy/9Ac71fxtWaRhuQYOVoOAlIoMMfmQkRB2w6r/ifnT0q1WmcfuEjhETh1s/VXpzblFETTGZY8h8FJP1dYBeOoSgGrXJCnTVlXQDyCBRuXJfdqm+/uGoJ/SKWD/+7VhlJ71FWkhm3kMetMsVH9MLJbl3jP9LVMlYaV4ZE1lS9yZnmIfwqRJd7sIr576LZ859XjKDe03kGHtKaBW1UKvfdix87cv/Gl9/5t+jP3hZxC5MyFFqKVt2/LXWRkfyD26XMiSzlszYGWJCxZ1J1cuuJmk8G4WWLGudgqWrUBwvYrNCnPgzuzxY6joef/KJ2nzGtb+nDn1tSmNHlehxaHG1oahDJIElqiXAqRzCl5/893j1+W+pc0G4pzRahT1zOR4lpropT547i8PH/lvcG/smfv72f8bD8tvoGmWfO13a51aL0Sy1dqXAmoHElun7GhjoOYV0KhdZ3sYgQh6D/rCJ6lI3qt5DmRUTsgI+OkO0G4wWMaElwrA6qFCjmgLq0AWshvBnhnHh8Nfx6suvoztXP/at3VfZOPYNoYm4N3Q204VzT15EV3oAxfB3MTs/jvGxhyj403iIX0GPt70dBalaAxmU6YR48vGnxXVSBrqxJxzro1n1wY76rv4Q6R4WPmzsrrQScaA0Hngfg7siE5ks+F28b6LPfQZnH38Rw8+dwHD3CWRykWaDB9Y9DNGth31FaN4cNeFKnZgPHz0O4DhwDJg/uoB33/0NHs7+GobpI3AZK947QTl9SjYNLy4H0Iqj6O7ur0UuGiV0rGOhfjgRDsMNEjBMdtxvV/3OakhEgxnaVd/m59IQVDWY5eP44lNfxmjuPM6cO1NHeE442p9d/fcVoWPrxnnfKs3Ngx7FShZ6erulIfd+ASlnOxrmH+jIFJ+CWwGMZgt+I0NsmCZ6ssdR1ROwbA8Vpt9b3EVqLeIIB0N09WB82UmGcEtpnOn5HfzWy9+Mdk9XuSGsm9xnVrke+8ebXwOVODFgGowtM2rg19oA7BeYjiZ+8+HhcxKXbdYFiiPs3I2OHX8Cjp1VH62F0YxmIW6IzjrBNEZGjknmj4IyOvuGweTVvqWMYH9f3WrTsb+gGaLnTqUzeOqCypT5gap63gpxNlMp6pSFPHR0FBZGMDdRlWLT+uFB7YA0dnR9kX+u6yJFhpv5gvoh9/sdB4fQ+wjkoG0HmLmtw8ifFl0KEU/hEg+Y4cYNYFlRX7q6PLFUvORPwF3qEsuv7SiFvzV4dWwiqRpJrv55SdbrVDmueKSNngv2GgeG0IzXirWQ/PAe3zZNQypnwCtk4bhP1FyN+LLYesVMrHON0Q9MTjyU/0jfOQbJ/eSZV9DfdwTZPuoi2vdoJMFpaNLatxJlB2PIfTboR5s4dIzVNKJm6RC6VYhFPUr8MyTpYYkOrHneYtB2iei0wEzkDPYfx8nTK6f/WF+hhRbKC7FoKboTUYdx7uQPxh9KdTS38hX3Axg9PIruxAnMP/RhWO1TrPGSGHsW1WLcW0wxV1I4bsmHY+SQ61I+/c4EX7uL9pmBFkHkpgwTARg5fFjIonS5q9lLa6NUce2PhDBc9+DjAIPd5zF6ZKTWyy3Weut+Cv5sLooKxJro6HqDKOu3xqWIw5Vd1nkU7h+ClWpfXR7vEBuxU//Cc0BsCMRv130sPfRhFUZXFtu+yGI1hn1PaKJm5FwgUT0soh9OyKr3Uyl7ZNarnYgPanZSw1DqZfQlz0fXF99G9f46hxHriUiY9OgCY7+7tbsJFwPlsGfPPYfnLnwT+fnGDpjbQdn1sbBcVXLcOu0LL5Wh0Yw9jMH0k3XGof1GolU4EISOw1i2kcDR7GuwkZOD09p0LbdRiau25f4rfQZJPXGngsdPXpTIhM8K7TWkVTZ4jYWlHiLgFOUQd8avYX5+Tj3DOksdayqGuy8gtfxFGadmObpSue3wM6mWA8rWcs4L3Q2lH1+hEhdVIqPj0OgxvPTiF2s+3G7seq3CgSB0vOWZloWzj70gKWY7xcPhylOW8qlyVW2jO336a8CXYwSDqeBMt47R5Fdx7MiFSKtdfwvV9STMLHI2JZVK4xxfjpAnABaLkyiXCorP9aZao0/to6enD08//jtY/OSQyGOTWWrEH5WhbgU5VkSE5eKnzHZyviiVJ7Lz1S0SLhouoMK9HA5lXkA6m9mtI0lLcSAIHZkyIdDR44eRCg6hOBtKijZ2A7hdswUCv6SyqoXeB1V/ybQh5Jq/24fzp/85EhYPTMFKbWDUcFL+DC3YyK4ic80Ya0DZnUOgPepSqLi0ovmxE8dx/sS/RvHhoLRFSGZMBN7G3f5j1H9sLnLKQaUOsVCROkDpfbKqxpGLjk1ygGrZw/Hca3jyxCsi2D+IjD4QhFYVLupRSS3iwOvQC70wkwwnrUQD6JoWyq40PXm0GGB7UJpntskNUZxN4Vj62+gbGJAM2kaaZ8sxkUgkVhGCl89CAFZ+V50JuJqy0Gvdo1jPwl9++vxFnOr/FgoP+2XQUiKtSZlarJqut7BKmM8CgBVJLt0v3g+SmLWZS4XqqkqXeAdhJtstB0hXnsDnX/wmBocHakL/g4YDQWhiJeUa4tVXXseZYy+iUvChGyoCEpcT0eWYXyrX6gB3CkqgDCfE9L0AvcZFvPL5L8N2VCKFRF+FiGHdPb04ceSCKp3iHY5aGMS+cHKogsXClOLzOr6xipaoLOKLL34Fjw9+F4t3+sDjgccG6vTH1zTi4XlYvoJQStXy5aoM+bw7sYzJOSXgZzuIegvOxcXcSbUIdIWP4zu/9d9jeOBETfV4ELHvxElbQZU0aTjd/zrGH46hOnAVxTnW7EWlLBzSXvIwNV/AYE9KjTzbZPb1RlAbggYzoaOw6GIo+3n8sxd+v/bjTPKsRRwzZxq8p6cXGFdlAY9U0QTAvTu3cXJwEd09XevOzVavpdj+7LNfQG/XIfzTpb/ApPZTDA2nZBQEmzLaNqvoAymf0jWWo/nidjHiIwKvQNUCRp6MygKqalwYlg/fDdGNJ/Dd3/4fMDQ4Gi2yA2PnHsGBI7RyP3ycefIJwPi3+Pn734PW+z6qRU2NTtN8ITCnt/Kx9XcnpQPTeiL2dSHrgkWgGuw0MH6jghP938DFC78L23Y2HdoeXxvJzobm5vsmwqCieBkFX0gs6p/vzFzD+PhtdPVc2LQtFNsVcIGcfOxxpLK/j1v3n8Hl63+L+eAq+o7YQFmDVw3hVliBbkg8XgnopNYG7Aup/AcVLNJ0X7TOlN4u303h/JFv4MXnv1Ijc7wADyoOHKGVf6HJFNazT56HFv5bvPnhn+FB9dfI9JsoLwOBRyIFWFjmAbGCvmwCtm3C8+urxlfmIkpRvmiQdei2j0RWR2HBw/ytYZw99AU8eerLMjeFEYh6n309SH9kw0AqmYLl9aMQ3odussqGSQtJxYl1LRq3sOyPQcMzj4b46iCz/yIh/fDwEIaHv4nu5CHMV27hwexNjN2/haI3i2q4iO4jIVLdmhweV7tCbOQTorjgo7qYwEDmFI4ffQKDLzyO08efj3YJ3huGQg+udSYOJKF503kK1w0NT559Ckn7D/DuWA8eLF5HeeEeMgO+nNx5SFwuV+RAlw1tGGxwbsV+ZCAj5vg/NrnhwYglUXMTHrzlfmSdExjteQEvXWQ8lla1CrO+q+IGiH19z9WR8I5g0XuAZJLV1SvdjMJAR2q4isXyfYlgqCY7GyM+KNKn5mc/d+4ZAM/IeLzr6fewXJ1EKZiB60zCDcvI5wuoeitRlFQ6iXQiDX0ghUTfKEa7nsYzzz9be0PG0llksDaufxChfVK61sIA1+5CFQHwISt/9tKb7+D9e3+NvPMRypWCFKEGYVX6SyQSBgb7E8imbCXMKXN6bdQuQ7NhGQ4Mw4a3eBgDzit48aUvSCcgJkhU373GtBWxNa2Uy/jx334f1wvfh91dQiWvRD7KGdCR6NJhz53Bl879Ac4+fU5tPPT1t4ihx5+Zr0YSroeJB5NYmletxTgmgv2q4/KwGLwWtr1VGcqDbZXrcaAJvRa02uTD8vIi3nn7N5iavY2Z0k1UgiX45iK0HDvMA5msiWRxFImgB0GoI2OewUj/Y3jyqfNIpzNRxKQxAq9FPSlv3vgYf3P9f4afnkZlkXNeoohMoMn4t+KMjmePfhv/4it/KC+z12OFPw04kC7HepC5exEJu7p68dprX0a5VIYblsT3DTV+qTIiuip64MCIPr6OhFiw+PdrVqwBi7kW9QfDE4+dRPrWEKbzU+ICqeFB7L7KoSQGug6FmA9uKLeDsW7JFG5tpetREznFfXk2zPtHOcloP95qJzio+NQQWkT1MoZBNTiku8AvICpragCxeyEFoNKIcXsCili3zwWS8R7D+OJNJPrK0KMODMq9AHRLw+zMffzqjZ9Is0Ox0oGKajSK9a5xPbmntFvgi27vIx0YfHqcp6h9gCoCMGT7pv/ITqc89PgBY7P8U30FgSf+rnz5/FPpk+kr77RuLv59RlrOn34NfblRJHMqihKDvesqyyEqWMR7Y/8PlheZOWT0ZueME/Ku+fqs4FNF6HqQVAyfsYKcxZ2McBg6/1Rf6lSvKpj5c608GMVWk27GE+fOYajvKNxSiPqqLLoeDK8lu4BS4hbeu/pLia8z4bGXs7IPOj61hN5rKPdHRS767TNYHkvAlHj0ypVxVyDRXdfDrz/8czycuKfckaigoYPm0SF0m6B8VrX1n3vsNZweeRl2WnXXrzV211VWz3R0BF3juPLBWygWSpI0Itk7aB4dQrcZQeihf2AAp488h6UH0QAJqXpSvjLDiDJ3xgCuz/0l7kxclh4YjxQIdNAQOoRuM8QtBnDyyNMYNp+Hk1EteFfCZ0xLQ3QoRu883nz/hxgfuyc+P630QSpQ3Q/oELrNUMOBAvT3jeDi019HdcGRlLyk2uP3FvFbCLdo4MHSu/j15b+WGLrMepFs6IFN5u46OoRuM6RqXeRvIU6eeALD2mvwq7pkCrW6vsr0rquVEOlRH2PlX+IXv/p7NRUsInUHjaFD6F1ArAPJZbvxpRe/g6zVp/xm9hdZZXx9lJdChNkZXFn4Ht67/J5cHUVDnUNiY+gQehdQX0J27MQJnEz9c2ilHBJdtMurs4K+G4i22TPn8Itb/xtuffyhkjPtUgP0g44OoXcJcWqe5P78y9/AkHkRxakADkN5dRkXwwjhldXclpJ1F3936T9gcnZcIh+uV9mlqz246BB6lxBnD+kXs+zqpae+hR48Bd/1YNbVJtIDUU10AN/VMae/j398608wOT0Oi4435aydQ+KG6BB6FxHrKwLfw2NnzuLzz38X2vwwNGtloOgKlNbbskzcmPwxfvKbP8Hi0qyaUBhNRuoQ+1FIdP8gi/wPIpRElLZYx6UrP8XfvPe/wEioHnhrm2GoNgqatD87mnkF33z1v8TgyJB87Galpp92nEyePcDlvQcYKw1lgAtPvoYvPf7fQed8FYtZw9UzYkn80A9gZzRMhW/iL9/4n/DepXfl0/N1PI8a706cOkbH5dgjsPSJFSzsEf38+S/hiPE6vAqLXIHQpwS2zvmIRqzpTohl/Q7eGP8j/PDvv4divgjTtIT0lMh2VHoHtEj20wImVigZZTeo157/PQTvuniQ/ykSPR4qCxxgGOXNpbUZox86dFODmxvDpU/+AgX/Ic4cfRVPnXlJJLIE9d0qzPfZtFU1O9Dxo/cG4i5I+ZSGh/cn8JO3/xgT+i8AoywdjVTYY8WlEJ+a/TYSqmrdnxvExRPfwWMnn8Jg31HYjpo3/lnzr+k/ixsWP8YOofcWLPBl6dXE+CR+8uafYNr5KUrlsjSoWc9DlkJbFiY4rLgBMDOCl578V3j2/KtIp3OfOQvdIfQ+RGxVC/k8fvWbH+Pth/8BepKDSKOJBev2wVNmyXc1JDMWkktncfHU7+G5ixc/U6R+hNCd8N3eo95NKBXLuHz1p/jFrf8dRq4Cr6AOkWtJHbcTpiTVsDV4pRBO8TieO/4v8cUvfj36UOK37P0HbBNiMhOfzZPDPoUK51Ha7yOZSuDli1/DK6d/H3qxC3Y2hK49WqQvbREY5fDYRVSTkRJ+zx18PPuT2qf8LEU/PjVtDD4tkCxgFP2gSu/zF/+FVL28/+Cv4Cem4ZdWevLVQxHbh1eykRlgPFu16/2sYZWFrjfdHewdSOq4n50GH1944Tt4evD3EBYd1W96A+9BtRr2US16QGW9QYmfPqzlbMfl2MeQ4oBIiffcudfxePbb4iuz89N6rGbkI9QDLE15SFTV0EzBZyiR+AihO1Z6f4EJEi9wke3K4sL5F1FeNOCzsah05l1tqtkSOJkzkLZHcTjzUu2DxPMTP21Yj6sdC30AoEVWerj/KE5nvyoDkpwMp4BReRdbYXbkN1GY93G45xyef/5lNV6uyV55Bx3rErpjpfcXqPeglNRx0nj1wu/CKo5Ika2TDsBhVSS1kwGSPR6MpRE8+/hXxKJ/mrERRze00B1S70NowLFTx/G54/8K5vxpoJqQ2YlMvIRLXUiXn8DXXv59nDn1XNS0cmUi1qcJm3Gz43IcENAPjsu4Pv/yV/H04LdhLA8j1aVD90zkqufw9af/R5w/+5oanfEZfbRbpo86Go8O9hO28hy2tNBbvUAHHewWGuHiloQmGnmhDjpoJxrlYEOE7qCDg4KGCd3oCumgg1ajGe41TOiO69HBXqAZMhNNEbpD6g52E82SmdgybLcZOiG9DtqB7RA5RtMWuh47eeMOOlgPO+XUjgjdcUE6aCV2SuYduxxr0XFBOtgOWkHklrgca9HKC+vgs4FWc2ZHh8LN0LHWHWyGVhM5RtsIHaND7A7q0S4i7xqh69Eh92cT7SZxPdpuoTdCh9yfbuwmifcFodeiQ/CDjb0i8Fr8/wZjxZeB59cKAAAAAElFTkSuQmCC")
REPORT_ICON_64 = base64.b64decode("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")


def render_report_html() -> bytes:
    with _state_lock:
        journal = {k: v for k, v in json.loads(json.dumps(_state.get("journal", {}))).items()
                   if k >= JOURNAL_START}
        _js_ms = int(datetime.strptime(JOURNAL_START, "%Y-%m-%d").replace(tzinfo=KST).timestamp() * 1000)
        trades = [t for t in _state.get("trade_log", []) if t.get("t", 0) >= _js_ms][-40:]
        acct = dict(_state.get("last_account") or {})
    esc = html.escape
    days = sorted(journal.items(), reverse=True)
    now = datetime.now(KST)
    today = now.strftime("%Y-%m-%d")
    WD = "월화수목금토일"

    def cls(v):
        return "pos" if v > 0 else ("neg" if v < 0 else "zero")

    def fmt(v, d=2):
        return f"{v:+,.{d}f}"

    # ---------- 자동매매만 (수동 거래·입출금 제외)
    starts = bot_start_balances(journal)
    bot_real = sum(v.get("pnl", 0.0) for d, v in journal.items() if d >= JOURNAL_START)
    bot_upl = acct.get("bot_upl", 0.0) if acct else 0.0
    bot_eq = STARTING_BALANCE + bot_real + bot_upl
    gain = bot_real + bot_upl
    rate = gain / STARTING_BALANCE * 100 if STARTING_BALANCE else 0
    upd = datetime.fromtimestamp(acct["t"] / 1000, KST).strftime("%H:%M") if acct else "-"
    acct_line = ""
    real_card = ""
    if acct:
        real_card = f'''
<section class="card realbal">
  <div class="row"><div class="lab">🏦 OKX 실제 잔고 <span class="muted">· 수동 거래·입출금 포함</span></div></div>
  <div class="row end"><div class="big3">{acct["eq"]:,.2f}<small class="muted"> USDT</small></div>
    <div class="r tiny">현금 {acct["eq"] - acct["upl"]:,.2f}<br>미실현 <b class="{cls(acct["upl"])}">{fmt(acct["upl"])}</b></div></div>
</section>'''

    hero = f'''
<section class="hero">
  <div class="lab">자동매매 잔액 <span class="muted">· {upd} 기준</span></div>
  <div class="big">{bot_eq:,.2f}<small> USDT</small></div>
  <div class="sub">자동매매 미실현 <b class="{cls(bot_upl)}">{fmt(bot_upl)}</b> · 실현 <b class="{cls(bot_real)}">{fmt(bot_real)}</b></div>
  <div class="startrow">
    <div><div class="lab">🚩 시작 ({esc(JOURNAL_START[5:].replace("-", "/"))})</div><div class="mid">{STARTING_BALANCE:,.0f}</div></div>
    <div class="r"><div class="lab">시작 대비 순수익</div>
      <div class="mid {cls(gain)}">{fmt(gain)}</div>
      <div class="pill {cls(rate)}">{fmt(rate)}%</div></div>
  </div>
  {acct_line}
</section>'''

    hero += real_card

    # ---------- 오늘
    td = journal.get(today, {"win": 0, "be": 0, "loss": 0, "pnl": 0.0})
    tpct = (td["pnl"] / DAILY_TARGET_USD * 100) if DAILY_TARGET_USD else 0
    t_start = starts.get(today)
    tg = (td["pnl"] / t_start * 100) if t_start else None
    today_html = f'''
<section class="card today">
  <div class="row"><div class="lab">오늘 · {now.month}/{now.day}({WD[now.weekday()]})</div>
    <div class="lab">하루 목표 {DAILY_TARGET_USD:g}</div></div>
  <div class="row end"><div class="big2 {cls(td["pnl"])}">{fmt(td["pnl"])}<small> USDT</small></div>
    <div class="pct">{tpct:.0f}%</div></div>
  <div class="bar"><i style="width:{max(0, min(100, tpct)):.0f}%"></i></div>
  <div class="chips"><span class="chip w">✅ 익절 {td["win"]}회</span><span class="chip b">➖ 본절 {td["be"]}회</span><span class="chip l">🛑 손절 {td["loss"]}회</span></div>
  {f'<div class="note">0시 잔액 {t_start:,.2f} · 하루 수익률 <b class="{cls(tg)}">{fmt(tg)}%</b></div>' if tg is not None else ''}
</section>'''

    # ---------- 기간 합계
    week_start = (now - timedelta(days=now.weekday())).strftime("%Y-%m-%d")
    month = now.strftime("%Y-%m")

    def total(fn):
        t = {"win": 0, "be": 0, "loss": 0, "pnl": 0.0, "days": 0}
        for d, v in journal.items():
            if fn(d):
                t["days"] += 1
                for k in ("win", "be", "loss"):
                    t[k] += v[k]
                t["pnl"] += v["pnl"]
        return t
    tiles = ""
    for title, t in (("이번 주", total(lambda d: d >= week_start)),
                     ("이번 달", total(lambda d: d.startswith(month))),
                     ("전체", total(lambda d: True))):
        n = t["win"] + t["be"] + t["loss"]
        avg = t["pnl"] / t["days"] if t["days"] else 0
        wr = (t["win"] + t["be"]) / n * 100 if n else 0
        wk = ""
        if title == "이번 주" and WEEKLY_TARGET_USD:
            wp = t["pnl"] / WEEKLY_TARGET_USD * 100
            wk = (f'<div class="bar sm" style="margin:6px 0 2px"><i style="width:{max(0, min(100, wp)):.0f}%"></i></div>'
                  f'<div class="tiny">목표 {WEEKLY_TARGET_USD:.0f} 중 <b>{wp:.0f}%</b></div>')
        tiles += (f'<div class="tile"><div class="lab">{title}</div>'
                  f'<div class="mid {cls(t["pnl"])}">{fmt(t["pnl"], 1)}</div>{wk}'
                  f'<div class="tiny">{t["days"]}일 · {n}번<br>하루 {fmt(avg, 1)}<br>승률 {wr:.0f}%</div></div>')

    # ---------- 일별 (표)
    drows = ""
    mrows = ""
    for d, v in days:
        dt = datetime.strptime(d, "%Y-%m-%d")
        n = v["win"] + v["be"] + v["loss"]
        pct = (v["pnl"] / DAILY_TARGET_USD * 100) if DAILY_TARGET_USD else 0
        b_start = starts.get(d)
        g = (v["pnl"] / b_start * 100) if b_start else None
        bal = (f'<b>{b_start:,.2f}</b>'
               + (f'<br><span class="tiny">하루 <b class="{cls(g)}">{fmt(g)}%</b></span>' if g is not None else '')
               if b_start else '<span class="muted">-</span>')
        tr = []
        if v.get("dep"):
            tr.append(f'<span class="pos">입금 +{v["dep"]:,.0f}</span>')
        if v.get("wd"):
            tr.append(f'<span class="neg">출금 {v["wd"]:,.0f}</span>')
        if v.get("dep") and v.get("wd"):
            tr.append(f'<b>합계 <span class="{cls(v["dep"] + v["wd"])}">{v["dep"] + v["wd"]:+,.0f}</span></b>')
        trh = "<br>".join(tr) or '<span class="muted">-</span>'
        srcs = "<br>".join(f'{esc(k)} <b class="{cls(x["pnl"])}">{fmt(x["pnl"], 1)}</b>'
                           for k, x in v["by_source"].items()) or '<span class="muted">-</span>'
        extra = []
        if tr:
            extra.append(" · ".join(tr))
        if v["by_source"]:
            extra.append(" · ".join(f'{esc(k)} <b class="{cls(x["pnl"])}">{fmt(x["pnl"], 1)}</b>'
                                    for k, x in v["by_source"].items()))
        mrows += (f'<tr class="mtop"><td class="dt">{dt.month}/{dt.day}<br><span class="tiny">({WD[dt.weekday()]}) · {n}번</span></td>'
                  f'<td class="res3">✅ 익절 {v["win"]}회<br>➖ 본절 {v["be"]}회<br>🛑 손절 {v["loss"]}회</td>'
                  f'<td class="r"><span class="num {cls(v["pnl"])}">{fmt(v["pnl"])}</span>'
                  f'<div class="bar sm r"><i style="width:{max(0, min(100, pct)):.0f}%"></i></div>'
                  f'<span class="tiny">목표 {pct:.0f}%</span></td>'
                  f'<td class="r">{bal}</td></tr>'
                  + (f'<tr class="msub"><td colspan="4">{"<br>".join(extra)}</td></tr>' if extra else ''))
        drows += (f'<tr><td class="dt">{dt.month}/{dt.day}<br><span class="tiny">({WD[dt.weekday()]})</span></td>'
                  f'<td>{n}</td>'
                  f'<td class="res3">✅ 익절 {v["win"]}회<br>➖ 본절 {v["be"]}회<br>🛑 손절 {v["loss"]}회</td>'
                  f'<td class="num {cls(v["pnl"])}">{fmt(v["pnl"])}</td>'
                  f'<td><div class="bar sm"><i style="width:{max(0, min(100, pct)):.0f}%"></i></div>'
                  f'<span class="tiny">{pct:.0f}%</span></td>'
                  f'<td>{bal}</td><td class="small">{trh}</td><td class="small">{srcs}</td></tr>')
    if not drows:
        drows = '<tr><td colspan="8" class="empty">아직 기록이 없어요</td></tr>'
        mrows = '<tr><td colspan="4" class="empty">아직 기록이 없어요</td></tr>'
    dcards = (f'<div class="tblwrap"><table class="dtbl"><thead><tr><th>날짜</th><th>거래</th><th>결과</th>'
              f'<th>실현손익</th><th>목표 달성</th><th>0시 잔액</th><th>입출금</th><th>신호별</th></tr></thead>'
              f'<tbody>{drows}</tbody></table></div>'
              f'<div class="mwrap"><table class="mtbl"><thead><tr><th>날짜</th><th>결과</th>'
              f'<th class="r">실현손익</th><th class="r">0시 잔액</th></tr></thead><tbody>{mrows}</tbody></table></div>')

    # ---------- 최근 거래
    tl = ""
    for t in reversed(trades):
        ts = datetime.fromtimestamp(t["t"] / 1000, KST)
        kind = {"win": ("✅", "익절"), "be": ("➖", "본절"), "loss": ("🛑", "손절")}.get(t["kind"], ("", ""))
        side = {"L": "롱", "S": "숏"}.get(t.get("side"), "")
        tl += (f'<div class="tr"><div class="ic">{kind[0]}</div>'
               f'<div class="tm"><div class="sym">{esc(t["inst"].replace("-USDT-SWAP", ""))} <span class="sd {"l" if side == "롱" else "s"}">{side}</span></div>'
               f'<div class="tiny">{esc(t["src"] or "")} · {ts.month}/{ts.day} {ts:%H:%M}</div></div>'
               f'<div class="tp {cls(t["pnl"])}">{fmt(t["pnl"])}<div class="tiny r">{kind[1]}</div></div></div>')
    if not tl:
        tl = '<div class="empty">아직 거래가 없어요</div>'

    page = f"""<!doctype html><html lang="ko"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="theme-color" content="#f3f4f7"><meta http-equiv="refresh" content="60">
<meta name="apple-mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-title" content="매매 기록지">
<link rel="icon" type="image/png" sizes="64x64" href="{REPORT_PATH}/icon64.png">
<link rel="apple-touch-icon" href="{REPORT_PATH}/icon.png"><title>매매 기록지</title>
<style>
:root{{--bg:#f3f4f7;--fg:#14161b;--card:#fff;--muted:#7a808c;--line:#e7e9ee;--pos:#0e9f5a;--neg:#e0443a;--zero:#7a808c;
--acc:#4b6bff;--acc2:#8a5cff;--chip:#f1f3f7;--hero1:#1b2140;--hero2:#2d2a5e}}
*{{box-sizing:border-box}}
body{{margin:0;background:var(--bg);color:var(--fg);font:15px/1.45 -apple-system,BlinkMacSystemFont,"Apple SD Gothic Neo","Noto Sans KR",sans-serif;-webkit-font-smoothing:antialiased}}
.wrap{{max-width:720px;margin:0 auto;padding:14px 14px calc(28px + env(safe-area-inset-bottom))}}
header{{display:flex;justify-content:space-between;align-items:center;margin:4px 2px 12px}}
h1{{font-size:19px;margin:0;letter-spacing:-.3px}} .muted{{color:var(--muted)}} .tiny{{font-size:11.5px;color:var(--muted);line-height:1.5}}
.pos{{color:var(--pos)}} .neg{{color:var(--neg)}} .zero{{color:var(--zero)}} .r{{text-align:right}}
.lab{{font-size:12px;color:var(--muted)}} .small{{font-size:12.5px}}
.card{{background:var(--card);border:1px solid var(--line);border-radius:18px;padding:14px 16px;margin-bottom:12px}}
.hero{{border-radius:22px;padding:18px 18px 14px;margin-bottom:12px;color:#fff;
background:radial-gradient(120% 140% at 100% 0%,var(--hero2),var(--hero1));box-shadow:0 10px 30px rgba(40,40,90,.25)}}
.hero .lab,.hero .muted,.hero .note,.hero .sub{{color:rgba(255,255,255,.72)}}
.hero .pos{{color:#5cf0a8}} .hero .neg{{color:#ff8f86}}
.big{{font-size:34px;font-weight:800;letter-spacing:-.8px;margin:2px 0}} .big small,.big2 small{{font-size:14px;font-weight:600;opacity:.7}}
.big2{{font-size:28px;font-weight:800;letter-spacing:-.6px}} .big3{{font-size:20px;font-weight:800;letter-spacing:-.4px}}
.mid{{font-size:19px;font-weight:750;letter-spacing:-.3px}}
.sub{{font-size:13px}} .note{{font-size:11.5px;color:var(--muted);margin-top:8px}}
.spark{{width:100%;height:64px;margin:10px 0 0;display:block}} .spark .ln{{fill:none;stroke-width:2.2;stroke-linejoin:round;stroke-linecap:round}}
.spark.up .ln{{stroke:#5cf0a8}} .spark.down .ln{{stroke:#ff8f86}} .spark .fill{{opacity:.18}} .spark.up .fill{{fill:#5cf0a8}} .spark.down .fill{{fill:#ff8f86}}
.spark .dot{{fill:#fff}} .sparklab{{display:flex;justify-content:space-between;font-size:10.5px;color:rgba(255,255,255,.55);margin-top:2px}}
.startrow{{display:flex;justify-content:space-between;align-items:flex-end;margin-top:12px;padding-top:12px;border-top:1px solid rgba(255,255,255,.14)}}
.startrow .r{{text-align:right}} .pill{{display:inline-block;margin-top:4px;padding:2px 9px;border-radius:999px;font-size:12px;font-weight:700;background:rgba(255,255,255,.12)}}
.row{{display:flex;justify-content:space-between;align-items:center;gap:8px}} .row.end{{align-items:flex-end}}
.pct{{font-size:15px;font-weight:700;color:var(--acc)}}
.bar{{height:9px;background:var(--chip);border-radius:6px;overflow:hidden;margin:10px 0}} .bar.sm{{height:6px;margin:8px 0 6px}}
.bar i{{display:block;height:100%;border-radius:6px;background:linear-gradient(90deg,var(--acc),var(--acc2))}}
.chips{{display:flex;gap:6px;flex-wrap:wrap}} .chip{{background:var(--chip);border-radius:999px;padding:5px 10px;font-size:12.5px;font-weight:600}}
.realbal{{padding:12px 16px}} .realbal .big3 small{{font-size:12px;font-weight:600}}
.tiles{{display:grid;grid-template-columns:repeat(3,1fr);gap:8px;margin-bottom:18px}}
.tile{{background:var(--card);border:1px solid var(--line);border-radius:16px;padding:11px 12px}} .tile .mid{{font-size:17px;margin:2px 0 4px}}
h2{{font-size:15px;margin:20px 4px 10px;letter-spacing:-.2px}}
.day .date{{font-weight:750;font-size:15px}}
.res{{display:grid;grid-template-columns:repeat(3,1fr);gap:6px;margin-top:10px}}
.res div{{background:var(--chip);border-radius:10px;padding:7px 6px;text-align:center;font-size:12.5px;font-weight:600}}
.tags{{display:flex;gap:6px;flex-wrap:wrap;margin-top:8px}} .tag{{font-size:12px;font-weight:700;padding:3px 9px;border-radius:8px;background:var(--chip)}}
.srcs{{display:flex;gap:10px;flex-wrap:wrap;margin-top:8px;font-size:12px;color:var(--muted)}}
.tblwrap{{background:var(--card);border:1px solid var(--line);border-radius:18px;overflow-x:auto;-webkit-overflow-scrolling:touch}}
.dtbl{{border-collapse:collapse;white-space:nowrap;width:100%;font-size:13.5px}}
.dtbl th{{position:sticky;top:0;background:var(--card);color:var(--muted);font-size:11.5px;font-weight:600;text-align:left;padding:10px 12px;border-bottom:1px solid var(--line)}}
.dtbl td{{padding:11px 12px;border-bottom:1px solid var(--line);vertical-align:middle}} .dtbl tr:last-child td{{border-bottom:0}}
.dtbl th:first-child,.dtbl td:first-child{{position:sticky;left:0;background:var(--card);z-index:1}}
.dtbl .dt{{font-weight:750}} .dtbl .num{{font-weight:800;font-size:15px}} .dtbl .res3{{line-height:1.7;font-size:12.5px}}
.dtbl .bar.sm{{width:70px;margin:0 0 3px}}
.mwrap{{display:none;background:var(--card);border:1px solid var(--line);border-radius:18px;overflow:hidden}}
.mtbl{{border-collapse:collapse;width:100%;font-size:12.5px}}
.mtbl th{{color:var(--muted);font-size:11px;font-weight:600;text-align:left;padding:9px 10px;border-bottom:1px solid var(--line)}}
.mtbl td{{padding:10px 10px;vertical-align:middle}} .mtbl .r,.mtbl th.r{{text-align:right}}
.mtbl tr.mtop td{{border-top:1px solid var(--line)}} .mtbl tbody tr.mtop:first-child td{{border-top:0}}
.mtbl tr.msub td{{padding:0 10px 10px;font-size:11.5px;color:var(--muted);line-height:1.6}}
.mtbl .dt{{font-weight:750;font-size:13.5px}} .mtbl .num{{font-weight:800;font-size:14.5px}} .mtbl .res3{{line-height:1.65;font-size:12px}}
.mtbl .bar.sm{{width:64px;margin:5px 0 2px auto}}
@media (max-width:600px){{.tblwrap{{display:none}} .mwrap{{display:block}}}}
.list{{background:var(--card);border:1px solid var(--line);border-radius:18px;padding:4px 14px}}
.tr{{display:flex;align-items:center;gap:10px;padding:11px 0;border-bottom:1px solid var(--line)}} .tr:last-child{{border-bottom:0}}
.ic{{width:34px;height:34px;border-radius:10px;background:var(--chip);display:flex;align-items:center;justify-content:center;font-size:15px;flex:none}}
.tm{{flex:1;min-width:0}} .sym{{font-weight:700}} .sd{{font-size:11px;font-weight:700;padding:1px 6px;border-radius:6px;margin-left:4px}}
.sd.l{{color:var(--pos);background:color-mix(in srgb,var(--pos) 14%,transparent)}} .sd.s{{color:var(--neg);background:color-mix(in srgb,var(--neg) 14%,transparent)}}
.tp{{font-weight:800;text-align:right}} .empty{{color:var(--muted);text-align:center;padding:18px}}
footer{{text-align:center;font-size:11px;color:var(--muted);margin-top:18px}}
</style></head><body><div class="wrap">
<header><h1>📒 매매 기록지</h1><a class="tiny" style="color:var(--acc);font-weight:700;text-decoration:none" href="{POSITIONS_PATH}">⚡ 실시간 포지션 →</a></header>
{hero}
{today_html}
<div class="tiles">{tiles}</div>
<h2>일별 기록</h2>
{dcards}
<h2>최근 거래</h2>
<div class="list">{tl}</div>
<footer>봇 거래만 기록 · 수동 거래 제외 · 하루 기준 한국시간 0시<br><a href="{REPORT_PATH}/trades.csv" style="color:inherit">📥 전체 거래 기록 엑셀(CSV) 받기</a></footer>
</div></body></html>"""
    return page.encode("utf-8")


def normalize_symbol(sym: str) -> str:
    """'BTCUSDT', 'BTCUSDT.P', 'BTC-USDT-SWAP' 등을 'BTC-USDT-SWAP'으로 통일."""
    sym = (sym or "").upper().strip()
    if sym.endswith(".P"):
        sym = sym[:-2]
    if sym.endswith("-SWAP"):
        return sym
    if "-" in sym:
        base, quote = sym.split("-")[:2]
    elif sym.endswith("USDT"):
        base, quote = sym[:-4], "USDT"
    else:
        base, quote = sym, "USDT"
    return f"{base}-{quote}-SWAP"


# ----------------------------------------------------------------------------
# OKX 실행 래퍼
# ----------------------------------------------------------------------------

@dataclass
class OkxExecutor:
    api_key: str
    api_secret: str
    passphrase: str
    _inst_cache: dict = field(default_factory=dict, init=False)

    def _timestamp(self) -> str:
        now = datetime.now(timezone.utc)
        return now.strftime("%Y-%m-%dT%H:%M:%S.") + f"{now.microsecond // 1000:03d}Z"

    def _sign(self, ts: str, method: str, path: str, body: str) -> str:
        msg = f"{ts}{method}{path}{body}"
        mac = hmac.new(self.api_secret.encode(), msg.encode(), hashlib.sha256)
        return base64.b64encode(mac.digest()).decode()

    def _request(self, method: str, path: str, params: dict | None = None, body: dict | None = None) -> dict:
        body_str = json.dumps(body) if body else ""
        query = ""
        if params:
            query = "?" + "&".join(f"{k}={v}" for k, v in params.items())
        ts = self._timestamp()
        headers = {
            "OK-ACCESS-KEY": self.api_key,
            "OK-ACCESS-SIGN": self._sign(ts, method, path + query, body_str),
            "OK-ACCESS-TIMESTAMP": ts,
            "OK-ACCESS-PASSPHRASE": self.passphrase,
            "Content-Type": "application/json",
        }
        resp = requests.request(method, OKX_BASE_URL + path + query, headers=headers,
                                data=body_str if body else None, timeout=15)
        data = resp.json()
        if data.get("code") not in ("0", 0):
            raise OkxApiError(data)
        return data

    def get_instrument(self, inst_id: str) -> dict:
        if inst_id in self._inst_cache:
            return self._inst_cache[inst_id]
        data = self._request("GET", "/api/v5/public/instruments", params={"instType": "SWAP", "instId": inst_id})
        info = data["data"][0]
        self._inst_cache[inst_id] = info
        return info

    def get_mark_price(self, inst_id: str) -> float:
        data = self._request("GET", "/api/v5/market/ticker", params={"instId": inst_id})
        return float(data["data"][0]["last"])

    def get_24h_volume_usd(self, inst_id: str) -> float:
        """최근 24시간 거래대금(USD). volCcy24h(코인 수량) × 현재가."""
        data = self._request("GET", "/api/v5/market/ticker", params={"instId": inst_id})
        t = data["data"][0]
        return float(t.get("volCcy24h") or 0) * float(t.get("last") or 0)

    def calc_qty(self, inst_id: str, notional_usdt: float, ref_price: float) -> float:
        inst = self.get_instrument(inst_id)
        ct_val = float(inst["ctVal"])
        lot_sz = float(inst["lotSz"])
        min_sz = float(inst["minSz"])
        qty = math.floor(notional_usdt / (ref_price * ct_val) / lot_sz) * lot_sz
        decimals = max(0, -int(math.floor(math.log10(lot_sz)))) if lot_sz < 1 else 0
        qty = round(qty, decimals)
        return qty if qty >= min_sz else 0.0

    def set_leverage(self, inst_id: str, leverage: int) -> None:
        try:
            self._request("POST", "/api/v5/account/set-leverage",
                          body={"instId": inst_id, "lever": str(leverage), "mgnMode": TD_MODE})
        except Exception as e:  # noqa: BLE001
            log.info("레버리지 설정 스킵/실패(무시): %s", e)

    def open_position(self, inst_id: str, side: str, notional_usdt: float, ref_price: float,
                      leverage: int, tp_margin_pct: float, sl_margin_pct: float) -> Optional[float]:
        order_side = "sell" if side == "S" else "buy"
        label = "SHORT" if side == "S" else "LONG"

        qty = self.calc_qty(inst_id, notional_usdt, ref_price)
        if qty <= 0:
            log.error("계산된 수량이 0 이하입니다: %s", inst_id)
            return None

        tp_price_pct = tp_margin_pct / leverage
        sl_price_pct = sl_margin_pct / leverage
        if side == "S":
            tp_price = ref_price * (1 - tp_price_pct)
            sl_price = ref_price * (1 + sl_price_pct)
        else:
            tp_price = ref_price * (1 + tp_price_pct)
            sl_price = ref_price * (1 - sl_price_pct)

        self.set_leverage(inst_id, leverage)

        body = {
            "instId": inst_id,
            "tdMode": TD_MODE,
            "side": order_side,
            "ordType": "market",
            "sz": str(qty),
            "attachAlgoOrds": [{
                "attachAlgoClOrdId": bot_algo_id(),
                "tpTriggerPx": str(round(tp_price, 6)),
                "tpOrdPx": "-1",
                "slTriggerPx": str(round(sl_price, 6)),
                "slOrdPx": "-1",
            }],
        }
        data = self._request("POST", "/api/v5/trade/order", body=body)
        log.info("%s OPEN 주문 전송: %s qty=%s TP=%.6f SL=%.6f -> %s", label, inst_id, qty, tp_price, sl_price, data)
        return qty

    def get_account_summary(self) -> dict:
        data = self._request("GET", "/api/v5/account/balance", params={"ccy": "USDT"})
        detail = data["data"][0]["details"][0] if data["data"][0]["details"] else {}
        return {
            "usdt_balance": float(detail.get("eq", 0) or 0),
            "unrealized_pnl": float(detail.get("upl", 0) or 0),
        }

    def get_positions_history(self, after_ms: Optional[int] = None) -> list:
        params = {"instType": "SWAP", "limit": "100"}
        if after_ms:
            params["after"] = str(after_ms)   # 이 시각보다 이전 기록
        data = self._request("GET", "/api/v5/account/positions-history", params=params)
        return data.get("data", []) or []

    def get_transfer_bills(self) -> list:
        """거래 계정 USDT 이체 내역 (자금 계정 ↔ 거래 계정). 최근 7일, 최신순."""
        data = self._request("GET", "/api/v5/account/bills",
                             params={"ccy": "USDT", "type": "1", "limit": "100"})
        return data.get("data", []) or []

    def get_position_size(self, inst_id: str) -> float:
        data = self._request("GET", "/api/v5/account/positions", params={"instId": inst_id})
        return sum(abs(float(p.get("pos", 0) or 0)) for p in data.get("data", []))

    def get_open_positions(self) -> list:
        data = self._request("GET", "/api/v5/account/positions")
        return [p for p in data.get("data", []) if float(p.get("pos", 0)) != 0]

    # -- 포지션 관리용 ------------------------------------------------------

    def round_px(self, inst_id: str, px: float) -> str:
        tick = float(self.get_instrument(inst_id)["tickSz"])
        n = round(px / tick) * tick
        decimals = max(0, -int(math.floor(math.log10(tick)))) if tick < 1 else 0
        return f"{n:.{decimals}f}"

    def round_sz_down(self, inst_id: str, sz: float) -> float:
        inst = self.get_instrument(inst_id)
        lot = float(inst["lotSz"])
        q = math.floor(sz / lot + 1e-9) * lot
        decimals = max(0, -int(math.floor(math.log10(lot)))) if lot < 1 else 0
        q = round(q, decimals)
        return q if q >= float(inst["minSz"]) else 0.0

    def pending_tpsl(self, inst_id: str) -> list:
        data = self._request("GET", "/api/v5/trade/orders-algo-pending",
                             params={"instType": "SWAP", "instId": inst_id, "ordType": "conditional,oco"})
        return data.get("data", []) or []

    def pending_tpsl_ids(self, inst_id: str) -> list:
        data = self._request("GET", "/api/v5/trade/orders-algo-pending",
                             params={"instType": "SWAP", "instId": inst_id, "ordType": "conditional,oco"})
        return [d["algoId"] for d in data.get("data", []) if d.get("algoId")]

    def cancel_algos(self, inst_id: str, algo_ids: list) -> None:
        if not algo_ids:
            return
        self._request("POST", "/api/v5/trade/cancel-algos",
                      body=[{"algoId": a, "instId": inst_id} for a in algo_ids])

    def replace_tpsl(self, inst_id: str, side: str, tp_px: float, sl_px: float) -> str:
        """포지션 전체에 걸리는 익절/손절 주문을 새로 걸고, 기존 익절/손절 주문은 취소."""
        old = self.pending_tpsl_ids(inst_id)
        body = {
            "instId": inst_id,
            "tdMode": TD_MODE,
            "side": "buy" if side == "S" else "sell",
            "ordType": "oco",
            "algoClOrdId": bot_algo_id(),
            "closeFraction": "1",
            "reduceOnly": True,
            "tpTriggerPx": self.round_px(inst_id, tp_px),
            "tpOrdPx": "-1",
            "slTriggerPx": self.round_px(inst_id, sl_px),
            "slOrdPx": "-1",
        }
        data = self._request("POST", "/api/v5/trade/order-algo", body=body)
        new_id = data["data"][0].get("algoId", "")
        try:
            self.cancel_algos(inst_id, [a for a in old if a != new_id])
        except Exception as e:  # noqa: BLE001
            log.warning("%s 기존 익절/손절 주문 취소 실패(새 주문은 정상): %s", inst_id, e)
        return new_id

    def close_partial(self, inst_id: str, side: str, sz: float) -> None:
        self._request("POST", "/api/v5/trade/order", body={
            "instId": inst_id, "tdMode": TD_MODE,
            "side": "buy" if side == "S" else "sell",
            "ordType": "market", "sz": str(sz), "reduceOnly": True,
        })


_executor: Optional[OkxExecutor] = None


def recover_bot_positions() -> None:
    """봇 기억(상태 파일)이 지워져서 '수동'으로 잘못 표시된 포지션을,
    OKX에 걸린 익절·손절 주문을 보고 다시 봇 포지션으로 되찾음.
    (BTC·ETH 같은 수동 전용 종목, 코인 아닌 종목은 제외)"""
    try:
        live = {p["instId"]: p for p in _executor.get_open_positions()}
    except Exception as e:  # noqa: BLE001
        log.warning("봇 포지션 복구: 포지션 조회 실패 %s", e)
        return
    with _state_lock:
        cand = [i for i, ents in _state.get("positions", {}).items()
                if ents and i in live and i not in BOT_EXCLUDE_SYMBOLS
                and (not ents[0].get("tp_px") or ents[0].get("source") == "복구")]
    for inst_id in cand:
        if NON_CRYPTO_BLOCK and is_non_crypto(inst_id):
            continue
        try:
            algos = _executor.pending_tpsl(inst_id)
        except Exception as e:  # noqa: BLE001
            log.warning("%s 익절·손절 주문 조회 실패: %s", inst_id, e)
            continue
        bot_algos = [a for a in algos if is_bot_algo(a)]
        if not bot_algos:
            # 봇 이름표가 붙은 주문이 없으면 수동 포지션 → 봇이 절대 건드리지 않음
            with _state_lock:
                ents = _state.get("positions", {}).get(inst_id) or []
                if ents and ents[0].get("source") == "복구":
                    ents[0].update(manual=True, tp_px=None, source=None)
                    save_state(_state)
                    log.info("%s 수동 포지션으로 되돌림 (봇 주문 아님)", inst_id)
            continue
        tps = [float(a["tpTriggerPx"]) for a in bot_algos if a.get("tpTriggerPx")]
        sls = [float(a["slTriggerPx"]) for a in bot_algos if a.get("slTriggerPx")]
        if not tps:
            continue
        p = live[inst_id]
        pos = float(p.get("pos", 0) or 0)
        side = "L" if pos > 0 else "S"
        entry = float(p.get("avgPx", 0) or 0)
        tp = max(tps) if side == "L" else min(tps)
        sl = (max(sls) if side == "L" else min(sls)) if sls else None
        be = step = False
        if sl and entry:
            gain_at_sl = (sl - entry) / entry if side == "L" else (entry - sl) / entry
            be = gain_at_sl >= 0
            step = gain_at_sl >= STEP_LOCK_PCT * 0.8
        ctime = int(p.get("cTime", 0) or 0) or int(time.time() * 1000)
        with _state_lock:
            ents = _state.setdefault("positions", {}).get(inst_id) or [{}]
            e = ents[0]
            e.update(side=side, qty=abs(pos), entry=entry, tp_px=tp, manual=False,
                     source=e.get("source") or "복구", opened_at=e.get("opened_at") or ctime,
                     be_done=be, partial_done=be, step_done=step or e.get("step_done", False),
                     step_locked=step)
            _state["positions"][inst_id] = [e]
            save_state(_state)
        log.info("%s 봇 포지션으로 복구 (익절 %s, 본절 %s, 수익확보 %s)", inst_id, tp, be, step)


def sync_positions_from_exchange() -> None:
    """시작할 때 OKX 실제 포지션 기준으로 로컬 상태를 다시 맞춤."""
    try:
        open_positions = _executor.get_open_positions()
    except Exception as e:  # noqa: BLE001
        log.warning("시작 시 포지션 동기화 실패: %s", e)
        return

    with _state_lock:
        new_positions: dict = {}
        for p in open_positions:
            inst_id = p.get("instId")
            pos_val = float(p.get("pos", 0) or 0)
            if not inst_id or pos_val == 0:
                continue
            prev = (_state.get("positions", {}).get(inst_id) or [{}])[0]
            new_positions[inst_id] = [{
                "side": "L" if pos_val > 0 else "S",
                "qty": abs(pos_val),
                "entry": float(p.get("avgPx", 0) or 0),
                "source": prev.get("source"),
                "opened_at": prev.get("opened_at"),
                "tp_px": prev.get("tp_px"),
                "be_done": prev.get("be_done", False),
                "partial_done": prev.get("partial_done", False),
                "step_done": prev.get("step_done", False),
                # 봇이 진입한 기록(tp_px)이 없으면 수동 포지션으로 보고 성적·손절 횟수에서 제외
                "manual": (not prev.get("tp_px")) or inst_id in BOT_EXCLUDE_SYMBOLS,
            }]
        _state["positions"] = new_positions
        save_state(_state)

    if new_positions:
        log.info("시작 시 OKX 실제 포지션과 동기화 완료: %s", ", ".join(new_positions.keys()))
    else:
        log.info("시작 시 OKX에 열려있는 포지션이 없습니다.")


# ----------------------------------------------------------------------------
# 진입 처리
# ----------------------------------------------------------------------------

# ----------------------------------------------------------------------------
# 비트코인 급변동 필터: BTC가 크게 흔들릴 때는 알트 신호(아트로포스·오라클) 진입을 잠시 멈춤
BTC_GUARD_ENABLED = True
BTC_GUARD_INST = "BTC-USDT-SWAP"
BTC_GUARD_MOVE_PCT = 0.015     # 15분 안에 BTC ±1.5% 이상 → 급등이면 숏 멈춤, 급락이면 롱 멈춤
BTC_GUARD_RANGE_PCT = 0.012    # 5분봉 하나의 위아래 폭이 1.2% 이상 → 롱·숏 모두 멈춤 (흔들기)
BTC_GUARD_COOLDOWN_MIN = 30    # 조건이 사라지고 이 시간(분) 지나면 다시 진입
BTC_GUARD_POLL_SEC = 20

_btc_guard = {"S": 0.0, "L": 0.0, "why_S": "", "why_L": ""}   # 방향별 '이 시각까지 멈춤'(초)


# 이 시각(한국시간)까지 신규 진입 멈춤 (빈 문자열이면 사용 안 함). 열린 포지션은 그대로 관리.
PAUSE_UNTIL_KST = "2026-11-28 03:00"


def paused_until() -> Optional[str]:
    if not PAUSE_UNTIL_KST:
        return None
    try:
        until = datetime.strptime(PAUSE_UNTIL_KST, "%Y-%m-%d %H:%M").replace(tzinfo=KST)
    except ValueError:
        return None
    return PAUSE_UNTIL_KST if datetime.now(KST) < until else None


def btc_guard_blocked(side: str) -> Optional[str]:
    if not BTC_GUARD_ENABLED:
        return None
    if time.time() < _btc_guard.get(side, 0.0):
        return _btc_guard.get("why_" + side) or "BTC 급변동"
    return None


def btc_guard_loop():
    log.info("BTC 급변동 필터 시작: 15분 ±%.1f%% / 5분봉 폭 %.1f%% / 풀림 %d분",
             BTC_GUARD_MOVE_PCT * 100, BTC_GUARD_RANGE_PCT * 100, BTC_GUARD_COOLDOWN_MIN)
    active = {"S": False, "L": False}
    while True:
        time.sleep(BTC_GUARD_POLL_SEC)
        if not BTC_GUARD_ENABLED:
            continue
        try:
            data = _executor._request("GET", "/api/v5/market/candles",
                                      params={"instId": BTC_GUARD_INST, "bar": "5m", "limit": "4"})
            c = data.get("data", []) or []   # 최신 봉이 맨 앞: [ts, o, h, l, c, ...]
            if len(c) < 3:
                continue
            last = float(c[0][4])
            move = last / float(c[2][1]) - 1           # 최근 15분(5분봉 3개) 변화
            rng = max((float(k[2]) - float(k[3])) / float(k[1]) for k in c[:2])   # 지금 봉·직전 봉 위아래 폭
            now = time.time()
            until = now + BTC_GUARD_COOLDOWN_MIN * 60
            hits = {}
            if rng >= BTC_GUARD_RANGE_PCT:
                why = f"BTC 5분봉 위아래 {rng * 100:.2f}% 흔들림"
                hits["S"] = hits["L"] = why
            if move >= BTC_GUARD_MOVE_PCT:
                hits["S"] = f"BTC 15분 {move * 100:+.2f}% 급등"
            elif move <= -BTC_GUARD_MOVE_PCT:
                hits["L"] = f"BTC 15분 {move * 100:+.2f}% 급락"
            for sd, why in hits.items():
                _btc_guard[sd] = until
                _btc_guard["why_" + sd] = why
            started = [sd for sd in hits if not active[sd]]
            for sd in started:
                active[sd] = True
            if started:
                what = "롱·숏 모두" if (active["S"] and active["L"]) else ("숏" if started[0] == "S" else "롱")
                notify("⚡ BTC 급변동 — 진입 멈춤",
                       f"{hits[started[0]]}\n→ {what} 신규 진입을 멈춰요 (BTC {last:,.1f}).\n"
                       f"잠잠해지고 {BTC_GUARD_COOLDOWN_MIN}분 지나면 다시 진입해요.\n"
                       f"열려 있는 포지션은 익절·손절 그대로 유지돼요.")
            ended = [sd for sd in ("S", "L") if active[sd] and now >= _btc_guard.get(sd, 0.0)]
            for sd in ended:
                active[sd] = False
            if ended:
                what = "롱·숏 모두" if len(ended) == 2 else ("숏" if ended[0] == "S" else "롱")
                notify("✅ BTC 잠잠해짐 — 진입 재개", f"{what} 신규 진입을 다시 시작해요 (BTC {last:,.1f}).")
        except Exception as ex:  # noqa: BLE001
            log.warning("BTC 급변동 필터 조회 오류: %s", ex)


def enter_position(symbol: str, side_raw: str, leverage: int = LEVERAGE,
                   tp_pct: float = TAKE_PROFIT_PCT, sl_pct: float = STOP_LOSS_PCT,
                   source: str = "기타", margin: Optional[float] = None) -> None:
    inst_id = normalize_symbol(symbol)
    side = "S" if side_raw == "short" else "L"
    if side == "L" and not LONG_ENTRY_ENABLED:
        log.info("롱 진입 꺼짐 — %s %s 롱 신호 무시", source, inst_id)
        return
    if NON_CRYPTO_BLOCK and is_non_crypto(inst_id):
        log.info("%s 은 코인이 아닌 종목(주식·ETF 등)이라 봇 진입 안 함", inst_id)
        return
    if inst_id in BOT_EXCLUDE_SYMBOLS:
        log.info("%s 은 수동 전용 종목이라 봇 진입 안 함", inst_id)
        return
    if paused_until():
        log.info("%s %s 신호 스킵 — %s(한국시간)까지 진입 멈춤", source, inst_id, PAUSE_UNTIL_KST)
        return
    why = btc_guard_blocked(side)
    if why:
        log.info("%s %s %s 신호 스킵 — %s", source, inst_id, "숏" if side == "S" else "롱", why)
        return

    # OKX에 이미 이 종목 포지션이 있으면(직접 들어간 수동 포지션 등) 봇은 들어가지 않음
    # → 같은 종목은 OKX에서 하나로 합쳐져서, 봇 손절·익절이 수동 물량까지 정리해버리기 때문
    try:
        live_sz = _executor.get_position_size(inst_id)
    except Exception as e:  # noqa: BLE001
        log.warning("%s 포지션 확인 실패 — 안전하게 진입 안 함: %s", inst_id, format_okx_error(e))
        return
    if live_sz > 0:
        with _state_lock:
            ents = _state.get("positions", {}).get(inst_id) or []
            if not any(x.get("tp_px") for x in ents):
                _state.setdefault("positions", {})[inst_id] = [{
                    "side": None, "qty": live_sz, "manual": True}]
                save_state(_state)
                log.info("%s 에 직접 들어간 포지션이 있어서 봇 진입 안 함", inst_id)
                return

    with _state_lock:
        if check_daily_sl_limit():
            log.info("오늘 손실 한도 도달로 신규 진입 스킵: %s", inst_id)
            return
        if symbol_sl_blocked(inst_id):
            log.info("%s 오늘 손절 %d회라 이 종목 진입 스킵", inst_id, MAX_SYMBOL_DAILY_SL)
            return

        # 봇 포지션 개수 제한 (전체 / 같은 방향)
        bot_open = [x for i, ents in _state.get("positions", {}).items() if i != inst_id
                    for x in (ents or [])[:1]
                    if not x.get("manual") and (x.get("tp_px") or x.get("pending"))]
        if MAX_BOT_POSITIONS and len(bot_open) >= MAX_BOT_POSITIONS:
            log.info("%s 봇 포지션 %d개로 최대(%d개)라 진입 스킵", inst_id, len(bot_open), MAX_BOT_POSITIONS)
            return
        same = sum(1 for x in bot_open if x.get("side") == side)
        if MAX_SAME_SIDE and same >= MAX_SAME_SIDE:
            log.info("%s 같은 방향(%s) 포지션 %d개로 최대(%d개)라 진입 스킵", inst_id,
                     "숏" if side == "S" else "롱", same, MAX_SAME_SIDE)
            return

        max_stack = SYMBOL_MAX_STACK_OVERRIDE.get(inst_id, MAX_STACK_POSITIONS)
        positions: dict = _state.setdefault("positions", {})
        entries = positions.setdefault(inst_id, [])

        # 반대 방향 신호는 단방향 모드에서 기존 포지션을 상쇄시키므로 스킵
        if entries and entries[0].get("side") != side:
            log.info("%s 반대 방향 신호라 진입 스킵 — 기존 포지션 보호", inst_id)
            return
        if len(entries) >= max_stack:
            log.info("%s 이미 포지션 %d개 보유 중(한도 %d개)이라 진입 스킵", inst_id, len(entries), max_stack)
            return

        # 자리 예약 (동시에 같은 종목 신호가 와도 중복 진입 방지)
        pending_entry = {"side": side, "qty": None, "entry": None, "pending": True,
                         "source": source, "opened_at": int(time.time() * 1000)}
        entries.append(pending_entry)
        save_state(_state)

    def _release():
        with _state_lock:
            ents = _state.setdefault("positions", {}).get(inst_id, [])
            if pending_entry in ents:
                ents.remove(pending_entry)
            save_state(_state)
            return get_trade_stats()

    # 방향별 배율 적용 (가격 기준 익절·손절 거리는 그대로 유지)
    forced = LONG_LEVERAGE if side == "L" else SHORT_LEVERAGE
    if forced and forced != leverage:
        tp_pct = tp_pct * forced / leverage
        sl_pct = sl_pct * forced / leverage
        leverage = forced
    base_margin = margin if margin else MARGIN_USDT
    if side == "L" and source in LONG_MARGIN_OVERRIDE:
        base_margin = LONG_MARGIN_OVERRIDE[source]
    notional = SYMBOL_MARGIN_OVERRIDE.get(inst_id, base_margin) * leverage
    try:
        ref_price = _executor.get_mark_price(inst_id)
        qty = _executor.open_position(inst_id, side, notional, ref_price,
                                      leverage, tp_pct, sl_pct)
    except Exception as e:  # noqa: BLE001
        stats = _release()
        log.warning("%s 진입 중 예외 발생: %s", inst_id, e)
        notify("⚠️ 진입 실패 (OKX)",
               f"📊 종목: {inst_id}\n❗ 사유: {format_okx_error(e)}\n━━━━━━━━━━\n"
               f"📈 오늘 성공: {stats['success']}회 / 실패: {stats['fail']}회")
        return

    if not qty:
        stats = _release()
        log.warning("%s 진입 실패", inst_id)
        notify("⚠️ 진입 실패 (OKX)",
               f"📊 종목: {inst_id}\n━━━━━━━━━━\n"
               f"📈 오늘 성공: {stats['success']}회 / 실패: {stats['fail']}회")
        return

    with _state_lock:
        pending_entry["qty"] = qty
        pending_entry["entry"] = ref_price
        if side == "S":
            pending_entry["tp_px"] = ref_price * (1 - tp_pct / leverage)
        else:
            pending_entry["tp_px"] = ref_price * (1 + tp_pct / leverage)
        pending_entry["be_done"] = False
        pending_entry["partial_done"] = False
        pending_entry["step_done"] = False
        pending_entry["margin"] = round(notional / leverage, 2)
        pending_entry["leverage"] = leverage
        pending_entry["tp_pct_px"] = round(tp_pct / leverage, 5)   # 가격 기준 익절 거리
        pending_entry["sl_pct_px"] = round(sl_pct / leverage, 5)   # 가격 기준 손절 거리
        pending_entry.pop("pending", None)
        save_state(_state)
        stats = record_trade_result(True)

    label = "🔴 숏" if side == "S" else "🟢 롱"
    notify("🚀 신규 진입 (OKX)",
           f"{label} 진입 완료 · {source}\n━━━━━━━━━━\n📊 종목: {inst_id}\n📦 수량: {qty}\n"
           f"💰 진입가: {ref_price}\n━━━━━━━━━━\n"
           f"📈 오늘 성공: {stats['success']}회 / 실패: {stats['fail']}회")


# ----------------------------------------------------------------------------
# zetro 신호 조회 루프
# ----------------------------------------------------------------------------

def _zetro_signal_key(sig: dict) -> str:
    return f"{sig.get('symbol')}|{sig.get('type')}|{sig.get('tf')}|{sig.get('at')}|{sig.get('side')}"


def _match_rule(sig: dict) -> Optional[str]:
    t = str(sig.get("type", "")).lower()
    k = str(sig.get("kind", "")).lower()
    for name, rule in ZETRO_SIGNAL_RULES.items():
        if t != rule["type"]:
            continue
        if rule["kinds"] and k not in rule["kinds"]:
            continue
        return name
    return None


def _plain_symbol(sym: str) -> str:
    """'BTC-USDT-SWAP', 'BTCUSDT.P' 등을 'BTCUSDT'로."""
    return normalize_symbol(sym).replace("-SWAP", "").replace("-", "")


def _zetro_fetch() -> list:
    params = {}
    resp = requests.get(ZETRO_SIGNALS_URL,
                        headers={"Authorization": f"Bearer {ZETRO_API_KEY}"},
                        params=params, timeout=10)
    if resp.status_code != 200:
        raise RuntimeError(f"zetro 응답 {resp.status_code}: {resp.text[:200]}")
    return resp.json().get("items", []) or []


def zetro_log_types() -> None:
    """시작할 때 zetro 신호 종류 목록을 한 번 받아서 로그에 남김 (type 이름 확인용)."""
    try:
        resp = requests.get(ZETRO_SIGNALS_URL.replace("/signals", "/types"),
                            headers={"Authorization": f"Bearer {ZETRO_API_KEY}"}, timeout=10)
        log.info("zetro 신호 종류 목록(%s): %s", resp.status_code, resp.text[:3000])
    except Exception as e:  # noqa: BLE001
        log.info("zetro 신호 종류 목록 조회 실패(무시): %s", e)


def zetro_poll_loop():
    zetro_log_types()
    with _state_lock:
        seen_list = _state.setdefault("zetro_seen", [])
    seen = set(seen_list)
    first_run = not seen   # 처음 켰을 때 이미 떠 있던 신호는 기록만 하고 진입 안 함
    error_streak = 0

    log.info("zetro 신호 조회 시작 (%s초 간격, API 진입: %s)", ZETRO_POLL_SECONDS,
             "ON" if ZETRO_API_ENTRY_ENABLED else "OFF(기록만)")

    while True:
        try:
            items = _zetro_fetch()
            if error_streak >= 3:
                notify("✅ zetro 연결 복구", "신호 조회가 다시 정상 작동합니다.")
            error_streak = 0
            now_ms = time.time() * 1000
            new_keys = []

            for sig in sorted(items, key=lambda s: s.get("at") or 0):
                key = _zetro_signal_key(sig)
                if key in seen:
                    continue   # 같은 신호로 두 번 진입 안 함
                seen.add(key)
                new_keys.append(key)

                if first_run:
                    continue

                sig_type = str(sig.get("type", ""))
                tf = str(sig.get("tf", ""))
                side = str(sig.get("side", "")).lower()
                symbol = sig.get("symbol", "")
                at = sig.get("at") or 0

                log.info("zetro 새 신호: %s %s type=%s tf=%s | 원본=%s", symbol, side, sig_type, tf,
                         json.dumps(sig, ensure_ascii=False)[:500])

                rule_name = _match_rule(sig)
                if not rule_name:
                    continue   # 정한 신호가 아니면 진입 안 함
                rule = ZETRO_SIGNAL_RULES[rule_name]
                if rule["symbols"] and _plain_symbol(symbol) not in rule["symbols"]:
                    log.info("%s 신호는 %s 종목 진입 안 함: %s", rule_name, symbol, sig)
                    continue
                if rule.get("tfs") and tf.lower() not in rule["tfs"]:
                    log.info("%s 신호가 %s봉이라 진입 안 함 (5분봉만): %s", rule_name, tf, sig)
                    continue
                if side not in ("long", "short") or not symbol:
                    log.info("zetro 신호 형식 불명확(스킵): %s", sig)
                    continue
                age_sec = (now_ms - at) / 1000 if at else None
                if age_sec is None or age_sec > rule["max_age_sec"]:
                    log.info("%s 신호가 %s초 지나서 스킵: %s", rule_name,
                             f"{age_sec:.0f}" if age_sec is not None else "?", sig)
                    continue

                inst_id = normalize_symbol(symbol)
                try:
                    vol_usd = _executor.get_24h_volume_usd(inst_id)
                except Exception as e:  # noqa: BLE001
                    log.info("%s 거래대금 조회 실패(OKX에 없는 종목일 수 있음) — 진입 안 함: %s", inst_id, format_okx_error(e))
                    continue
                if vol_usd < MIN_24H_VOLUME_USD:
                    log.info("%s 24시간 거래대금 $%s < $%s 이라 진입 안 함", inst_id,
                             f"{vol_usd:,.0f}", f"{MIN_24H_VOLUME_USD:,.0f}")
                    continue

                if not ZETRO_API_ENTRY_ENABLED or not rule.get("api_entry"):
                    log.info("API 진입 꺼짐 — %s %s %s 신호 기록만 함", rule_name, symbol, side)
                    continue

                log.info("zetro %s 신호로 진입 시도: %s %s (%s)", rule_name, symbol, side, tf)
                try:
                    enter_position(symbol, side, rule.get("leverage", LEVERAGE),
                                   rule.get("tp_pct", TAKE_PROFIT_PCT), rule.get("sl_pct", STOP_LOSS_PCT),
                                   source=rule_name)
                except Exception as e:  # noqa: BLE001
                    log.error("zetro 신호 진입 처리 실패: %s", e)

            first_run = False
            if new_keys:
                with _state_lock:
                    seen_list = _state.setdefault("zetro_seen", [])
                    seen_list.extend(new_keys)
                    if len(seen_list) > 2000:
                        del seen_list[:-2000]
                        seen.intersection_update(seen_list)
                    save_state(_state)
        except Exception as e:  # noqa: BLE001
            error_streak += 1
            log.warning("zetro 신호 조회 실패(%d회 연속): %s", error_streak, e)
            if error_streak == 3:
                notify("⚠️ zetro 신호 조회 실패", f"3회 연속 실패\n사유: {str(e)[:200]}")
        time.sleep(ZETRO_POLL_SECONDS)


# ----------------------------------------------------------------------------
# zetro 스크리너 조회 루프
# ----------------------------------------------------------------------------

def _collect_screener_ids(obj, out: set, under_screener: bool = False) -> None:
    """/types 응답에서 'screener' 칸 아래에 있는 조건 id들을 모음."""
    if isinstance(obj, dict):
        for k, v in obj.items():
            flag = under_screener or str(k).lower() == "screener"
            if flag and str(k).lower() in ("id", "screener") and isinstance(v, str):
                out.add(v)
            _collect_screener_ids(v, out, flag)
    elif isinstance(obj, list):
        for v in obj:
            if under_screener and isinstance(v, str):
                out.add(v)
            _collect_screener_ids(v, out, under_screener)


def resolve_screener_ids() -> None:
    try:
        resp = requests.get(ZETRO_SIGNALS_URL.replace("/signals", "/types"),
                            headers={"Authorization": f"Bearer {ZETRO_API_KEY}"}, timeout=10)
        data = resp.json()
    except Exception as e:  # noqa: BLE001
        log.warning("스크리너 조건 목록 조회 실패: %s", e)
        data = {}
    ids: set = set()
    _collect_screener_ids(data, ids)
    log.info("스크리너 조건 id 목록: %s", ", ".join(sorted(ids)) or "(못 찾음)")
    for name, rule in SCREENER_RULES.items():
        if rule.get("id"):
            continue
        matches = sorted(i for i in ids if rule["find"].lower() in i.lower())
        # 롱/숏이 따로 있어도 같이 받도록 쉼표로 묶음 (최대 4개)
        rule["id"] = ",".join(matches[:4]) if matches else rule["find"]
        log.info("스크리너 %s 조건 id = %s%s", name, rule["id"], "" if matches else " (목록에 없어 기본값 사용)")


def _screener_fetch(cond_id: str, tf: str) -> list:
    params = {"type": cond_id, "tf": tf, "limit": "100", **SCREENER_FILTERS}
    resp = requests.get(ZETRO_SCREENER_URL, headers={"Authorization": f"Bearer {ZETRO_API_KEY}"},
                        params=params, timeout=10)
    if resp.status_code != 200:
        raise RuntimeError(f"스크리너 응답 {resp.status_code}: {resp.text[:200]}")
    return resp.json().get("items", []) or []


def screener_poll_loop():
    resolve_screener_ids()
    with _state_lock:
        seen_list = _state.setdefault("screener_seen", [])
    seen = set(seen_list)
    first_run = {name: True for name in SCREENER_RULES}
    error_streak = 0
    log.info("스크리너 조회 시작 (%s초 간격, 필터: %s)", SCREENER_POLL_SECONDS, SCREENER_FILTERS)

    while True:
        try:
            new_keys = []
            now_ms = time.time() * 1000
            for name, rule in SCREENER_RULES.items():
                items = _screener_fetch(rule["id"], rule["tf"])
                for it in sorted(items, key=lambda x: x.get("at") or 0):
                    symbol = str(it.get("symbol", "")).upper()
                    side = str(it.get("side", "")).lower()
                    at = it.get("at") or 0
                    key = f"{name}|{symbol}|{it.get('kind')}|{it.get('tf')}|{at}"
                    if key in seen:
                        continue
                    seen.add(key)
                    new_keys.append(key)
                    if first_run[name]:
                        continue   # 봇 켤 때 이미 떠 있던 건 진입 안 함

                    log.info("스크리너 %s 새 종목: %s %s | 원본=%s", name, symbol, side,
                             json.dumps(it, ensure_ascii=False)[:400])
                    if rule.get("kinds") and str(it.get("kind", "")).lower() not in rule["kinds"]:
                        log.info("스크리너 %s: %s kind=%s 라 진입 안 함", name, symbol, it.get("kind"))
                        continue
                    if rule["symbols"] and symbol not in rule["symbols"]:
                        continue
                    if side not in ("long", "short") or not symbol:
                        continue
                    age = (now_ms - at) / 1000 if at else None
                    if age is None or age > rule["max_age_sec"]:
                        log.info("스크리너 %s: %s 뜬 지 %s초라 진입 안 함", name, symbol,
                                 f"{age:.0f}" if age is not None else "?")
                        continue
                    if not SCREENER_ENTRY_ENABLED:
                        log.info("스크리너 진입 꺼짐 — %s %s %s 기록만 함", name, symbol, side)
                        continue
                    log.info("스크리너 %s 신호로 진입 시도: %s %s", name, symbol, side)
                    try:
                        enter_position(symbol, side, rule["leverage"], rule["tp_pct"], rule["sl_pct"],
                                       source=name, margin=rule.get("margin"))
                    except Exception as e:  # noqa: BLE001
                        log.error("스크리너 진입 처리 실패: %s", e)
                first_run[name] = False

            if new_keys:
                with _state_lock:
                    seen_list = _state.setdefault("screener_seen", [])
                    seen_list.extend(new_keys)
                    if len(seen_list) > 2000:
                        del seen_list[:-2000]
                        seen.intersection_update(seen_list)
                    save_state(_state)
            if error_streak >= 3:
                notify("✅ 스크리너 연결 복구", "스크리너 조회가 다시 정상 작동합니다.")
            error_streak = 0
        except Exception as e:  # noqa: BLE001
            error_streak += 1
            log.warning("스크리너 조회 실패(%d회 연속): %s", error_streak, e)
            if error_streak == 3:
                notify("⚠️ 스크리너 조회 실패", f"3회 연속 실패\n사유: {str(e)[:200]}")
        time.sleep(SCREENER_POLL_SECONDS)


# ----------------------------------------------------------------------------
# zetro 웹훅 신호 처리
# ----------------------------------------------------------------------------

_hook_lock = threading.Lock()


def _hook_side(p: dict) -> Optional[str]:
    v = str(p.get("side", "")).lower().strip()
    if v in ("up", "long", "buy", "롱", "매수"):
        return "long"
    if v in ("down", "short", "sell", "숏", "매도"):
        return "short"
    return None


def _hook_age_sec(p: dict) -> Optional[float]:
    t = str(p.get("time", "")).strip()
    if not t:
        return None
    try:
        if t.isdigit():
            ts = int(t) / (1000 if len(t) > 10 else 1)
        else:
            ts = datetime.fromisoformat(t.replace("Z", "+00:00")).timestamp()
        return time.time() - ts
    except Exception:  # noqa: BLE001
        return None


def handle_zetro_hook(text: str) -> None:
    try:
        payload = json.loads(text)
    except Exception:  # noqa: BLE001
        log.info("웹훅 내용이 JSON이 아니라 무시 (zetro 알림 메시지 칸 확인 필요): %s", text[:200])
        return

    rule_name = str(payload.get("rule", "")).strip()
    rule = HOOK_RULES.get(rule_name)
    if rule is not None and not rule.get("enabled", True):
        log.info("웹훅 %s: 이 신호는 꺼져 있어서 진입 안 함", rule_name)
        return
    if not rule:
        log.info("웹훅: 진입 규칙에 없는 알림이라 무시 (rule=%s)", rule_name or "-")
        return

    ticker = str(payload.get("ticker", "")).upper().strip()
    symbol = ticker if ticker.endswith("USDT") else f"{ticker}USDT"
    side = _hook_side(payload)
    interval = re.sub(r"[^0-9]", "", str(payload.get("interval", "")))   # "5", "5m", "5분" → "5"
    age = _hook_age_sec(payload)

    if not ticker or not side:
        log.info("웹훅: 종목/방향을 알 수 없어 무시: %s", text[:300])
        return
    if rule.get("sides") and side not in rule["sides"]:
        log.info("웹훅 %s: %s 방향이라 진입 안 함", rule_name, side)
        return
    if rule["intervals"] and interval not in rule["intervals"]:
        log.info("웹훅 %s: %s봉이라 무시 (5분봉만)", rule_name, interval)
        return
    if rule["symbols"] and symbol not in rule["symbols"]:
        log.info("웹훅 %s: %s 종목은 진입 안 함", rule_name, symbol)
        return
    if age is not None and age > rule["max_age_sec"]:
        log.info("웹훅 %s: %s 신호가 %.0f초 지나서 무시", rule_name, symbol, age)
        return

    # 같은 신호 중복 진입 방지
    key = str(payload.get("id") or f"{rule_name}|{symbol}|{side}|{payload.get('time')}")
    with _hook_lock:
        with _state_lock:
            seen = _state.setdefault("hook_seen", [])
            if key in seen:
                log.info("웹훅: 이미 처리한 신호라 무시 (%s)", key)
                return
            seen.append(key)
            if len(seen) > 2000:
                del seen[:-2000]
            save_state(_state)

    if not HOOK_ENTRY_ENABLED:
        log.info("웹훅 진입 꺼짐 — %s %s %s 기록만 함", rule_name, symbol, side)
        return

    inst_id = normalize_symbol(symbol)
    try:
        vol_usd = _executor.get_24h_volume_usd(inst_id)
    except Exception as e:  # noqa: BLE001
        log.info("웹훅 %s: %s 조회 실패(OKX에 없는 종목일 수 있음) — 진입 안 함: %s",
                 rule_name, inst_id, format_okx_error(e))
        return
    if vol_usd < MIN_24H_VOLUME_USD:
        log.info("웹훅 %s: %s OKX 24시간 거래대금 $%s 부족 — 진입 안 함", rule_name, inst_id, f"{vol_usd:,.0f}")
        return

    log.info("웹훅 %s 신호로 진입 시도: %s %s", rule_name, symbol, side)
    enter_position(symbol, side, rule["leverage"],
                   rule.get("tp_pct", TAKE_PROFIT_PCT), rule.get("sl_pct", STOP_LOSS_PCT),
                   source=HOOK_NAMES.get(rule_name, rule_name), margin=rule.get("margin"))


# ----------------------------------------------------------------------------
# 정기 리포트 / 익절·손절 감시
# ----------------------------------------------------------------------------

HEARTBEAT_MINUTES = 10   # 정기 리포트 주기(분)


def heartbeat_loop():
    time.sleep(20)   # 시작 직후 포지션 동기화가 끝나길 잠깐 기다렸다가 첫 리포트 전송
    while True:
        try:
            sync_transfers()
            recover_bot_positions()
            summary = _executor.get_account_summary()
            upl = summary["unrealized_pnl"]
            with _state_lock:
                ensure_daily_base(summary["usdt_balance"] - upl)
                journal_set_equity(summary["usdt_balance"] - upl, summary["usdt_balance"])
                _state["last_account"] = {"eq": round(summary["usdt_balance"], 2), "upl": round(upl, 2),
                                          "t": int(time.time() * 1000)}
            open_positions = _executor.get_open_positions()
            with _state_lock:
                st_pos = _state.get("positions", {})
                bot_upl = 0.0
                for p in open_positions:
                    ents = st_pos.get(p.get("instId")) or []
                    if ents and ents[0].get("tp_px") and not ents[0].get("manual"):
                        bot_upl += float(p.get("upl", 0) or 0)
                if _state.get("last_account"):
                    _state["last_account"]["bot_upl"] = round(bot_upl, 2)
            if open_positions:
                lines = []
                for p in open_positions:
                    pos_val = float(p.get("pos", 0))
                    p_pnl = float(p.get("upl", 0) or 0)
                    lines.append(
                        f"{'🟢 롱' if pos_val > 0 else '🔴 숏'} {p['instId']}\n"
                        f"   수량: {abs(pos_val)} | 손익: {p_pnl:+.2f} USDT"
                    )
                pos_text = "\n\n".join(lines)
            else:
                pos_text = "보유 포지션 없음"

            with _state_lock:
                wl = dict(_daily("daily_win_loss", {"win": 0, "loss": 0}))
                pnl_today = _daily("daily_pnl", {"total": 0.0})["total"]
                sl_count = _daily("daily_sl", {"count": 0})["count"]
                cum_text = format_cum_stats()
            with _state_lock:
                loss_now, loss_limit = daily_loss_info()
                stopped_flag = check_daily_sl_limit()
            stopped = "\n⛔ 오늘 손실 한도 도달 — 신규 진입 중지 중" if stopped_flag else ""
            if loss_limit is not None:
                room = loss_now + loss_limit
                stopped = (f"\n🧯 오늘 멈춤 기준: 손익 -{loss_limit:.2f} USDT 되면 중지"
                           f"\n    (지금 {loss_now:+.2f} → 앞으로 {max(room, 0):.2f} 더 잃으면 멈춤)") + stopped

            notify("📊 정기 리포트 (OKX)",
                   f"━━━━━━━━━━\n💰 USDT 잔고: {summary['usdt_balance']:.2f}\n"
                   f"{'📈' if upl >= 0 else '📉'} 미실현 손익: {upl:+.2f}\n━━━━━━━━━━\n"
                   f"🗓 오늘 성적 (한국시간 0시 기준)\n"
                   f"🏆 {wl['win']}승 {wl['loss']}패\n"
                   f"💵 당일 실현손익: {pnl_today:+.2f} USDT{stopped}\n━━━━━━━━━━\n"
                   f"{cum_text}\n━━━━━━━━━━\n\n"
                   f"📌 보유 포지션\n{pos_text}")
        except Exception as e:  # noqa: BLE001
            log.warning("하트비트 알림 실패: %s", e)
        time.sleep(HEARTBEAT_MINUTES * 60)


def manage_positions_loop():
    """봇이 진입한 포지션을 보면서 본절 손절·분할 익절을 처리."""
    log.info("포지션 관리 시작: 본절 +%.1f%% / 분할익절 +%.1f%%에서 %d%% 청산 / +%.1f%%에서 손절을 +%.1f%%로",
             BREAKEVEN_TRIGGER_PCT * 100, PARTIAL_TP_TRIGGER_PCT * 100, int(PARTIAL_TP_RATIO * 100),
             STEP_TRIGGER_PCT * 100, STEP_LOCK_PCT * 100)
    while True:
        time.sleep(MANAGE_POLL_SECONDS)
        if not MANAGE_ENABLED:
            continue
        try:
            live = {p["instId"]: p for p in _executor.get_open_positions()}
            with _state_lock:
                targets = []
                for inst_id, entries in _state.get("positions", {}).items():
                    if not entries or inst_id not in live:
                        continue
                    e = entries[0]
                    if e.get("manual") or not e.get("tp_px") or (e.get("be_done") and e.get("partial_done") and e.get("step_done")):
                        continue   # 봇이 진입한 게 아니거나(수동) 이미 다 처리함
                    targets.append((inst_id, e))

            for inst_id, e in targets:
                p = live[inst_id]
                side = e["side"]
                entry = float(p.get("avgPx") or e.get("entry") or 0)
                mark = float(p.get("markPx") or p.get("last") or 0)
                if not entry or not mark:
                    continue
                gain = (mark - entry) / entry if side == "L" else (entry - mark) / entry

                # 0) 시간 손절: 정해둔 시간 안에 본절까지도 못 가면 정리
                ts_min = TIME_STOP_MIN.get(e.get("source") or "")
                opened = e.get("opened_at") or 0
                if (ts_min and opened and not e.get("be_done") and not e.get("time_stopped")
                        and time.time() * 1000 - opened >= ts_min * 60_000):
                    pos_raw = str(p.get("pos") or "0").lstrip("-")
                    try:
                        old_algos = _executor.pending_tpsl_ids(inst_id)
                        _executor.close_partial(inst_id, side, pos_raw)
                        with _state_lock:
                            e["time_stopped"] = True
                            save_state(_state)
                        try:
                            _executor.cancel_algos(inst_id, old_algos)
                        except Exception:  # noqa: BLE001
                            pass   # 포지션이 닫히면 같이 사라지는 경우가 많음
                        log.info("%s 시간 손절: %d분 지나도 본절 못 감 → 정리 (현재 %+.2f%%)", inst_id, ts_min, gain * 100)
                        notify("⏰ 시간 손절 (OKX)",
                               f"📊 종목: {inst_id}{' · ' + e['source'] if e.get('source') else ''}\n"
                               f"{ts_min // 60}시간이 지나도 본절까지 못 가서 정리했어요.\n"
                               f"정리할 때 가격 변화: {gain * 100:+.2f}%")
                    except Exception as ex:  # noqa: BLE001
                        log.warning("%s 시간 손절 실패: %s", inst_id, format_okx_error(ex))
                    continue

                # 1) 본절 손절
                if not e.get("be_done") and gain >= BREAKEVEN_TRIGGER_PCT:
                    be_px = entry * (1 + BREAKEVEN_BUFFER_PCT) if side == "L" else entry * (1 - BREAKEVEN_BUFFER_PCT)
                    try:
                        _executor.replace_tpsl(inst_id, side, e["tp_px"], be_px)
                        with _state_lock:
                            e["be_done"] = True
                            save_state(_state)
                        log.info("%s 본절 손절 설정: 손절 → %s (현재 +%.2f%%)", inst_id, be_px, gain * 100)
                        notify("🛡 본절 손절 설정 (OKX)",
                               f"📊 종목: {inst_id}{' · ' + e['source'] if e.get('source') else ''}\n"
                               f"가격이 +{gain * 100:.2f}% 가서 손절을 진입가로 올렸어요.\n"
                               f"이제 다시 내려와도 손실 없이 끝나요.")
                    except Exception as ex:  # noqa: BLE001
                        log.warning("%s 본절 손절 설정 실패: %s", inst_id, format_okx_error(ex))

                # 2) 분할 익절
                if not e.get("partial_done") and gain >= PARTIAL_TP_TRIGGER_PCT:
                    pos_sz = abs(float(p.get("pos", 0) or 0))
                    sz = _executor.round_sz_down(inst_id, pos_sz * PARTIAL_TP_RATIO)
                    try:
                        if sz > 0 and sz < pos_sz:
                            _executor.close_partial(inst_id, side, sz)
                            log.info("%s 분할 익절: %s / %s 청산 (현재 +%.2f%%)", inst_id, sz, pos_sz, gain * 100)
                            ct_val = float(_executor.get_instrument(inst_id).get("ctVal", 1))
                            upl = gain * entry * sz * ct_val
                            notify("💰 분할 익절 (OKX)",
                                   f"📊 종목: {inst_id}{' · ' + e['source'] if e.get('source') else ''}\n"
                                   f"가격 +{gain * 100:.2f}%에서 {int(PARTIAL_TP_RATIO * 100)}% 청산 (약 {upl:+.2f} USDT)\n"
                                   f"나머지는 익절가까지 가져가요.")
                        else:
                            log.info("%s 수량이 너무 적어 분할 익절은 건너뜀", inst_id)
                        with _state_lock:
                            e["partial_done"] = True
                            save_state(_state)
                    except Exception as ex:  # noqa: BLE001
                        log.warning("%s 분할 익절 실패: %s", inst_id, format_okx_error(ex))

                # 3) 단계 손절: 수익 일부 확보 (최종 익절이 이 지점보다 가까우면 필요 없음)
                tp_dist = abs(e["tp_px"] - entry) / entry if entry else 0
                if not e.get("step_done") and tp_dist <= STEP_TRIGGER_PCT + 0.002:
                    with _state_lock:
                        e["step_done"] = True
                        save_state(_state)
                if not e.get("step_done") and gain >= STEP_TRIGGER_PCT:
                    lock_px = entry * (1 + STEP_LOCK_PCT) if side == "L" else entry * (1 - STEP_LOCK_PCT)
                    try:
                        _executor.replace_tpsl(inst_id, side, e["tp_px"], lock_px)
                        with _state_lock:
                            e["step_done"] = True
                            e["step_locked"] = True
                            e["be_done"] = True
                            save_state(_state)
                        log.info("%s 단계 손절: 손절 → %s (현재 +%.2f%%)", inst_id, lock_px, gain * 100)
                        notify("🔒 수익 확보 (OKX)",
                               f"📊 종목: {inst_id}{' · ' + e['source'] if e.get('source') else ''}\n"
                               f"가격이 +{gain * 100:.2f}% 가서 손절을 +{STEP_LOCK_PCT * 100:.1f}% 자리로 올렸어요.\n"
                               f"이제 돌아와도 수익을 챙기고 끝나요.")
                    except Exception as ex:  # noqa: BLE001
                        log.warning("%s 단계 손절 설정 실패: %s", inst_id, format_okx_error(ex))
        except Exception as ex:  # noqa: BLE001
            log.warning("포지션 관리 루프 오류: %s", ex)


def sl_watch_loop():
    while True:
        time.sleep(120)
        try:
            open_inst_ids = {p["instId"] for p in _executor.get_open_positions()}

            with _state_lock:
                positions_state: dict = _state.setdefault("positions", {})
                closed_inst_ids = [i for i, v in positions_state.items() if v and i not in open_inst_ids]

            for inst_id in closed_inst_ids:
                with _state_lock:
                    entries = _state.setdefault("positions", {}).get(inst_id) or []
                    has_real_entry = any(e.get("qty") for e in entries)
                    tracked = [e for e in entries if e.get("qty") and (e.get("opened_at") or 0) >= _stats_start_ms()]
                    source = (tracked[0].get("source") or "기타") if tracked else None
                    is_manual = bool(entries) and (entries[0].get("manual") or not entries[0].get("tp_px"))
                    if has_real_entry and is_manual:
                        _state["positions"][inst_id] = []
                        save_state(_state)
                        log.info("%s 수동 포지션 종료 — 성적·손절 횟수에 넣지 않음", inst_id)
                        continue
                    if not has_real_entry:
                        # 주문 진행 중인 예약 자리는 건드리지 않음
                        if not any(e.get("pending") for e in entries):
                            _state["positions"][inst_id] = []
                            save_state(_state)
                        continue

                with _state_lock:
                    j_entries = _state.get("positions", {}).get(inst_id) or []
                    j_source = (j_entries[0].get("source") if j_entries else None) or "기타"
                    j_side = j_entries[0].get("side") if j_entries else None
                    j0 = dict(j_entries[0]) if j_entries else {}
                hist = _executor._request("GET", "/api/v5/account/positions-history",
                                          params={"instId": inst_id, "limit": "1"})
                rows = hist.get("data", [])
                gross = float(rows[0].get("pnl", 0) or 0) if rows else 0.0
                # 실제 손익 = 수수료·펀딩비까지 반영된 realizedPnl (없으면 pnl)
                real_raw = rows[0].get("realizedPnl") if rows else None
                pnl = float(real_raw) if real_raw not in (None, "") else gross
                is_win = gross >= 0      # 익절/손절 판정은 수수료 빼기 전 기준 (본절이 손절로 잡히지 않게)
                # 한 달 뒤 분석용 상세 기록 (진입·청산가, 보유 시간, 관리 단계)
                r0 = rows[0] if rows else {}
                def _f(x):
                    try:
                        return float(x) if x not in (None, "") else None
                    except (TypeError, ValueError):
                        return None
                opened_ms = j0.get("opened_at") or (int(r0["cTime"]) if r0.get("cTime") else None)
                extra = {
                    "opened": opened_ms,
                    "hold_min": round((time.time() * 1000 - opened_ms) / 60000, 1) if opened_ms else None,
                    "entry": _f(r0.get("openAvgPx")) or j0.get("entry"),
                    "close": _f(r0.get("closeAvgPx")),
                    "gross": round(gross, 4),
                    "fee": _f(r0.get("fee")),
                    "funding": _f(r0.get("fundingFee")),
                    "margin": j0.get("margin"),
                    "lev": j0.get("leverage"),
                    "tp_px_pct": j0.get("tp_pct_px"),
                    "sl_px_pct": j0.get("sl_pct_px"),
                    "be": bool(j0.get("be_done")),
                    "partial": bool(j0.get("partial_done")),
                    "step": bool(j0.get("step_done")),
                    "time_stop": bool(j0.get("time_stopped")),
                }

                with _state_lock:
                    if not is_win:
                        record_sl_hit()
                        record_symbol_sl(inst_id)
                    win_loss = record_win_loss(is_win)
                    daily_pnl = record_daily_pnl(pnl)
                    close_kind = journal_record(inst_id, j_source, j_side, pnl,
                                                kind=classify_close(gross, rows[0] if rows else None),
                                                extra=extra)
                    maybe_notify_loss_limit()
                    if source:
                        record_cum_trade(source, pnl)
                    cum_text = format_cum_stats()
                    _state.setdefault("positions", {})[inst_id] = []
                    save_state(_state)

                if not is_win:
                    title = "🛑 손절"
                elif close_kind == "be":
                    title = "➖ 본절 종료 (분할 익절분 포함)" if pnl >= 1.0 else "➖ 본절 종료"
                else:
                    title = "✅ 익절"
                notify(f"{title} (OKX)",
                       f"📊 종목: {inst_id}{' · ' + source if source else ''}\n💰 손익: {pnl:+.2f} USDT\n━━━━━━━━━━\n"
                       f"🏆 오늘 {win_loss['win']}승 {win_loss['loss']}패\n"
                       f"💵 당일 실현손익: {daily_pnl['total']:+.2f} USDT\n━━━━━━━━━━\n"
                       f"{cum_text}")
        except Exception as e:  # noqa: BLE001
            log.warning("손절 감시 루프 오류: %s", e)


# ----------------------------------------------------------------------------
# Railway 상태 확인용 (주문 기능 없음, 접속하면 ok만 응답)
# ----------------------------------------------------------------------------

class HealthHandler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        pass

    @staticmethod
    def _safe_handle(text: str) -> None:
        try:
            handle_zetro_hook(text)
        except Exception as e:  # noqa: BLE001
            log.error("웹훅 처리 실패: %s", e)

    def do_POST(self):
        # zetro 웹훅 수신 → 응답은 바로 하고 진입 처리는 따로 진행
        length = int(self.headers.get("Content-Length", 0) or 0)
        raw = self.rfile.read(length) if length else b""
        path_only = self.path.split("?", 1)[0].rstrip("/")
        text = raw.decode("utf-8", errors="ignore")[:2000]
        if path_only == ZETRO_HOOK_PATH:
            log.info("zetro 웹훅 수신: %s", text)
            threading.Thread(target=self._safe_handle, args=(text,), daemon=True).start()
            code, body = 200, b'{"ok":true}'
        else:
            # 주소가 달라도 무엇이 왔는지 확인할 수 있게 기록
            log.info("웹훅 수신(주소 불일치) path=%s body=%s", self.path[:200], text[:500])
            code, body = 404, b""
        self.send_response(code)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        path_only = self.path.split("?", 1)[0].rstrip("/")
        if path_only == POSITIONS_PATH:
            body, ctype = render_positions_html(), "text/html; charset=utf-8"
        elif path_only == POSITIONS_PATH + "/data":
            try:
                body = json.dumps(positions_snapshot(), ensure_ascii=False).encode("utf-8")
                ctype = "application/json; charset=utf-8"
            except Exception as e:  # noqa: BLE001
                log.warning("실시간 포지션 조회 오류: %s", e)
                self.send_response(503)
                self.send_header("Content-Length", "0")
                self.end_headers()
                return
        elif path_only == REPORT_PATH + "/trades.csv":
            body, ctype = trades_csv(), "text/csv; charset=utf-8"
        elif path_only == REPORT_PATH + "/icon.png":
            body, ctype = REPORT_ICON_180, "image/png"
        elif path_only == REPORT_PATH + "/icon64.png":
            body, ctype = REPORT_ICON_64, "image/png"
        elif path_only == REPORT_PATH:
            try:
                body = render_report_html()
                ctype = "text/html; charset=utf-8"
            except Exception as e:  # noqa: BLE001
                log.warning("기록지 페이지 오류: %s", e)
                body, ctype = "기록지를 만드는 중 오류가 났어요".encode("utf-8"), "text/plain; charset=utf-8"
        else:
            body, ctype = b'{"ok":true}', "application/json"
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


def main():
    global _executor, _state

    api_key = os.environ.get("OKX_API_KEY", "")
    api_secret = os.environ.get("OKX_API_SECRET", "")
    passphrase = os.environ.get("OKX_API_PASSPHRASE", "")
    if not api_key or not api_secret or not passphrase:
        raise SystemExit("OKX_API_KEY / OKX_API_SECRET / OKX_API_PASSPHRASE 환경변수를 설정해야 합니다.")

    _executor = OkxExecutor(api_key=api_key, api_secret=api_secret, passphrase=passphrase)
    _state = load_state()
    reset_sl_on_new_commit()
    purge_excluded_sources()
    merge_split_sources()
    sync_positions_from_exchange()
    recover_bot_positions()
    purge_old_journal()
    wipe_day_once()
    seed_journal_today()

    log.info("상태 파일 위치: %s (%s)", STATE_FILE.resolve(),
             "Volume 사용 중 — 재배포해도 기록 유지" if os.environ.get("RAILWAY_VOLUME_MOUNT_PATH")
             else "Volume 없음 — 재배포하면 기록 초기화")
    if not os.environ.get("RAILWAY_VOLUME_MOUNT_PATH"):
        notify("⚠️ 저장 공간(Volume) 없음",
               "봇 기록이 재배포할 때마다 지워지고 있어요.\n"
               "Railway에서 서비스에 Volume을 붙이고 위치를 /data 로 해주세요.\n"
               "(열린 봇 포지션은 OKX 익절·손절 주문을 보고 최대한 되찾아요)")
    log.info("zetro OKX 봇 시작 | 증거금=%sUSDT 기본레버리지=%sx TP=+%.0f%% SL=-%.0f%%",
             MARGIN_USDT, LEVERAGE, TAKE_PROFIT_PCT * 100, STOP_LOSS_PCT * 100)

    threading.Thread(target=heartbeat_loop, daemon=True).start()
    threading.Thread(target=sl_watch_loop, daemon=True).start()
    threading.Thread(target=manage_positions_loop, daemon=True).start()
    threading.Thread(target=btc_guard_loop, daemon=True).start()
    threading.Thread(target=daily_close_loop, daemon=True).start()
    log.info("매매 기록지: %s", report_url())
    log.info("실시간 포지션: %s", report_url().replace(REPORT_PATH, POSITIONS_PATH))
    if ZETRO_API_KEY:
        threading.Thread(target=zetro_poll_loop, daemon=True).start()
        threading.Thread(target=screener_poll_loop, daemon=True).start()
    else:
        log.warning("ZETRO_API_KEY가 없어서 zetro 신호 조회는 꺼둔 상태로 시작합니다.")
        notify("⚠️ zetro 신호 조회 꺼짐", "Railway Variables에 ZETRO_API_KEY를 넣어주세요.")

    server = ThreadingHTTPServer(("0.0.0.0", PORT), HealthHandler)
    server.daemon_threads = True
    server.serve_forever()


if __name__ == "__main__":
    main()
