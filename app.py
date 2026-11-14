#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Wahm Pay — بوابة دفع ذاتية الاستضافة
Flask + SQLite، جاهزة للرفع على Render.com
"""

from __future__ import annotations

import hmac
import json
import logging
import os
import random
import re
import secrets
import sqlite3
import string
import threading
import time
from contextlib import contextmanager
from datetime import datetime, timedelta, timezone
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from functools import wraps
from typing import Any, Optional
from zoneinfo import ZoneInfo

import requests
from flask import (
    Flask,
    Response,
    flash,
    jsonify,
    redirect,
    render_template,
    request,
    session,
    url_for,
)
from werkzeug.middleware.proxy_fix import ProxyFix

try:
    from dotenv import load_dotenv

    load_dotenv()
except ImportError:
    pass

# ---------------------------------------------------------------------------
# Constants (easy to change)
# ---------------------------------------------------------------------------

GEMINI_MODEL = "gemini-2.0-flash"
GEMINI_API_URL = (
    "https://generativelanguage.googleapis.com/v1beta/models/"
    f"{GEMINI_MODEL}:generateContent"
)

RIYADH_TZ = ZoneInfo("Asia/Riyadh")
UTC = timezone.utc

TOKEN_PREFIX = "PAY-"
TOKEN_ALPHABET = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
TOKEN_LENGTH = 5

STATUS_PENDING = "Pending"
STATUS_PAID = "Paid"
STATUS_EXPIRED = "Expired"

LOGIN_MAX_ATTEMPTS = 8
LOGIN_WINDOW_SECONDS = 300

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
)
log = logging.getLogger("wahm-pay")

# ---------------------------------------------------------------------------
# App & config
# ---------------------------------------------------------------------------

app = Flask(__name__)
app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1)


def _env(name: str, default: Optional[str] = None) -> Optional[str]:
    value = os.environ.get(name)
    if value is None:
        return default
    value = value.strip()
    return value if value else default


def _required_env_or_empty(name: str) -> str:
    return _env(name, "") or ""


FLASK_SECRET = _env("FLASK_SECRET_KEY")
if not FLASK_SECRET:
    FLASK_SECRET = secrets.token_hex(32)
    log.warning(
        "FLASK_SECRET_KEY is not set; using a random key. "
        "Sessions will reset on every restart."
    )
app.secret_key = FLASK_SECRET
app.config["SESSION_COOKIE_HTTPONLY"] = True
app.config["SESSION_COOKIE_SAMESITE"] = "Lax"
app.config["SESSION_COOKIE_NAME"] = "wahm_pay_session"
app.config["PERMANENT_SESSION_LIFETIME"] = timedelta(days=7)
app.config["MAX_CONTENT_LENGTH"] = 1 * 1024 * 1024  # 1 MB

# Persistent disk on Render should be mounted and pointed here.
_DEFAULT_DB = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data", "payments.db")
DATABASE_PATH = os.path.abspath(_env("DATABASE_PATH", _DEFAULT_DB) or _DEFAULT_DB)

ADMIN_PASSWORD = _required_env_or_empty("ADMIN_PASSWORD")
API_SECRET_KEY = _required_env_or_empty("SECRET_KEY")
GEMINI_API_KEY = _required_env_or_empty("GEMINI_API_KEY")
TELEGRAM_BOT_TOKEN = _required_env_or_empty("TELEGRAM_BOT_TOKEN")
TELEGRAM_CHAT_ID = _required_env_or_empty("TELEGRAM_CHAT_ID")
MERCHANT_IBAN = _required_env_or_empty("MERCHANT_IBAN")
MERCHANT_NAME = _env("MERCHANT_NAME", "التاجر") or "التاجر"
BASE_URL = (_env("BASE_URL", "") or "").rstrip("/")

try:
    INVOICE_VALIDITY_MINUTES = max(1, int(_env("INVOICE_VALIDITY_MINUTES", "15") or "15"))
except ValueError:
    INVOICE_VALIDITY_MINUTES = 15

# Test-only hooks (never set in production):
# SMOKE_TEST_GEMINI_JSON = raw JSON text
# SMOKE_TEST_GEMINI_FILE = path to a JSON file (read at call time)

_db_lock = threading.Lock()
_login_attempts: dict[str, list[float]] = {}
_login_lock = threading.Lock()

# ---------------------------------------------------------------------------
# Time helpers
# ---------------------------------------------------------------------------


def utcnow() -> datetime:
    return datetime.now(UTC)


def to_iso(dt: Optional[datetime]) -> Optional[str]:
    if dt is None:
        return None
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=UTC)
    return dt.astimezone(UTC).isoformat().replace("+00:00", "Z")


def parse_iso(value: Optional[str]) -> Optional[datetime]:
    if not value:
        return None
    text = value.strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    try:
        dt = datetime.fromisoformat(text)
    except ValueError:
        return None
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=UTC)
    return dt


def format_riyadh(dt: Optional[datetime]) -> str:
    if dt is None:
        return "—"
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=UTC)
    return dt.astimezone(RIYADH_TZ).strftime("%Y-%m-%d %H:%M:%S")


# ---------------------------------------------------------------------------
# Money helpers (store as integer halalas to avoid float errors)
# ---------------------------------------------------------------------------

ARABIC_DIGITS = str.maketrans("٠١٢٣٤٥٦٧٨٩٫٬", "0123456789.,")
HALALA_QUANT = Decimal("0.01")


def to_halalas(value: Any) -> int:
    """Convert a SAR amount (str/int/float/Decimal) to integer halalas."""
    if isinstance(value, int) and not isinstance(value, bool):
        # Ambiguous if someone passes already-halalas; treat ints as whole SAR
        # only when used from price fields. Prefer string/Decimal from APIs.
        return value * 100
    text = str(value).strip().translate(ARABIC_DIGITS).replace(",", "")
    text = re.sub(r"[^\d.\-]", "", text)
    if not text or text in {".", "-", "-."}:
        raise ValueError("مبلغ غير صالح")
    try:
        amount = Decimal(text)
    except InvalidOperation as exc:
        raise ValueError("مبلغ غير صالح") from exc
    if amount < 0:
        raise ValueError("المبلغ لا يمكن أن يكون سالباً")
    quantized = amount.quantize(HALALA_QUANT, rounding=ROUND_HALF_UP)
    return int(quantized * 100)


def parse_amount_to_halalas(value: Any) -> int:
    """Parse an exact amount that may already include halalas (50.14 -> 5014)."""
    text = str(value).strip().translate(ARABIC_DIGITS).replace(",", "")
    text = re.sub(r"[^\d.\-]", "", text)
    if not text or text in {".", "-", "-."}:
        raise ValueError("مبلغ غير صالح")
    try:
        amount = Decimal(text)
    except InvalidOperation as exc:
        raise ValueError("مبلغ غير صالح") from exc
    if amount < 0:
        raise ValueError("المبلغ لا يمكن أن يكون سالباً")
    quantized = amount.quantize(HALALA_QUANT, rounding=ROUND_HALF_UP)
    return int((quantized * 100).to_integral_value(rounding=ROUND_HALF_UP))


def halalas_to_str(halalas: int) -> str:
    return f"{halalas / 100:.2f}"


# ---------------------------------------------------------------------------
# Database
# ---------------------------------------------------------------------------


def _connect() -> sqlite3.Connection:
    os.makedirs(os.path.dirname(DATABASE_PATH), exist_ok=True)
    conn = sqlite3.connect(DATABASE_PATH, timeout=30, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    conn.execute("PRAGMA journal_mode = WAL")
    conn.execute("PRAGMA busy_timeout = 5000")
    return conn


@contextmanager
def get_db():
    with _db_lock:
        conn = _connect()
        try:
            yield conn
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            conn.close()


def init_db() -> None:
    with get_db() as conn:
        conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS invoices (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                token TEXT NOT NULL UNIQUE,
                product_name TEXT NOT NULL,
                base_price_halalas INTEGER NOT NULL,
                required_amount_halalas INTEGER NOT NULL,
                redirect_url TEXT,
                status TEXT NOT NULL DEFAULT 'Pending',
                created_at TEXT NOT NULL,
                expires_at TEXT NOT NULL,
                paid_at TEXT,
                sender_name TEXT,
                bank_name TEXT,
                reference TEXT,
                transfer_amount_halalas INTEGER,
                raw_sms TEXT
            );

            CREATE INDEX IF NOT EXISTS idx_invoices_status ON invoices(status);
            CREATE INDEX IF NOT EXISTS idx_invoices_amount_status
                ON invoices(required_amount_halalas, status);
            CREATE INDEX IF NOT EXISTS idx_invoices_created ON invoices(created_at);

            CREATE TABLE IF NOT EXISTS unmatched_deposits (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                amount_halalas INTEGER,
                sender_name TEXT,
                bank_name TEXT,
                reference TEXT,
                raw_sms TEXT,
                reason TEXT,
                created_at TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS webhook_logs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                received_at TEXT NOT NULL,
                raw_text TEXT,
                parsed_json TEXT,
                result TEXT,
                invoice_token TEXT,
                detail TEXT
            );
            """
        )
    log.info("Database ready at %s", DATABASE_PATH)


def row_to_dict(row: Optional[sqlite3.Row]) -> Optional[dict]:
    if row is None:
        return None
    return dict(row)


def expire_stale_invoices(conn: sqlite3.Connection) -> int:
    now = to_iso(utcnow())
    cur = conn.execute(
        """
        UPDATE invoices
           SET status = ?
         WHERE status = ?
           AND expires_at <= ?
        """,
        (STATUS_EXPIRED, STATUS_PENDING, now),
    )
    return cur.rowcount or 0


# ---------------------------------------------------------------------------
# Token & unique-halala generator
# ---------------------------------------------------------------------------


def generate_token(conn: sqlite3.Connection) -> str:
    for _ in range(40):
        suffix = "".join(secrets.choice(TOKEN_ALPHABET) for _ in range(TOKEN_LENGTH))
        token = f"{TOKEN_PREFIX}{suffix}"
        exists = conn.execute(
            "SELECT 1 FROM invoices WHERE token = ?", (token,)
        ).fetchone()
        if not exists:
            return token
    raise RuntimeError("تعذر توليد توكن فريد")


def generate_unique_amount(conn: sqlite3.Connection, base_halalas: int) -> int:
    """
    Add a unique random halala suffix (0.01–0.99) so concurrent Pending
    invoices never share the exact required amount.
    """
    expire_stale_invoices(conn)
    rows = conn.execute(
        """
        SELECT required_amount_halalas
          FROM invoices
         WHERE status = ?
        """,
        (STATUS_PENDING,),
    ).fetchall()
    used = {int(r["required_amount_halalas"]) for r in rows}

    suffixes = list(range(1, 100))  # 0.01 .. 0.99
    random.SystemRandom().shuffle(suffixes)
    for suffix in suffixes:
        amount = base_halalas + suffix
        if amount not in used:
            return amount

    raise RuntimeError(
        "جميع الهللات مستخدمة حالياً لفواتير معلّقة بنفس النطاق. "
        "انتظر انتهاء بعض الفواتير أو ألغِ القديمة ثم أعد المحاولة."
    )


# ---------------------------------------------------------------------------
# Auth helpers
# ---------------------------------------------------------------------------


def _client_ip() -> str:
    return (request.headers.get("X-Forwarded-For") or request.remote_addr or "unknown").split(",")[0].strip()


def _login_allowed(ip: str) -> bool:
    now = time.time()
    with _login_lock:
        stamps = [t for t in _login_attempts.get(ip, []) if now - t < LOGIN_WINDOW_SECONDS]
        _login_attempts[ip] = stamps
        return len(stamps) < LOGIN_MAX_ATTEMPTS


def _record_login_failure(ip: str) -> None:
    with _login_lock:
        _login_attempts.setdefault(ip, []).append(time.time())


def _clear_login_failures(ip: str) -> None:
    with _login_lock:
        _login_attempts.pop(ip, None)


def csrf_token() -> str:
    token = session.get("_csrf")
    if not token:
        token = secrets.token_urlsafe(32)
        session["_csrf"] = token
    return token


def validate_csrf() -> bool:
    sent = request.form.get("csrf_token") or request.headers.get("X-CSRF-Token") or ""
    expected = session.get("_csrf") or ""
    if not expected or not sent:
        return False
    return hmac.compare_digest(str(expected), str(sent))


def admin_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        if not session.get("admin"):
            if request.path.startswith("/api/"):
                return jsonify({"ok": False, "error": "غير مصرح"}), 401
            return redirect(url_for("login", next=request.path))
        return view(*args, **kwargs)

    return wrapped


def _extract_provided_secret() -> str:
    header = (
        request.headers.get("X-Secret-Key")
        or request.headers.get("X-Api-Key")
        or request.headers.get("X-Webhook-Secret")
        or ""
    ).strip()
    if header:
        return header
    auth = (request.headers.get("Authorization") or "").strip()
    if auth.lower().startswith("bearer "):
        return auth[7:].strip()
    if request.is_json:
        body = request.get_json(silent=True) or {}
        for key in ("secret", "secret_key", "SECRET_KEY", "key"):
            if body.get(key):
                return str(body.get(key)).strip()
    if request.form:
        for key in ("secret", "secret_key", "SECRET_KEY", "key"):
            if request.form.get(key):
                return str(request.form.get(key)).strip()
    if request.args.get("secret"):
        return str(request.args.get("secret")).strip()
    return ""


def require_api_secret() -> Optional[Response]:
    if not API_SECRET_KEY:
        log.error("SECRET_KEY is not configured; refusing protected request")
        return jsonify({"ok": False, "error": "الخادم غير مُعدّ: SECRET_KEY"}), 503
    provided = _extract_provided_secret()
    if not provided or not hmac.compare_digest(API_SECRET_KEY, provided):
        return jsonify({"ok": False, "error": "مفتاح سري غير صالح"}), 401
    return None


def public_base_url() -> str:
    if BASE_URL:
        return BASE_URL
    return request.url_root.rstrip("/")


def payment_link(token: str) -> str:
    return f"{public_base_url()}/pay/{token}"


# ---------------------------------------------------------------------------
# Gemini verification
# ---------------------------------------------------------------------------

GEMINI_PROMPT = """أنت محلل رسائل بنكية. استخرج بيانات الحوالة الواردة (إيداع / تحويل مستلم) من نص الرسالة التالية.
أرجع JSON صالحاً فقط بدون أي شرح أو علامات markdown، بهذا الشكل تماماً:
{{
  "is_valid_deposit": true,
  "amount": 50.14,
  "sender_name": "اسم المرسل أو null",
  "bank_name": "اسم البنك أو null",
  "reference": "رقم المرجع أو null"
}}

القواعد:
- is_valid_deposit = true فقط إذا كانت الرسالة تؤكد استلام مبلغ (إيداع أو حوالة واردة ناجحة).
- اجعلها false للسحوبات، وكلمات السر، والإعلانات، والحوالات الفاشلة، وأي شيء ليس إيداعاً مؤكداً.
- amount رقم بالريال السعودي (مثال 50.14) بدون عملة وبدون فواصل آلاف.
- إذا لم تجد حقلاً فضع null.
- الأرقام العربية حوّلها إلى إنجليزية.

نص الرسالة:
\"\"\"{sms}\"\"\"
"""


def _strip_code_fences(text: str) -> str:
    cleaned = text.strip()
    if cleaned.startswith("```"):
        cleaned = re.sub(r"^```(?:json)?\s*", "", cleaned, flags=re.IGNORECASE)
        cleaned = re.sub(r"\s*```$", "", cleaned)
    return cleaned.strip()


def _extract_json_object(text: str) -> Optional[str]:
    cleaned = _strip_code_fences(text)
    try:
        json.loads(cleaned)
        return cleaned
    except json.JSONDecodeError:
        pass
    match = re.search(r"\{[\s\S]*\}", cleaned)
    if match:
        candidate = match.group(0)
        try:
            json.loads(candidate)
            return candidate
        except json.JSONDecodeError:
            return None
    return None


def parse_gemini_payload(raw_text: str) -> dict:
    """Defensively parse model output into the expected schema."""
    result = {
        "is_valid_deposit": False,
        "amount": None,
        "sender_name": None,
        "bank_name": None,
        "reference": None,
        "raw_model_text": raw_text,
        "parse_error": None,
    }
    blob = _extract_json_object(raw_text or "")
    if not blob:
        result["parse_error"] = "no_json"
        return result
    try:
        data = json.loads(blob)
    except json.JSONDecodeError as exc:
        result["parse_error"] = f"json_error: {exc}"
        return result
    if not isinstance(data, dict):
        result["parse_error"] = "not_an_object"
        return result

    valid = data.get("is_valid_deposit")
    if isinstance(valid, str):
        valid = valid.strip().lower() in {"1", "true", "yes", "ok"}
    result["is_valid_deposit"] = bool(valid)

    amount = data.get("amount")
    if amount is not None and str(amount).strip() not in {"", "null", "None"}:
        try:
            result["amount"] = halalas_to_str(parse_amount_to_halalas(amount))
            result["amount_halalas"] = parse_amount_to_halalas(amount)
        except ValueError:
            result["is_valid_deposit"] = False
            result["parse_error"] = "bad_amount"

    def _clean(value: Any) -> Optional[str]:
        if value is None:
            return None
        text = str(value).strip()
        if text.lower() in {"", "null", "none", "n/a", "-"}:
            return None
        return text

    result["sender_name"] = _clean(data.get("sender_name"))
    result["bank_name"] = _clean(data.get("bank_name"))
    result["reference"] = _clean(data.get("reference"))
    return result


def _extract_gemini_text(api_response: dict) -> str:
    """Handle the real Gemini REST shape: candidates[0].content.parts[0].text"""
    try:
        candidates = api_response.get("candidates") or []
        if not candidates:
            # Some error payloads look like {"error": {"message": "..."}}
            err = api_response.get("error") or {}
            msg = err.get("message") if isinstance(err, dict) else None
            raise RuntimeError(msg or "Gemini returned no candidates")
        content = candidates[0].get("content") or {}
        parts = content.get("parts") or []
        chunks = []
        for part in parts:
            if isinstance(part, dict) and part.get("text"):
                chunks.append(part["text"])
        if not chunks:
            raise RuntimeError("Gemini response had no text parts")
        return "\n".join(chunks)
    except (IndexError, AttributeError, TypeError) as exc:
        raise RuntimeError(f"Unexpected Gemini response shape: {exc}") from exc



def _smoke_test_gemini_payload() -> Optional[str]:
    """Return mock Gemini text if test env hooks are set. Production stays empty."""
    raw = os.environ.get("SMOKE_TEST_GEMINI_JSON")
    if raw and raw.strip():
        return raw
    path = os.environ.get("SMOKE_TEST_GEMINI_FILE")
    if path and os.path.isfile(path):
        try:
            with open(path, "r", encoding="utf-8") as fh:
                data = fh.read()
            if data.strip():
                return data
        except OSError as exc:
            log.warning("Could not read SMOKE_TEST_GEMINI_FILE: %s", exc)
    return None


def verify_sms_with_gemini(sms_text: str) -> dict:
    """
    Send raw bank SMS to Gemini and return a defensive parse of:
    {is_valid_deposit, amount, sender_name, bank_name, reference}
    """
    mock = _smoke_test_gemini_payload()
    if mock:
        log.info("Using smoke-test Gemini mock instead of live API")
        return parse_gemini_payload(mock)

    if not GEMINI_API_KEY:
        raise RuntimeError("GEMINI_API_KEY غير مُعدّ")

    prompt = GEMINI_PROMPT.format(sms=sms_text[:8000])
    payload = {
        "contents": [{"role": "user", "parts": [{"text": prompt}]}],
        "generationConfig": {
            "temperature": 0,
            "responseMimeType": "application/json",
        },
    }
    try:
        response = requests.post(
            GEMINI_API_URL,
            params={"key": GEMINI_API_KEY},
            json=payload,
            timeout=30,
            headers={"Content-Type": "application/json"},
        )
    except requests.RequestException as exc:
        raise RuntimeError(f"تعذر الاتصال بـ Gemini: {exc}") from exc

    try:
        body = response.json()
    except ValueError as exc:
        raise RuntimeError(
            f"Gemini returned non-JSON (HTTP {response.status_code})"
        ) from exc

    if response.status_code >= 400:
        err = body.get("error") if isinstance(body, dict) else None
        msg = err.get("message") if isinstance(err, dict) else response.text[:300]
        raise RuntimeError(f"Gemini HTTP {response.status_code}: {msg}")

    text = _extract_gemini_text(body)
    return parse_gemini_payload(text)


# ---------------------------------------------------------------------------
# Telegram
# ---------------------------------------------------------------------------


def send_telegram(message: str) -> bool:
    """Send a Telegram message. No-ops safely if token/chat is missing."""
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        log.info("Telegram skipped (TELEGRAM_BOT_TOKEN or TELEGRAM_CHAT_ID not set)")
        return False
    url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
    try:
        response = requests.post(
            url,
            json={
                "chat_id": TELEGRAM_CHAT_ID,
                "text": message,
                "parse_mode": "HTML",
                "disable_web_page_preview": True,
            },
            timeout=15,
        )
        if response.status_code >= 400:
            log.warning("Telegram send failed: %s %s", response.status_code, response.text[:300])
            return False
        return True
    except requests.RequestException as exc:
        log.warning("Telegram send error: %s", exc)
        return False


def notify_paid(invoice: dict, parsed: dict) -> None:
    link = payment_link(invoice["token"])
    message = (
        "✅ <b>تم تأكيد دفعة — Wahm Pay</b>\n\n"
        f"المنتج: <b>{_html(invoice['product_name'])}</b>\n"
        f"التوكن: <code>{_html(invoice['token'])}</code>\n"
        f"المبلغ: <b>{halalas_to_str(invoice['required_amount_halalas'])} ر.س</b>\n"
        f"المرسل: {_html(parsed.get('sender_name') or '—')}\n"
        f"البنك: {_html(parsed.get('bank_name') or '—')}\n"
        f"المرجع: {_html(parsed.get('reference') or '—')}\n"
        f"الوقت: {format_riyadh(utcnow())} (الرياض)\n"
        f"الرابط: {_html(link)}"
    )
    send_telegram(message)


def notify_unmatched(parsed: dict, reason: str, raw_sms: str) -> None:
    amount = parsed.get("amount") or "—"
    message = (
        "⚠️ <b>حوالة بدون فاتورة مطابقة — Wahm Pay</b>\n\n"
        f"السبب: {_html(reason)}\n"
        f"المبلغ: <b>{_html(str(amount))} ر.س</b>\n"
        f"المرسل: {_html(parsed.get('sender_name') or '—')}\n"
        f"البنك: {_html(parsed.get('bank_name') or '—')}\n"
        f"المرجع: {_html(parsed.get('reference') or '—')}\n"
        f"الوقت: {format_riyadh(utcnow())} (الرياض)\n\n"
        f"<pre>{_html((raw_sms or '')[:800])}</pre>"
    )
    send_telegram(message)


def _html(value: str) -> str:
    return (
        str(value)
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
    )


# ---------------------------------------------------------------------------
# Webhook helpers
# ---------------------------------------------------------------------------


def extract_sms_text() -> str:
    if request.is_json:
        body = request.get_json(silent=True) or {}
        if isinstance(body, dict):
            for key in (
                "text",
                "sms",
                "message",
                "body",
                "Body",
                "content",
                "msg",
                "sms_text",
            ):
                if body.get(key):
                    return str(body.get(key)).strip()
            # Some shortcuts wrap it
            if isinstance(body.get("data"), str):
                return body["data"].strip()
        elif isinstance(body, str):
            return body.strip()
    if request.form:
        for key in ("text", "sms", "message", "body", "Body", "content", "msg"):
            if request.form.get(key):
                return str(request.form.get(key)).strip()
    raw = request.get_data(as_text=True) or ""
    raw = raw.strip()
    if raw.startswith("{") or raw.startswith("["):
        try:
            parsed = json.loads(raw)
            if isinstance(parsed, dict):
                for key in ("text", "sms", "message", "body", "Body", "content"):
                    if parsed.get(key):
                        return str(parsed.get(key)).strip()
            if isinstance(parsed, str):
                return parsed.strip()
        except json.JSONDecodeError:
            pass
    return raw


def log_webhook(conn: sqlite3.Connection, raw_text: str, parsed: Optional[dict], result: str, token: Optional[str], detail: str) -> None:
    conn.execute(
        """
        INSERT INTO webhook_logs (received_at, raw_text, parsed_json, result, invoice_token, detail)
        VALUES (?, ?, ?, ?, ?, ?)
        """,
        (
            to_iso(utcnow()),
            raw_text,
            json.dumps(parsed, ensure_ascii=False) if parsed else None,
            result,
            token,
            detail,
        ),
    )


def invoice_public_dict(inv: dict, include_redirect: bool = True) -> dict:
    created = parse_iso(inv.get("created_at"))
    expires = parse_iso(inv.get("expires_at"))
    paid = parse_iso(inv.get("paid_at"))
    status = inv["status"]
    # Re-evaluate expiry for the caller
    if status == STATUS_PENDING and expires and expires <= utcnow():
        status = STATUS_EXPIRED
    payload = {
        "ok": True,
        "token": inv["token"],
        "product_name": inv["product_name"],
        "base_price": halalas_to_str(inv["base_price_halalas"]),
        "amount": halalas_to_str(inv["required_amount_halalas"]),
        "status": status,
        "created_at": to_iso(created),
        "expires_at": to_iso(expires),
        "paid_at": to_iso(paid),
    }
    if include_redirect:
        payload["redirect_url"] = inv.get("redirect_url") or None
    if status == STATUS_PAID:
        payload["sender_name"] = inv.get("sender_name")
        payload["bank_name"] = inv.get("bank_name")
        payload["reference"] = inv.get("reference")
    return payload


def create_invoice_record(product_name: str, base_price_raw: Any, redirect_url: Optional[str]) -> dict:
    product_name = (product_name or "").strip()
    if not product_name:
        raise ValueError("اسم المنتج مطلوب")
    if len(product_name) > 200:
        raise ValueError("اسم المنتج طويل جداً")

    base_halalas = parse_amount_to_halalas(base_price_raw)
    if base_halalas <= 0:
        raise ValueError("السعر يجب أن يكون أكبر من صفر")
    if base_halalas > 10_000_000 * 100:
        raise ValueError("السعر أكبر من الحد المسموح")

    redirect_url = (redirect_url or "").strip() or None
    if redirect_url:
        if len(redirect_url) > 2000:
            raise ValueError("رابط التوجيه طويل جداً")
        lowered = redirect_url.lower()
        if not (lowered.startswith("http://") or lowered.startswith("https://")):
            raise ValueError("رابط التوجيه يجب أن يبدأ بـ http:// أو https://")

    now = utcnow()
    expires = now + timedelta(minutes=INVOICE_VALIDITY_MINUTES)

    with get_db() as conn:
        expire_stale_invoices(conn)
        token = generate_token(conn)
        required = generate_unique_amount(conn, base_halalas)
        conn.execute(
            """
            INSERT INTO invoices (
                token, product_name, base_price_halalas, required_amount_halalas,
                redirect_url, status, created_at, expires_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                token,
                product_name,
                base_halalas,
                required,
                redirect_url,
                STATUS_PENDING,
                to_iso(now),
                to_iso(expires),
            ),
        )
        row = conn.execute("SELECT * FROM invoices WHERE token = ?", (token,)).fetchone()

    inv = row_to_dict(row)
    assert inv is not None
    log.info(
        "Created invoice %s amount=%s (base %s) expires=%s",
        token,
        halalas_to_str(required),
        halalas_to_str(base_halalas),
        to_iso(expires),
    )
    return inv


# ---------------------------------------------------------------------------
# Template context
# ---------------------------------------------------------------------------


@app.context_processor
def inject_globals():
    return {
        "csrf_token": csrf_token,
        "merchant_name": MERCHANT_NAME,
        "merchant_iban": MERCHANT_IBAN,
        "format_riyadh": format_riyadh,
        "halalas_to_str": halalas_to_str,
        "validity_minutes": INVOICE_VALIDITY_MINUTES,
    }


@app.after_request
def security_headers(response: Response) -> Response:
    response.headers.setdefault("X-Content-Type-Options", "nosniff")
    response.headers.setdefault("X-Frame-Options", "DENY")
    response.headers.setdefault("Referrer-Policy", "strict-origin-when-cross-origin")
    # Allow Tailwind CDN + Google Fonts on HTML pages
    if response.content_type and "text/html" in response.content_type:
        response.headers.setdefault(
            "Content-Security-Policy",
            "default-src 'self'; "
            "script-src 'self' 'unsafe-inline' https://cdn.tailwindcss.com; "
            "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; "
            "font-src https://fonts.gstatic.com; "
            "img-src 'self' data:; "
            "connect-src 'self'; "
            "frame-ancestors 'none'",
        )
    if request.is_secure or request.headers.get("X-Forwarded-Proto") == "https":
        response.headers.setdefault(
            "Strict-Transport-Security", "max-age=31536000; includeSubDomains"
        )
    return response


# ---------------------------------------------------------------------------
# Routes — health & home
# ---------------------------------------------------------------------------


@app.route("/health")
def health():
    try:
        with get_db() as conn:
            conn.execute("SELECT 1").fetchone()
        db_ok = True
    except Exception as exc:
        log.exception("Health check DB error: %s", exc)
        db_ok = False
    payload = {
        "ok": db_ok,
        "service": "wahm-pay",
        "time": to_iso(utcnow()),
    }
    return jsonify(payload), 200 if db_ok else 500


@app.route("/")
def home():
    if session.get("admin"):
        return redirect(url_for("admin_dashboard"))
    return redirect(url_for("login"))


# ---------------------------------------------------------------------------
# Routes — admin auth
# ---------------------------------------------------------------------------


@app.route("/login", methods=["GET", "POST"])
def login():
    if session.get("admin"):
        return redirect(url_for("admin_dashboard"))

    error = None
    if request.method == "POST":
        if not validate_csrf():
            error = "انتهت صلاحية الجلسة، حدّث الصفحة وحاول مرة أخرى."
        elif not ADMIN_PASSWORD:
            error = "الخادم غير مُعدّ: عيّن متغير البيئة ADMIN_PASSWORD."
        elif not _login_allowed(_client_ip()):
            error = "محاولات كثيرة. انتظر بضع دقائق ثم حاول مرة أخرى."
        else:
            password = request.form.get("password") or ""
            if hmac.compare_digest(ADMIN_PASSWORD, password):
                _clear_login_failures(_client_ip())
                session.clear()
                session["admin"] = True
                session.permanent = True
                csrf_token()
                nxt = request.args.get("next") or url_for("admin_dashboard")
                if not nxt.startswith("/"):
                    nxt = url_for("admin_dashboard")
                return redirect(nxt)
            _record_login_failure(_client_ip())
            error = "كلمة المرور غير صحيحة."

    return render_template("login.html", error=error)


@app.route("/logout", methods=["POST", "GET"])
def logout():
    if request.method == "POST" and not validate_csrf():
        flash("طلب غير صالح.", "error")
        return redirect(url_for("admin_dashboard"))
    session.clear()
    return redirect(url_for("login"))


# ---------------------------------------------------------------------------
# Routes — admin dashboard
# ---------------------------------------------------------------------------


@app.route("/admin")
@admin_required
def admin_dashboard():
    with get_db() as conn:
        expire_stale_invoices(conn)
        invoices = conn.execute(
            "SELECT * FROM invoices ORDER BY id DESC LIMIT 500"
        ).fetchall()
        unmatched = conn.execute(
            "SELECT * FROM unmatched_deposits ORDER BY id DESC LIMIT 50"
        ).fetchall()
        logs = conn.execute(
            "SELECT * FROM webhook_logs ORDER BY id DESC LIMIT 30"
        ).fetchall()
        counts_rows = conn.execute(
            "SELECT status, COUNT(*) AS n FROM invoices GROUP BY status"
        ).fetchall()

    counts = {STATUS_PENDING: 0, STATUS_PAID: 0, STATUS_EXPIRED: 0}
    for row in counts_rows:
        counts[row["status"]] = row["n"]

    invoice_views = []
    for row in invoices:
        inv = row_to_dict(row)
        inv["base_price_str"] = halalas_to_str(inv["base_price_halalas"])
        inv["amount_str"] = halalas_to_str(inv["required_amount_halalas"])
        inv["created_local"] = format_riyadh(parse_iso(inv["created_at"]))
        inv["expires_local"] = format_riyadh(parse_iso(inv["expires_at"]))
        inv["paid_local"] = format_riyadh(parse_iso(inv["paid_at"])) if inv.get("paid_at") else "—"
        inv["payment_link"] = payment_link(inv["token"])
        if inv.get("transfer_amount_halalas") is not None:
            inv["transfer_amount_str"] = halalas_to_str(inv["transfer_amount_halalas"])
        else:
            inv["transfer_amount_str"] = None
        invoice_views.append(inv)

    unmatched_views = []
    for row in unmatched:
        item = row_to_dict(row)
        item["amount_str"] = (
            halalas_to_str(item["amount_halalas"]) if item.get("amount_halalas") is not None else "—"
        )
        item["created_local"] = format_riyadh(parse_iso(item["created_at"]))
        unmatched_views.append(item)

    log_views = []
    for row in logs:
        item = row_to_dict(row)
        item["received_local"] = format_riyadh(parse_iso(item["received_at"]))
        log_views.append(item)

    return render_template(
        "admin.html",
        invoices=invoice_views,
        unmatched=unmatched_views,
        logs=log_views,
        counts=counts,
        base_url=public_base_url(),
    )


@app.route("/admin/create", methods=["POST"])
@admin_required
def admin_create():
    if not validate_csrf():
        flash("طلب غير صالح، حدّث الصفحة وحاول مرة أخرى.", "error")
        return redirect(url_for("admin_dashboard"))
    product_name = request.form.get("product_name") or ""
    price = request.form.get("price") or ""
    redirect_url = request.form.get("redirect_url") or ""
    try:
        inv = create_invoice_record(product_name, price, redirect_url)
    except ValueError as exc:
        flash(str(exc), "error")
        return redirect(url_for("admin_dashboard"))
    except RuntimeError as exc:
        flash(str(exc), "error")
        return redirect(url_for("admin_dashboard"))
    flash(
        f"تم إنشاء الفاتورة {inv['token']} — المبلغ المطلوب {halalas_to_str(inv['required_amount_halalas'])} ر.س",
        "success",
    )
    return redirect(url_for("admin_dashboard"))


# ---------------------------------------------------------------------------
# Routes — checkout
# ---------------------------------------------------------------------------


@app.route("/pay/<token>")
def checkout(token: str):
    token = (token or "").strip().upper()
    with get_db() as conn:
        expire_stale_invoices(conn)
        row = conn.execute("SELECT * FROM invoices WHERE token = ?", (token,)).fetchone()
        if row and row["status"] == STATUS_PENDING:
            expires = parse_iso(row["expires_at"])
            if expires and expires <= utcnow():
                conn.execute(
                    "UPDATE invoices SET status = ? WHERE token = ? AND status = ?",
                    (STATUS_EXPIRED, token, STATUS_PENDING),
                )
                row = conn.execute("SELECT * FROM invoices WHERE token = ?", (token,)).fetchone()

    if not row:
        return render_template("checkout.html", missing=True, token=token), 404

    inv = row_to_dict(row)
    inv["amount_str"] = halalas_to_str(inv["required_amount_halalas"])
    inv["base_price_str"] = halalas_to_str(inv["base_price_halalas"])
    return render_template(
        "checkout.html",
        missing=False,
        invoice=inv,
        amount_str=inv["amount_str"],
        expires_at=inv["expires_at"],
        status=inv["status"],
    )


# ---------------------------------------------------------------------------
# Routes — public status + create-invoice API
# ---------------------------------------------------------------------------


@app.route("/api/status/<token>")
def api_status(token: str):
    token = (token or "").strip().upper()
    with get_db() as conn:
        expire_stale_invoices(conn)
        row = conn.execute("SELECT * FROM invoices WHERE token = ?", (token,)).fetchone()
    if not row:
        return jsonify({"ok": False, "error": "الفاتورة غير موجودة", "status": "NotFound"}), 404
    return jsonify(invoice_public_dict(row_to_dict(row)))


@app.route("/api/create-invoice", methods=["POST"])
def api_create_invoice():
    denied = require_api_secret()
    if denied:
        return denied
    data = request.get_json(silent=True) or {}
    if not data and request.form:
        data = request.form.to_dict()

    product_name = (
        data.get("product_name")
        or data.get("name")
        or data.get("title")
        or data.get("product")
        or ""
    )
    price = data.get("price", data.get("amount", data.get("base_price")))
    redirect_url = data.get("redirect_url") or data.get("redirect") or data.get("url") or ""

    if price is None or str(price).strip() == "":
        return jsonify({"ok": False, "error": "السعر مطلوب (price)"}), 400

    try:
        inv = create_invoice_record(product_name, price, redirect_url)
    except ValueError as exc:
        return jsonify({"ok": False, "error": str(exc)}), 400
    except RuntimeError as exc:
        return jsonify({"ok": False, "error": str(exc)}), 409

    return jsonify(
        {
            "ok": True,
            "token": inv["token"],
            "payment_link": payment_link(inv["token"]),
            "amount": halalas_to_str(inv["required_amount_halalas"]),
            "base_price": halalas_to_str(inv["base_price_halalas"]),
            "status": inv["status"],
            "expires_at": inv["expires_at"],
            "product_name": inv["product_name"],
        }
    ), 201


# ---------------------------------------------------------------------------
# Routes — webhook
# ---------------------------------------------------------------------------


@app.route("/webhook/sms", methods=["POST"])
def webhook_sms():
    denied = require_api_secret()
    if denied:
        return denied

    try:
        return _handle_webhook_sms()
    except Exception as exc:
        log.exception("Unhandled webhook error: %s", exc)
        try:
            with get_db() as conn:
                log_webhook(conn, "", None, "error", None, str(exc))
        except Exception:
            pass
        return jsonify({"ok": False, "error": "خطأ داخلي أثناء معالجة الرسالة"}), 500


def _handle_webhook_sms():
    sms_text = extract_sms_text()
    if not sms_text:
        return jsonify({"ok": False, "error": "نص الرسالة فارغ (text / sms / message)"}), 400

    try:
        parsed = verify_sms_with_gemini(sms_text)
    except RuntimeError as exc:
        log.warning("Gemini verification failed: %s", exc)
        with get_db() as conn:
            log_webhook(conn, sms_text, None, "gemini_error", None, str(exc))
        return jsonify({"ok": False, "error": f"فشل التحقق بالذكاء الاصطناعي: {exc}"}), 502

    if not parsed.get("is_valid_deposit") or parsed.get("amount_halalas") is None:
        reason = parsed.get("parse_error") or "ليست حوالة واردة صالحة"
        with get_db() as conn:
            log_webhook(conn, sms_text, parsed, "ignored", None, reason)
        return jsonify(
            {
                "ok": True,
                "result": "ignored",
                "reason": reason,
                "parsed": {
                    "is_valid_deposit": parsed.get("is_valid_deposit"),
                    "amount": parsed.get("amount"),
                    "sender_name": parsed.get("sender_name"),
                    "bank_name": parsed.get("bank_name"),
                    "reference": parsed.get("reference"),
                },
            }
        )

    amount_halalas = int(parsed["amount_halalas"])

    with get_db() as conn:
        expire_stale_invoices(conn)

        # Prefer a currently-Pending exact match.
        pending = conn.execute(
            """
            SELECT * FROM invoices
             WHERE status = ? AND required_amount_halalas = ?
             ORDER BY id ASC
             LIMIT 1
            """,
            (STATUS_PENDING, amount_halalas),
        ).fetchone()

        if pending:
            expires = parse_iso(pending["expires_at"])
            if expires and expires <= utcnow():
                conn.execute(
                    "UPDATE invoices SET status = ? WHERE id = ? AND status = ?",
                    (STATUS_EXPIRED, pending["id"], STATUS_PENDING),
                )
                pending = None
                # fall through to expired/unmatched checks
            else:
                now_iso = to_iso(utcnow())
                conn.execute(
                    """
                    UPDATE invoices
                       SET status = ?,
                           paid_at = ?,
                           sender_name = ?,
                           bank_name = ?,
                           reference = ?,
                           transfer_amount_halalas = ?,
                           raw_sms = ?
                     WHERE id = ? AND status = ?
                    """,
                    (
                        STATUS_PAID,
                        now_iso,
                        parsed.get("sender_name"),
                        parsed.get("bank_name"),
                        parsed.get("reference"),
                        amount_halalas,
                        sms_text,
                        pending["id"],
                        STATUS_PENDING,
                    ),
                )
                fresh = conn.execute(
                    "SELECT * FROM invoices WHERE id = ?", (pending["id"],)
                ).fetchone()
                log_webhook(
                    conn,
                    sms_text,
                    parsed,
                    "paid",
                    pending["token"],
                    "matched pending invoice",
                )
                invoice = row_to_dict(fresh)
                # Notify after commit by collecting data now; send outside lock is nicer
                # but we are inside get_db(). Sending here is acceptable (lock held briefly).
                try:
                    notify_paid(invoice, parsed)
                except Exception as exc:
                    log.warning("Telegram notify_paid failed: %s", exc)
                return jsonify(
                    {
                        "ok": True,
                        "result": "paid",
                        "token": invoice["token"],
                        "payment_link": payment_link(invoice["token"]),
                        "amount": halalas_to_str(amount_halalas),
                        "parsed": {
                            "is_valid_deposit": True,
                            "amount": parsed.get("amount"),
                            "sender_name": parsed.get("sender_name"),
                            "bank_name": parsed.get("bank_name"),
                            "reference": parsed.get("reference"),
                        },
                    }
                )

        # Already paid with this exact amount?
        already = conn.execute(
            """
            SELECT * FROM invoices
             WHERE status = ? AND required_amount_halalas = ?
             ORDER BY paid_at DESC
             LIMIT 1
            """,
            (STATUS_PAID, amount_halalas),
        ).fetchone()
        if already:
            log_webhook(
                conn,
                sms_text,
                parsed,
                "already_paid",
                already["token"],
                "amount matches an already-paid invoice",
            )
            return jsonify(
                {
                    "ok": True,
                    "result": "already_paid",
                    "token": already["token"],
                    "amount": halalas_to_str(amount_halalas),
                    "message": "يوجد فاتورة مدفوعة بنفس المبلغ",
                }
            )

        expired = conn.execute(
            """
            SELECT * FROM invoices
             WHERE status = ? AND required_amount_halalas = ?
             ORDER BY id DESC
             LIMIT 1
            """,
            (STATUS_EXPIRED, amount_halalas),
        ).fetchone()
        if expired:
            reason = f"المبلغ يطابق فاتورة منتهية ({expired['token']})"
            conn.execute(
                """
                INSERT INTO unmatched_deposits (
                    amount_halalas, sender_name, bank_name, reference, raw_sms, reason, created_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    amount_halalas,
                    parsed.get("sender_name"),
                    parsed.get("bank_name"),
                    parsed.get("reference"),
                    sms_text,
                    reason,
                    to_iso(utcnow()),
                ),
            )
            log_webhook(conn, sms_text, parsed, "expired", expired["token"], reason)
            try:
                notify_unmatched(parsed, reason, sms_text)
            except Exception as exc:
                log.warning("Telegram notify_unmatched failed: %s", exc)
            return jsonify(
                {
                    "ok": True,
                    "result": "expired",
                    "token": expired["token"],
                    "amount": halalas_to_str(amount_halalas),
                    "message": reason,
                }
            )

        reason = "لا توجد فاتورة معلّقة بهذا المبلغ بالضبط"
        conn.execute(
            """
            INSERT INTO unmatched_deposits (
                amount_halalas, sender_name, bank_name, reference, raw_sms, reason, created_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?)
            """,
            (
                amount_halalas,
                parsed.get("sender_name"),
                parsed.get("bank_name"),
                parsed.get("reference"),
                sms_text,
                reason,
                to_iso(utcnow()),
            ),
        )
        log_webhook(conn, sms_text, parsed, "unmatched", None, reason)
        try:
            notify_unmatched(parsed, reason, sms_text)
        except Exception as exc:
            log.warning("Telegram notify_unmatched failed: %s", exc)
        return jsonify(
            {
                "ok": True,
                "result": "unmatched",
                "amount": halalas_to_str(amount_halalas),
                "message": reason,
                "parsed": {
                    "is_valid_deposit": True,
                    "amount": parsed.get("amount"),
                    "sender_name": parsed.get("sender_name"),
                    "bank_name": parsed.get("bank_name"),
                    "reference": parsed.get("reference"),
                },
            }
        )


# ---------------------------------------------------------------------------
# Startup
# ---------------------------------------------------------------------------


init_db()


if __name__ == "__main__":
    port = int(os.environ.get("PORT", "5000"))
    debug = (_env("FLASK_DEBUG", "0") or "0") in {"1", "true", "True"}
    log.info("Starting Wahm Pay on port %s (debug=%s)", port, debug)
    app.run(host="0.0.0.0", port=port, debug=debug)
