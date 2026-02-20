"""
TikTok SMS Module v14.0

Changelog v14.0:

  Fix: "Url does not match" (status_code=1).
    - Added SIGNER_URL_MODE to control what is passed to sign(params=).
    - Three modes: 'query' (bare query string), 'path_query' (path+query),
      'full_url' (full URL). Default: 'path_query'.
    - Switchable via --sign-mode CLI argument for quick testing.
    - Applied to all signing paths: _request, captcha GET, captcha verify.

  Fix: extract_error_code now checks both 'error_code' and 'status_code'
    fields at root and nested data levels.

  Carries forward all v13.8/v13.9 fixes (binary payload signing,
  SignerPy 3-param API, TTEncrypt class API, manual x-ss-stub).
"""

import asyncio
import aiohttp
import atexit
import hashlib
import json
import random
import re
import secrets
import time
import threading
import base64
import logging
import csv
import argparse
import sys
import os
import signal
import uuid
from datetime import datetime, timedelta
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import urlencode, quote, urlparse
from yarl import URL as YarlURL
from dataclasses import dataclass, replace, fields
from typing import Optional, List, Any, Dict, Tuple, NamedTuple, Set

from SignerPy import sign as signerpy_sign

try:
    from SignerPy import get as signerpy_get
    HAS_SIGNERPY_GET = True
except ImportError:
    HAS_SIGNERPY_GET = False

try:
    from SignerPy import ttencrypt as signerpy_ttencrypt_module
    HAS_TTENCRYPT = True
except ImportError:
    HAS_TTENCRYPT = False

try:
    from SignerPy.encryption import enc as signerpy_enc
    HAS_ENC = True
except ImportError:
    HAS_ENC = False

try:
    from SignerPy.edata import decrypt as signerpy_edata_decrypt
    HAS_EDATA_DECRYPT = True
except ImportError:
    HAS_EDATA_DECRYPT = False

if sys.platform == 'win32':
    asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s')
log = logging.getLogger('tiktok_sms')


# ============================================
#  CONSTANTS
# ============================================

TT_CAPTCHA_REQUIRED = 1107
TT_DEVICE_BAN = 1109
TT_RATE_LIMIT_CODES = (1105, 2, 3)
TT_MSTOKEN_ERRORS = (1003, 1004)
TT_ANTI_SPAM_CODES = (1105, 1109)

ERR_HLR_FAILED = -1
ERR_DEVICE_SETUP = -2
ERR_MAX_RETRIES = -3
ERR_CAPTCHA_LOOP = -4
ERR_SHUTDOWN = -5
ERR_MSTOKEN = -6
ERR_SIGNER = -9
ERR_ALL_ENDPOINTS_FAILED = -10
ERR_CRASH = -99

RETRYABLE_HTTP_CODES = (429, 500, 502, 503, 504)
REDIRECT_HTTP_CODES = (301, 302, 303, 307, 308)
HTTP_TOO_MANY_REQUESTS = 429

MAX_CAPTCHA_ATTEMPTS = 2
MAX_CAPTCHA_ROTATIONS_NO_KEY = 3
MAX_EMPTY_CLAIMS = 3
MAX_PROXY_CONSECUTIVE_FAILS = 3
MAX_PROXY_FAIL_RATE = 0.15
MAX_PROXY_MIN_REQUESTS_FOR_REMOVAL = 20
PROXY_BLACKLIST_BASE_SECONDS = 30
PROXY_BLACKLIST_CAP_SECONDS = 300

APP_AID = 1233
APP_AID_ALT = 1988
APP_AID_STR = '1233'
APP_AID_ALT_STR = '1988'
APP_PACKAGE = 'com.zhiliaoapp.musically'
APP_DISPLAY_NAME = 'TikTok'
APP_CHANNEL = 'googleplay'
APP_SDK_VERSION = '3.0.0'

SIGNER_GORGON_VERSION = 8404

# Sign mode: what to pass as params= to SignerPy.sign()
#   'query'     - only query string: "key1=val1&key2=val2"
#   'path_query' - path + ? + query: "/aweme/v1/path/?key1=val1&key2=val2"
#   'full_url'  - full URL: "https://host/path/?key1=val1&key2=val2"
# TikTok client signs path+query, not bare query string.
SIGNER_URL_MODE = 'query'

DEVICE_ID_MIN = 7_000_000_000_000_000_000
DEVICE_ID_MAX = 7_999_999_999_999_999_999
DEVICE_ID_RANGE = DEVICE_ID_MAX - DEVICE_ID_MIN + 1
DEVICE_ROM_BUILD = 'TP1A.220624.014'
DEVICE_CPU_ABI = 'arm64-v8a'

MS_TOKEN_TTL_SECONDS = 270
MS_TOKEN_MAX_USES = 35
MS_TOKEN_COOKIE_NAME = 'msToken'
MS_TOKEN_HEADER = 'x-ms-token'

DEVICE_MAX_USES_PER_SESSION = 45
RECOVERY_MAX_USES_PER_SESSION = 80

CAPTCHA_TIMEOUTS: Dict[str, int] = {
    '3d': 45, 'shapes': 45, 'slide': 20,
    'puzzle': 20, 'rotate': 25, 'icon': 30,
}
CAPTCHA_TIMEOUT_DEFAULT = 30

RATE_LIMIT_BACKOFF_FACTOR = 0.7
RATE_LIMIT_MIN_RPS = 0.01
RATE_LIMIT_RECOVERY_SECONDS = 30.0
RATE_LIMIT_RECOVERY_FACTOR = 1.5

TASK_BATCH_SIZE = 50
FSYNC_INTERVAL = 10

DEVICE_POOL_REQUIRED_KEYS = frozenset({
    'device_id', 'install_id', 'registered',
    'version_name', 'device_type', 'region',
})

DEVICE_REGISTER_HOSTS: Tuple[str, ...] = (
    'log-va.tiktokv.com',
    'log16-normal-c-useast1a.tiktokv.com',
    'log16-normal-c-useast2a.tiktokv.com',
    'log-va-useast2a.tiktokv.com',
)
DEVICE_REGISTER_PATH = '/service/2/device_register/'
XLOG_PATH = '/service/2/app_log/'

URL_CAPTCHA_GET = 'https://verify.tiktok.com/captcha/get'
URL_CAPTCHA_VERIFY = 'https://verify.tiktok.com/captcha/verify'

VERSION_STALENESS_DAYS = 90

MASK_SUFFIX_LEN = 2
MASK_SHORT_THRESHOLD = 6

SIGN_REQUIRED_HEADERS = ('x-argus', 'x-gorgon', 'x-khronos')
SIGN_OPTIONAL_HEADERS = (
    'x-ladon', 'x-ss-req-ticket', 'x-tt-trace-id', 'x-ss-stub')
SIGN_ALL_HEADERS = SIGN_REQUIRED_HEADERS + SIGN_OPTIONAL_HEADERS

PHONE_MIN_LENGTH = 7
PHONE_MAX_LENGTH = 15
PHONE_PATTERN = re.compile(r'^\+?\d{7,15}$')

# v13.9: max redirect hops when handling manually
MAX_REGISTER_REDIRECT_HOPS = 2
# v13.9: keys to extract from error responses for logging
REGISTER_ERROR_LOG_KEYS = ('error_code', 'code', 'status_code', 'message',
                           'description', 'msg', 'error_msg', 'sub_code')


# ============================================
#  SHUTDOWN
# ============================================

_shutdown_event: Optional[asyncio.Event] = None


def _get_shutdown_event() -> asyncio.Event:
    global _shutdown_event
    if _shutdown_event is None:
        _shutdown_event = asyncio.Event()
    return _shutdown_event


def _setup_signals():
    if threading.current_thread() is not threading.main_thread():
        return

    def _handler(sig, _):
        log.info('Signal %s, shutting down...', sig)
        _get_shutdown_event().set()
    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            signal.signal(sig, _handler)
        except (OSError, ValueError):
            pass


def _setup_signals_if_main():
    try:
        _setup_signals()
    except Exception:
        pass


def check_shutdown():
    if _get_shutdown_event().is_set():
        raise ShutdownError('Shutdown requested')


def is_shutdown() -> bool:
    return _get_shutdown_event().is_set()


# ============================================
#  EXCEPTIONS
# ============================================

class AppError(Exception):
    pass

class NetworkError(AppError):
    def __init__(self, msg: str, retryable: bool = True):
        super().__init__(msg)
        self.retryable = retryable

class ParseError(AppError):
    pass

class DeviceError(AppError):
    pass

class CaptchaError(AppError):
    pass

class ProxyError(AppError):
    pass

class TokenError(AppError):
    pass

class ShutdownError(AppError):
    pass

class ConfigError(AppError):
    pass

class HLRError(AppError):
    pass

class SignerError(AppError):
    pass

class EndpointExhaustedError(AppError):
    pass


# ============================================
#  TYPED EXTRACTION
# ============================================

def extract_dict(data: Any, key: str, context: str = '') -> dict:
    if not isinstance(data, dict):
        raise ParseError(
            '%sexpected dict, got %s' % (
                (context + ': ') if context else '', type(data).__name__))
    value = data.get(key)
    if value is None:
        raise ParseError(
            '%skey "%s" missing' % ((context + ': ') if context else '', key))
    if not isinstance(value, dict):
        raise ParseError(
            '%skey "%s" expected dict, got %s' % (
                (context + ': ') if context else '', key, type(value).__name__))
    return value


def extract_str(data: dict, key: str, default: Optional[str] = None,
                context: str = '') -> str:
    if not isinstance(data, dict):
        raise ParseError(
            '%sexpected dict, got %s' % (
                (context + ': ') if context else '', type(data).__name__))
    value = data.get(key)
    if value is None:
        if default is not None:
            return default
        raise ParseError(
            '%skey "%s" missing' % ((context + ': ') if context else '', key))
    return str(value)


def extract_int(data: dict, key: str, default: Optional[int] = None,
                context: str = '') -> int:
    if not isinstance(data, dict):
        raise ParseError(
            '%sexpected dict, got %s' % (
                (context + ': ') if context else '', type(data).__name__))
    value = data.get(key)
    if value is None:
        if default is not None:
            return default
        raise ParseError(
            '%skey "%s" missing' % ((context + ': ') if context else '', key))
    try:
        return int(value)
    except (ValueError, TypeError):
        if default is not None:
            return default
        raise ParseError(
            '%skey "%s" not int: %r' % (
                (context + ': ') if context else '', key, value)) from None


def extract_optional_dict(data: Any, key: str,
                          context: str = '') -> Optional[dict]:
    if not isinstance(data, dict):
        return None
    value = data.get(key)
    if value is None or not isinstance(value, dict):
        return None
    return value


def extract_error_code(data: dict, context: str = '') -> int:
    inner = extract_optional_dict(data, 'data', context)
    if inner is not None:
        for key in ('error_code', 'status_code'):
            raw = inner.get(key)
            if raw is not None:
                try:
                    return int(raw)
                except (ValueError, TypeError):
                    pass
    for key in ('error_code', 'status_code'):
        raw = data.get(key)
        if raw is not None:
            try:
                return int(raw)
            except (ValueError, TypeError):
                pass
    return -1


def extract_captcha_config(response_data: dict,
                           context: str = 'captcha') -> dict:
    inner = extract_optional_dict(response_data, 'data', context)
    if inner is None:
        raise ParseError('%s: no "data" dict' % context)
    raw_conf = inner.get('verify_center_decision_conf')
    if not raw_conf:
        raise ParseError('%s: no verify_center_decision_conf' % context)
    if isinstance(raw_conf, dict):
        return raw_conf
    if isinstance(raw_conf, str):
        try:
            parsed = json.loads(raw_conf)
        except json.JSONDecodeError as exc:
            raise ParseError('%s: invalid JSON: %s' % (context, exc)) from exc
        if not isinstance(parsed, dict):
            raise ParseError(
                '%s: parsed to %s' % (context, type(parsed).__name__))
        return parsed
    raise ParseError(
        '%s: unexpected type %s' % (context, type(raw_conf).__name__))


# ============================================
#  UTILS
# ============================================

def strip_plus(phone: str) -> str:
    return phone[1:] if phone.startswith('+') else phone


def validate_phone(phone: str) -> str:
    cleaned = phone.strip()
    if not cleaned:
        raise ConfigError('Empty phone number')
    if not PHONE_PATTERN.match(cleaned):
        raise ConfigError('Invalid phone format: %s' % cleaned)
    digits = strip_plus(cleaned)
    if len(digits) < PHONE_MIN_LENGTH:
        raise ConfigError('Phone too short: %s' % cleaned)
    if len(digits) > PHONE_MAX_LENGTH:
        raise ConfigError('Phone too long: %s' % cleaned)
    return cleaned


def mask_phone(phone: str) -> str:
    if not phone:
        return '***'
    clean = phone.strip()
    if len(clean) <= MASK_SHORT_THRESHOLD:
        if len(clean) > MASK_SUFFIX_LEN:
            return '***' + clean[-MASK_SUFFIX_LEN:]
        return '***'
    return '*' * (len(clean) - MASK_SUFFIX_LEN) + clean[-MASK_SUFFIX_LEN:]


def jitter_delay(attempt: int, base: float = 1.0, cap: float = 30.0) -> float:
    return random.uniform(0, min(base * (2 ** attempt), cap))


def _generate_device_id() -> str:
    return str(DEVICE_ID_MIN + secrets.randbelow(DEVICE_ID_RANGE))


def _generate_openudid() -> str:
    return secrets.token_hex(8)


def _generate_cdid() -> str:
    return str(uuid.uuid4())


def sanitize_proxy_url(url: str) -> str:
    if not url:
        return ''
    try:
        parsed = urlparse(url)
        if parsed.password:
            return url.replace(':' + parsed.password + '@', ':***@')
        return url
    except Exception:
        return '***'


def _compute_ss_stub_str(body: str) -> str:
    if not body:
        return ''
    return hashlib.md5(body.encode('utf-8')).hexdigest().upper()


def _compute_ss_stub_bytes(body: bytes) -> str:
    if not body:
        return ''
    return hashlib.md5(body).hexdigest().upper()


# v13.9: summarize a dict response for error logging
def _summarize_response(data: dict, max_len: int = 300) -> str:
    """Extract known error fields from TikTok response for logging."""
    parts = []
    for key in REGISTER_ERROR_LOG_KEYS:
        val = data.get(key)
        if val is not None:
            parts.append('%s=%s' % (key, val))
    # Check nested data dict
    inner = data.get('data')
    if isinstance(inner, dict):
        for key in REGISTER_ERROR_LOG_KEYS:
            val = inner.get(key)
            if val is not None:
                parts.append('data.%s=%s' % (key, val))
    if parts:
        result = ', '.join(parts)
    else:
        # No known fields - dump truncated JSON
        try:
            result = json.dumps(data, ensure_ascii=False)
        except (TypeError, ValueError):
            result = str(data)
    return result[:max_len]


# v13.9: extract host from redirect Location header
def _extract_redirect_host(resp_headers: dict, original_host: str) -> Optional[str]:
    """Parse Location header and return new hostname if different."""
    location = resp_headers.get('Location', '') or resp_headers.get('location', '')
    if not location:
        return None
    try:
        parsed = urlparse(location)
        new_host = parsed.hostname
        if new_host and new_host != original_host:
            return new_host
    except Exception:
        pass
    return None


# ============================================
#  FILE I/O EXECUTOR
# ============================================

_io_executor = ThreadPoolExecutor(max_workers=2, thread_name_prefix='file_io')
atexit.register(lambda: _io_executor.shutdown(wait=False))


async def run_in_io(func, *args):
    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(_io_executor, func, *args)


# ============================================
#  DEVICE HARDWARE
# ============================================

class DeviceHardware(NamedTuple):
    brand: str
    model: str
    os_api: str
    os_version: str
    dpi: str
    resolution: str


# ============================================
#  ENDPOINT REGISTRY
# ============================================

@dataclass(frozen=True)
class SMSEndpoint:
    tier: int
    path: str
    stability: str
    body_style: str
    preferred_aid: int
    supported_types: Tuple[int, ...]

    @property
    def is_deprecated(self) -> bool:
        return self.stability in ('deprecated', 'nearly_deprecated')


ENDPOINT_TIER_1 = SMSEndpoint(
    tier=1, path='/aweme/v1/passport/send_sms_code/',
    stability='excellent', body_style='phone_number',
    preferred_aid=APP_AID_ALT, supported_types=(6, 1, 9))
ENDPOINT_TIER_2 = SMSEndpoint(
    tier=2, path='/aweme/v1/passport/send_phone_sms/',
    stability='good', body_style='mobile',
    preferred_aid=APP_AID, supported_types=(27, 1, 6))
ENDPOINT_TIER_3 = SMSEndpoint(
    tier=3, path='/passport/mobile/send_code/',
    stability='stable', body_style='mobile',
    preferred_aid=APP_AID, supported_types=(5, 21, 1))
ENDPOINT_TIER_4 = SMSEndpoint(
    tier=4, path='/aweme/v1/passport/send_code/',
    stability='legacy', body_style='mobile',
    preferred_aid=APP_AID, supported_types=(5, 21))
ENDPOINT_TIER_5 = SMSEndpoint(
    tier=5, path='/passport/send_sms/',
    stability='nearly_deprecated', body_style='phone_number',
    preferred_aid=APP_AID, supported_types=(1, 6))

ALL_ENDPOINTS: Tuple[SMSEndpoint, ...] = (
    ENDPOINT_TIER_1, ENDPOINT_TIER_2,
    ENDPOINT_TIER_3, ENDPOINT_TIER_4, ENDPOINT_TIER_5)
_ENDPOINTS_BY_TIER: Dict[int, SMSEndpoint] = {ep.tier: ep for ep in ALL_ENDPOINTS}


# ============================================
#  EVENT TYPES & MAPPING
# ============================================

VALID_EVENTS = ('register', 'login', 'recovery', 'change_phone')
LIGHTWEIGHT_EVENTS = frozenset({'recovery', 'change_phone'})

EVENT_EXTRA_PARAMS: Dict[str, Dict[str, Any]] = {
    'register': {'account_sdk_source': 'app', 'mix_mode': 1, 'multi_login': 1},
    'login': {'account_sdk_source': 'app', 'mix_mode': 1, 'multi_login': 1},
    'recovery': {'account_sdk_source': 'app', 'mix_mode': 1, 'multi_login': 1},
    'change_phone': {'account_sdk_source': 'app', 'mix_mode': 1},
}


@dataclass(frozen=True)
class EventEndpointConfig:
    sms_type: int
    fallback_types: Tuple[int, ...]
    endpoint_chain: Tuple[int, ...]

    @property
    def primary_tier(self) -> int:
        return self.endpoint_chain[0]


EVENT_ENDPOINT_MAP: Dict[str, EventEndpointConfig] = {
    'register': EventEndpointConfig(6, (6, 1), (1, 2, 3)),
    'login': EventEndpointConfig(1, (1,), (1, 3, 2)),
    'recovery': EventEndpointConfig(9, (9, 5), (1, 3, 4)),
    'change_phone': EventEndpointConfig(27, (27, 21), (2, 3, 4)),
}


def get_event_config(event: str) -> EventEndpointConfig:
    if event not in EVENT_ENDPOINT_MAP:
        raise ConfigError('Unknown event: ' + event)
    return EVENT_ENDPOINT_MAP[event]


def resolve_sms_type_for_endpoint(event_cfg, endpoint):
    if event_cfg.sms_type in endpoint.supported_types:
        return event_cfg.sms_type
    for ft in event_cfg.fallback_types:
        if ft in endpoint.supported_types:
            return ft
    return event_cfg.sms_type


def build_endpoint_chain(event_cfg, include_deprecated=False, event_name=''):
    chain = []
    seen = set()
    skipped = 0
    for tier in event_cfg.endpoint_chain:
        ep = _ENDPOINTS_BY_TIER.get(tier)
        if not ep:
            continue
        if ep.is_deprecated and not include_deprecated:
            skipped += 1
            continue
        chain.append((ep, resolve_sms_type_for_endpoint(event_cfg, ep)))
        seen.add(tier)
    if include_deprecated:
        for ep in ALL_ENDPOINTS:
            if ep.tier not in seen:
                chain.append((ep, resolve_sms_type_for_endpoint(event_cfg, ep)))
    if not chain and skipped > 0:
        log.warning('Empty chain for %s: all %d deprecated.',
                    event_name or str(event_cfg.sms_type), skipped)
    return chain


def build_body_for_endpoint(endpoint, sms_type, prefix, national, extra_params):
    body: Dict[str, Any] = {}
    if endpoint.body_style == 'phone_number':
        body['phone_number'] = '+' + prefix + national
        body['area'] = prefix
        body['country_code'] = prefix
        body['type'] = sms_type
    else:
        body['type'] = sms_type
        body['mobile_prefix'] = prefix
        body['mobile'] = national
    if endpoint.preferred_aid != APP_AID:
        body['aid'] = endpoint.preferred_aid
    body.update(extra_params)
    return urlencode(body, quote_via=quote)


# ============================================
#  APK VERSION REGISTRY
# ============================================

@dataclass(frozen=True)
class APKVersion:
    version_name: str
    version_code: str
    manifest_version_code: str
    tt_ok_version: str
    sdk_version_str: str
    sdk_version_int: int
    passport_sdk_version: str
    sig_hash: str
    stability: str
    release_date: str = ''
    min_sdk: int = 23
    target_sdk: int = 35

    @property
    def manifest_int(self) -> int:
        try:
            return int(self.manifest_version_code)
        except (ValueError, TypeError):
            return 2023700040

    @property
    def version_code_int(self) -> int:
        try:
            return int(self.version_code)
        except (ValueError, TypeError):
            return 370004

    def is_outdated(self, days=90):
        if not self.release_date:
            return False
        try:
            return datetime.now() - datetime.strptime(
                self.release_date, '%Y-%m-%d') > timedelta(days=days)
        except ValueError:
            return False

    def is_device_compatible(self, os_api):
        return self.min_sdk <= os_api <= self.target_sdk


_DEFAULT_SIG_HASH = '194326e82c84a639a52e5c023116f12a'

APK_VERSIONS: Tuple[APKVersion, ...] = (
    APKVersion('37.0.4', '370004', '2023700040', '3.15.1-tiktok',
               'v04.04.05-ov-android', 134744640, '25',
               _DEFAULT_SIG_HASH, 'stable', '2024-01-15', 23, 34),
    APKVersion('43.9.2', '430902', '2024309020', '3.15.2-tiktok',
               'v04.04.05-ov-android', 134744640, '26',
               _DEFAULT_SIG_HASH, 'unverified', '2025-02-14', 23, 35),
    APKVersion('37.0.3', '370003', '2023700030', '3.15.1-tiktok',
               'v04.04.05-ov-android', 134744640, '25',
               _DEFAULT_SIG_HASH, 'deprecated', '2024-01-10', 23, 34),
    APKVersion('37.0.2', '370002', '2023700020', '3.15.1-tiktok',
               'v04.04.04-ov-android', 134744384, '25',
               _DEFAULT_SIG_HASH, 'deprecated', '2024-01-05', 23, 34),
)

_APK_VERSION_MAP = {v.version_name: v for v in APK_VERSIONS}
DEFAULT_APK_VERSION = APK_VERSIONS[0]


def get_apk_version(name):
    return _APK_VERSION_MAP.get(name, DEFAULT_APK_VERSION)


# ============================================
#  SIGNERPY WRAPPERS
# ============================================

def _extract_cookie_string(cookie_jar, url=''):
    if not cookie_jar:
        return ''
    try:
        if url:
            cookies = cookie_jar.filter_cookies(url)
            if cookies:
                return '; '.join(k + '=' + m.value for k, m in cookies.items())
        all_cookies = []
        try:
            for dc in cookie_jar._cookies.values():
                if isinstance(dc, dict):
                    for k, m in dc.items():
                        if hasattr(m, 'value'):
                            all_cookies.append(k + '=' + m.value)
                        elif isinstance(m, dict):
                            for n, mm in m.items():
                                if hasattr(mm, 'value'):
                                    all_cookies.append(n + '=' + mm.value)
        except AttributeError:
            pass
        return '; '.join(all_cookies)
    except Exception as exc:
        log.warning('_extract_cookie_string: %s', exc)
        return ''


def signer_sign(params: str, payload: str = '',
                version: int = SIGNER_GORGON_VERSION) -> Dict[str, str]:
    try:
        result = signerpy_sign(params=params, payload=payload, version=version)
        if not isinstance(result, dict) or not result:
            raise SignerError('sign() returned empty')
        missing = [h for h in SIGN_REQUIRED_HEADERS if not result.get(h)]
        if missing:
            log.warning('sign() missing: %s', ', '.join(missing))
        return result
    except SignerError:
        raise
    except TypeError as exc:
        log.error('sign() TypeError: %s', exc)
        raise SignerError('sign() API mismatch: ' + str(exc)) from exc
    except Exception as exc:
        raise SignerError('sign(): ' + str(exc)) from exc


def signer_get(params: str) -> Dict[str, str]:
    if HAS_SIGNERPY_GET:
        try:
            result = signerpy_get(params=params)
            if isinstance(result, dict) and result:
                return result
        except Exception as exc:
            log.debug('get() failed: %s', exc)
    return signer_sign(params=params, payload='')


def signer_encrypt(payload: Any) -> bytes:
    if isinstance(payload, dict):
        payload_str = json.dumps(payload)
    elif isinstance(payload, bytes):
        payload_str = payload.decode('utf-8')
    elif isinstance(payload, str):
        payload_str = payload
    else:
        payload_str = json.dumps(payload)

    if HAS_TTENCRYPT:
        try:
            enc_instance = signerpy_ttencrypt_module.Enc()
            result = enc_instance.encrypt(data=payload_str)
            if isinstance(result, bytes) and result:
                return result
            if isinstance(result, str) and result:
                return result.encode('utf-8')
        except AttributeError:
            log.warning('ttencrypt.Enc().encrypt() unavailable')
            try:
                if hasattr(signerpy_ttencrypt_module, 'encrypt'):
                    result = signerpy_ttencrypt_module.encrypt(
                        payload_str.encode('utf-8'))
                    if isinstance(result, bytes) and result:
                        return result
                    if isinstance(result, str) and result:
                        return result.encode('utf-8')
            except Exception as exc2:
                log.warning('ttencrypt fallback: %s', exc2)
        except Exception as exc:
            log.warning('TTEncrypt failed: %s', exc)

    if HAS_ENC:
        try:
            result = signerpy_enc(payload)
            if isinstance(result, bytes) and result:
                return result
            if isinstance(result, str) and result:
                return result.encode('utf-8')
        except Exception as exc:
            log.warning('enc() failed: %s', exc)

    raise SignerError('All encryption methods failed')


def signer_decrypt(data: bytes) -> str:
    if not HAS_EDATA_DECRYPT:
        raise SignerError('edata decrypt not available')
    try:
        result = signerpy_edata_decrypt(data)
        if isinstance(result, str):
            return result
        if isinstance(result, bytes):
            return result.decode('utf-8')
        raise SignerError('decrypt returned non-str')
    except SignerError:
        raise
    except Exception as exc:
        raise SignerError('decrypt: ' + str(exc)) from exc


@dataclass(frozen=True)
class _BodyInfo:
    """Describes the body for signing and sending.

    sign_payload: string to pass to sign(payload=...).
    ss_stub: precomputed x-ss-stub value, or empty.
    raw_data: the actual body to send via aiohttp (str or bytes or None).
    is_post: whether this is a POST request.
    """
    sign_payload: str
    ss_stub: str
    raw_data: Any  # str, bytes, or None
    is_post: bool


def _classify_body(method: str, body: Any) -> _BodyInfo:
    """Classify request body into signing and sending components."""
    is_post = method == 'POST'

    if body is None:
        return _BodyInfo(
            sign_payload='', ss_stub='',
            raw_data=None, is_post=is_post)

    if isinstance(body, bytes):
        return _BodyInfo(
            sign_payload='',
            ss_stub=_compute_ss_stub_bytes(body),
            raw_data=body,
            is_post=is_post)

    if isinstance(body, str):
        return _BodyInfo(
            sign_payload=body,
            ss_stub=_compute_ss_stub_str(body),
            raw_data=body,
            is_post=is_post)

    body_str = str(body)
    return _BodyInfo(
        sign_payload=body_str,
        ss_stub=_compute_ss_stub_str(body_str),
        raw_data=body_str,
        is_post=is_post)


def _make_sign_params(url: str, query_string: str) -> str:
    """Build the string to pass to sign(params=...) based on SIGNER_URL_MODE.

    Args:
        url: full URL without query string (e.g. https://host/path)
        query_string: bare query string (e.g. key1=val1&key2=val2)
    """
    if SIGNER_URL_MODE == 'path_query':
        try:
            parsed_path = urlparse(url).path
            return parsed_path + '?' + query_string
        except Exception:
            return query_string
    elif SIGNER_URL_MODE == 'full_url':
        return url + '?' + query_string
    else:
        return query_string


def _build_signing_headers(params_str: str,
                           body_info: _BodyInfo,
                           user_agent: str,
                           frozen_ts_s: Optional[str] = None,
                           frozen_ts_ms: Optional[str] = None,
                           ) -> Dict[str, str]:
    if body_info.is_post and body_info.sign_payload:
        auth = signer_sign(params=params_str, payload=body_info.sign_payload)
    else:
        auth = signer_get(params=params_str)

    headers: Dict[str, str] = {
        'User-Agent': user_agent,
        'Accept-Encoding': 'gzip',
        'Connection': 'Keep-Alive',
    }

    for h in SIGN_ALL_HEADERS:
        v = auth.get(h, '')
        if v:
            headers[h] = str(v)

    if body_info.ss_stub:
        headers['x-ss-stub'] = body_info.ss_stub
    elif 'x-ss-stub' in headers:
        del headers['x-ss-stub']

    if frozen_ts_s is not None:
        headers['x-khronos'] = frozen_ts_s
    elif not headers.get('x-khronos'):
        headers['x-khronos'] = str(int(time.time()))

    if frozen_ts_ms is not None:
        headers['x-ss-req-ticket'] = frozen_ts_ms
    elif not headers.get('x-ss-req-ticket'):
        headers['x-ss-req-ticket'] = str(int(time.time() * 1000))

    return headers


def _build_test_params(device_id='7123456789012345678', ver=None):
    if ver is None:
        ver = DEFAULT_APK_VERSION
    now_ms = str(int(time.time() * 1000))
    now_s = str(int(time.time()))
    return urlencode({
        'version_name': ver.version_name,
        'version_code': ver.version_code,
        'manifest_version_code': ver.manifest_version_code,
        'update_version_code': ver.manifest_version_code,
        'device_id': device_id,
        'iid': _generate_device_id(),
        'aid': APP_AID_STR, 'app_name': 'musical_ly',
        'channel': APP_CHANNEL, 'device_platform': 'android',
        'device_type': 'Pixel 7', 'device_brand': 'Google',
        'os': 'android', 'os_version': '14', 'os_api': '34',
        'ac': 'wifi', 'ac2': 'wifi', 'language': 'en', 'locale': 'en',
        'region': 'US', 'sys_region': 'US', 'current_region': 'US',
        'carrier_region': 'US', 'op_region': 'US', 'residence': 'US',
        'app_language': 'en', 'ssmix': 'a',
        'openudid': _generate_openudid(), 'cdid': _generate_cdid(),
        'resolution': '1080*2400', 'dpi': '420',
        'ab_version': ver.version_name,
        'build_number': ver.version_name,
        'host_abi': DEVICE_CPU_ABI, 'is_pad': '0',
        'app_type': 'normal', 'timezone_name': 'America/New_York',
        'timezone_offset': '-14400', 'mcc_mnc': '310260', 'uoo': '0',
        '_rticket': now_ms, 'ts': now_s,
        'passport-sdk-version': ver.passport_sdk_version,
    })


# ============================================
#  HLR
# ============================================

@dataclass
class HLRResult:
    country_code: str = 'US'
    country_prefix: str = ''
    national_number: str = ''
    country_name: str = ''
    carrier: str = ''

    @classmethod
    def from_api(cls, info: dict, fallback: str = ''):
        return cls(
            country_code=info.get('country_code', 'US'),
            country_prefix=strip_plus(info.get('country_prefix', '')),
            national_number=info.get('national_number', fallback),
            country_name=info.get('country_name', ''),
            carrier=info.get('carrier', ''))


class HLRLookup:
    def __init__(self, config):
        self.api_key = config.hlr_api_key
        self.api_url = config.hlr_api_url

    async def lookup(self, session, phone):
        phone_clean = strip_plus(phone)
        timeout_count = 0
        for attempt in range(3):
            check_shutdown()
            try:
                async with session.get(
                    self.api_url, params={'phoneNumber': phone_clean},
                    headers={'X-API-Key': self.api_key},
                    timeout=aiohttp.ClientTimeout(total=10)
                ) as resp:
                    if resp.status == 200:
                        data = await resp.json()
                        if data.get('success'):
                            return HLRResult.from_api(
                                data.get('data') or {}, phone_clean)
                        return None
                    if resp.status in RETRYABLE_HTTP_CODES:
                        await asyncio.sleep(jitter_delay(attempt))
                        continue
                    return None
            except (asyncio.TimeoutError, aiohttp.ServerTimeoutError):
                timeout_count += 1
                log.warning('HLR timeout %d/3 for %s',
                            timeout_count, mask_phone(phone))
                await asyncio.sleep(jitter_delay(attempt, 0.5))
            except aiohttp.ClientError as exc:
                raise NetworkError('HLR: ' + str(exc)) from exc
            except ShutdownError:
                raise
            except Exception as exc:
                raise NetworkError('HLR: ' + str(exc)) from exc
        if timeout_count >= 3:
            raise HLRError('HLR timed out 3x for %s' % mask_phone(phone))
        return None


# ============================================
#  RATE LIMITER
# ============================================

class RateLimiter:
    def __init__(self, rate=10.0, burst=20):
        self._rate = max(rate, RATE_LIMIT_MIN_RPS)
        self._initial_rate = self._rate
        self._burst = burst
        self._tokens = float(burst)
        self._last_refill = time.monotonic()
        self._last_slowdown = 0.0
        self._lock = asyncio.Lock()

    async def acquire(self, tokens=1):
        while True:
            check_shutdown()
            async with self._lock:
                now = time.monotonic()
                self._tokens = min(
                    self._burst,
                    self._tokens + (now - self._last_refill) * self._rate)
                self._last_refill = now
                if (self._rate < self._initial_rate
                        and self._last_slowdown > 0
                        and now - self._last_slowdown > RATE_LIMIT_RECOVERY_SECONDS):
                    self._rate = min(self._initial_rate,
                                     self._rate * RATE_LIMIT_RECOVERY_FACTOR)
                if self._tokens >= tokens:
                    self._tokens -= tokens
                    return
                wait = (tokens - self._tokens) / max(self._rate, 1e-9)
            await asyncio.sleep(min(wait, 1.0))

    async def slow_down(self):
        async with self._lock:
            new = max(RATE_LIMIT_MIN_RPS, self._rate * RATE_LIMIT_BACKOFF_FACTOR)
            if new != self._rate:
                self._rate = new
                self._last_slowdown = time.monotonic()
                log.info('Rate -> %.2f', self._rate)


# ============================================
#  PROXY MANAGER
# ============================================

class ProxyManager:
    @dataclass
    class _Entry:
        host: str
        port: str
        user: str
        password: str
        fail_count: int = 0
        permanent_fail_count: int = 0
        blacklisted_until: float = 0.0
        total_requests: int = 0
        permanently_removed: bool = False

        @property
        def host_port(self):
            return self.host + ':' + self.port

        def is_available(self):
            if self.permanently_removed:
                return False
            return self.blacklisted_until <= 0 or time.time() > self.blacklisted_until

        def record_success(self):
            self.total_requests += 1
            self.fail_count = 0

        def record_failure(self):
            self.total_requests += 1
            self.fail_count += 1
            self.permanent_fail_count += 1
            if (self.total_requests >= MAX_PROXY_MIN_REQUESTS_FOR_REMOVAL
                    and self.permanent_fail_count / self.total_requests > MAX_PROXY_FAIL_RATE):
                self.permanently_removed = True
                log.warning('Proxy %s removed: %.1f%% errors',
                            self.host_port,
                            self.permanent_fail_count / self.total_requests * 100)
                return
            if self.fail_count >= MAX_PROXY_CONSECUTIVE_FAILS:
                duration = min(
                    PROXY_BLACKLIST_BASE_SECONDS * (2 ** (self.fail_count - MAX_PROXY_CONSECUTIVE_FAILS)),
                    PROXY_BLACKLIST_CAP_SECONDS)
                self.blacklisted_until = time.time() + duration

    def __init__(self, proxies=None):
        self._entries = []
        self._lock = asyncio.Lock()
        self._index = 0
        if proxies:
            for ps in proxies:
                e = self._parse(ps)
                if e:
                    self._entries.append(e)
            log.info('Proxies: %d', len(self._entries))

    @staticmethod
    def _parse(proxy):
        clean = proxy.strip()
        for pfx in ('http://', 'https://', 'socks5://'):
            if clean.startswith(pfx):
                clean = clean[len(pfx):]
        host = port = user = password = ''
        if '@' in clean:
            auth, server = clean.rsplit('@', 1)
            sp = server.split(':')
            if len(sp) != 2:
                return None
            host, port = sp
            ap = auth.split(':', 1)
            user = ap[0]
            password = ap[1] if len(ap) > 1 else ''
        else:
            parts = clean.split(':', 3)
            if len(parts) == 2:
                host, port = parts
            elif len(parts) >= 4:
                host, port, user, password = parts[0], parts[1], parts[2], parts[3]
            else:
                return None
        return ProxyManager._Entry(host=host, port=port, user=user, password=password) if host and port else None

    async def get(self, country_code=None):
        if not self._entries:
            return None
        async with self._lock:
            available = [e for e in self._entries if not e.permanently_removed]
            if not available:
                return None
            for _ in range(len(available)):
                e = available[self._index % len(available)]
                self._index += 1
                if e.is_available():
                    return self._url(e, country_code)
            best = min(available, key=lambda x: x.blacklisted_until)
            best.blacklisted_until = 0
            best.fail_count = 0
            return self._url(best, country_code)

    @staticmethod
    def _url(e, cc):
        pw = e.password
        if cc:
            if 'COUNTRY_CODE' in pw:
                pw = pw.replace('COUNTRY_CODE', cc)
            elif 'country-' not in pw:
                pw += '_country-' + cc + '_streaming-1'
        if e.user:
            return 'http://' + quote(e.user, safe='') + ':' + quote(pw, safe='') + '@' + e.host + ':' + e.port
        return 'http://' + e.host + ':' + e.port

    def _find_entry(self, url):
        if not url:
            return None
        try:
            parsed = urlparse(url)
            hp = (parsed.hostname or '') + ':' + str(parsed.port or '')
            for e in self._entries:
                if e.host_port == hp:
                    return e
        except Exception:
            pass
        return None

    async def report_success(self, url):
        if not url or not self._entries:
            return
        async with self._lock:
            entry = self._find_entry(url)
            if entry:
                entry.record_success()

    async def report_failure(self, url):
        if not url or not self._entries:
            return
        async with self._lock:
            entry = self._find_entry(url)
            if entry:
                entry.record_failure()


# ============================================
#  CONFIG
# ============================================

_DEFAULT_DEVICES: Tuple[DeviceHardware, ...] = (
    DeviceHardware('Google', 'Pixel 9', '35', '15', '420', '1080*2424'),
    DeviceHardware('Google', 'Pixel 9 Pro', '35', '15', '512', '1280*2856'),
    DeviceHardware('Google', 'Pixel 9 Pro XL', '35', '15', '512', '1344*2992'),
    DeviceHardware('Samsung', 'SM-S928B', '35', '15', '480', '1440*3120'),
    DeviceHardware('Samsung', 'SM-S926B', '35', '15', '480', '1440*3120'),
    DeviceHardware('Google', 'Pixel 8', '34', '14', '420', '1080*2400'),
    DeviceHardware('Google', 'Pixel 8 Pro', '34', '14', '512', '1344*2992'),
    DeviceHardware('Google', 'Pixel 7 Pro', '34', '14', '512', '1440*3120'),
    DeviceHardware('Samsung', 'SM-S918B', '34', '14', '480', '1440*3088'),
    DeviceHardware('Samsung', 'SM-A546B', '34', '14', '400', '1080*2340'),
    DeviceHardware('Xiaomi', '2304FPN6DC', '34', '14', '440', '1080*2400'),
    DeviceHardware('OnePlus', 'CPH2449', '34', '14', '480', '1240*2772'),
    DeviceHardware('Google', 'Pixel 7', '33', '13', '420', '1080*2400'),
    DeviceHardware('Samsung', 'SM-G998B', '33', '13', '480', '1440*3200'),
    DeviceHardware('Xiaomi', 'MI 13', '33', '13', '440', '1080*2400'),
    DeviceHardware('OnePlus', 'NE2215', '33', '13', '420', '1080*2400'),
)


@dataclass
class AppConfig:
    sadcaptcha_key: str = ''
    hlr_api_key: str = ''
    hlr_api_url: str = 'https://hlrdeep.com/api/public/v1/hlr/check'
    number_api_base: str = ''
    number_api_key: str = ''
    claim_count: int = 10
    lease_seconds: int = 600
    max_retries: int = 3
    request_timeout: int = 15
    delay_min: float = 0.5
    delay_max: float = 2.0
    device_pool_path: str = 'device_pool.json'
    device_pool_size: int = 50
    global_rps: float = 10.0
    global_burst: int = 20
    default_version: str = '37.0.4'
    ms_token_max_uses: int = MS_TOKEN_MAX_USES
    device_max_uses: int = DEVICE_MAX_USES_PER_SESSION
    recovery_max_uses: int = RECOVERY_MAX_USES_PER_SESSION
    include_deprecated_endpoints: bool = False
    endpoint_fallback_delay: float = 1.5
    device_file: str = ''
    devices: Tuple[DeviceHardware, ...] = _DEFAULT_DEVICES
    mcc_mnc: Tuple[Tuple[str, Tuple[str, ...]], ...] = (
        ('US', ('310260', '310410', '311480')),
        ('GB', ('23410', '23415', '23420')),
        ('DE', ('26201', '26202', '26203')),
        ('FR', ('20801', '20810', '20820')),
        ('RU', ('25001', '25002', '25099')),
        ('UA', ('25501', '25503', '25506')),
        ('IN', ('40401', '40410', '40445')),
        ('BR', ('72405', '72410', '72411')),
        ('AT', ('23201', '23203', '23205')),
        ('VN', ('45201', '45202', '45204')),
        ('TR', ('28601', '28602', '28603')),
        ('PL', ('26001', '26002', '26003')),
        ('IT', ('22201', '22210', '22288')),
        ('ES', ('21401', '21403', '21407')),
        ('NL', ('20404', '20408', '20412')),
        ('BE', ('20601', '20605', '20610')),
    )
    api_hosts: Tuple[str, ...] = (
        'api16-normal-c-useast1a.tiktokv.com',
        'api22-normal-c-useast1a.tiktokv.com',
        'api19-normal-c-useast1a.tiktokv.com',
        'api16-normal-c-useast2a.tiktokv.com',
        'api16-normal-va.tiktokv.com',
        'api16-normal-c-alisg.tiktokv.com',
        'api16-normal-no1a.tiktokv.eu',
    )

    def _validate_apk(self):
        if self.default_version not in _APK_VERSION_MAP:
            raise ConfigError('Unknown version: ' + self.default_version)
        ver = get_apk_version(self.default_version)
        if ver.stability == 'unverified':
            log.warning('APK %s unverified with SignerPy', ver.version_name)

    def validate(self, mode='csv'):
        missing = []
        if mode in ('csv', 'api'):
            if not self.sadcaptcha_key: missing.append('sadcaptcha_key')
            if not self.hlr_api_key: missing.append('hlr_api_key')
        if mode == 'api':
            if not self.number_api_base: missing.append('number_api_base')
            if not self.number_api_key: missing.append('number_api_key')
        if mode == 'prewarm':
            if not self.sadcaptcha_key: missing.append('sadcaptcha_key')
        if missing:
            raise ConfigError('Missing: ' + ', '.join(missing))
        self._validate_apk()

    def validate_recovery(self, need_number_api=False):
        missing = []
        if not self.hlr_api_key: missing.append('hlr_api_key')
        if need_number_api:
            if not self.number_api_base: missing.append('number_api_base')
            if not self.number_api_key: missing.append('number_api_key')
        if missing:
            raise ConfigError('Missing: ' + ', '.join(missing))
        self._validate_apk()
        if not self.sadcaptcha_key:
            log.warning('No sadcaptcha_key. Captcha by rotation.')

    def get_mcc_mnc(self, region):
        for code, mncs in self.mcc_mnc:
            if code == region:
                return mncs
        return ('310260',)

    def random_device_hw(self, apk_ver=None):
        if apk_ver:
            c = [d for d in self.devices if apk_ver.is_device_compatible(int(d.os_api))]
            if c:
                return random.choice(c)
        return random.choice(self.devices)

    def get_default_apk_version(self):
        return get_apk_version(self.default_version)

    def random_host(self):
        return random.choice(self.api_hosts)

    def with_overrides(self, **kw):
        return replace(self, **kw)


def load_config(path='config.json'):
    overrides = {}
    valid_keys = {f.name for f in fields(AppConfig)
                  if f.name not in ('devices', 'mcc_mnc', 'api_hosts')}
    if os.path.exists(path):
        try:
            with open(path, 'r', encoding='utf-8') as f:
                raw = json.load(f)
            unknown = [k for k in raw if k not in valid_keys]
            if unknown:
                log.warning('Config: unknown keys: %s', ', '.join(sorted(unknown)))
            overrides = {k: v for k, v in raw.items() if k in valid_keys}
            log.info('Config: %s', path)
        except (json.JSONDecodeError, IOError) as exc:
            log.warning('Config error: %s', exc)
    for env_key, conf_key in {
        'SADCAPTCHA_KEY': 'sadcaptcha_key', 'HLR_API_KEY': 'hlr_api_key',
        'HLR_API_URL': 'hlr_api_url', 'NUMBER_API_BASE': 'number_api_base',
        'NUMBER_API_KEY': 'number_api_key', 'DEVICE_POOL_PATH': 'device_pool_path',
        'DEVICE_FILE': 'device_file',
    }.items():
        val = os.environ.get(env_key)
        if val:
            overrides[conf_key] = val
    return AppConfig(**overrides)


# ============================================
#  EXTERNAL DEVICE POOL
# ============================================

@dataclass
class ExternalDevice:
    device_id: str
    install_id: str
    device_type: str
    device_brand: str
    openudid: str
    cdid: str


def load_external_devices(path):
    if not os.path.exists(path):
        raise ConfigError('Device file not found: ' + path)
    devices, skipped = [], 0
    with open(path, 'r', encoding='utf-8') as f:
        for line in f:
            s = line.strip()
            if not s or s.startswith('#'):
                continue
            parts = s.split(':')
            if len(parts) < 6:
                skipped += 1; continue
            did, iid = parts[0].strip(), parts[1].strip()
            if not did or not iid:
                skipped += 1; continue
            devices.append(ExternalDevice(
                did, iid, parts[2].strip(), parts[3].strip(),
                parts[4].strip(), ':'.join(p.strip() for p in parts[5:])))
    if skipped:
        log.warning('Device file: skipped %d', skipped)
    log.info('Device file: loaded %d from %s', len(devices), path)
    return devices


class ExternalDevicePool:
    def __init__(self, devices):
        self._queue = asyncio.Queue()
        self._all_ids = set()
        self._checked_out = {}
        self._removed = set()
        self._lock = asyncio.Lock()
        for d in devices:
            self._queue.put_nowait(d)
            self._all_ids.add(d.device_id)

    @property
    def size(self):
        return len(self._all_ids) - len(self._removed)

    @property
    def is_empty(self):
        return self.size <= 0

    async def checkout(self):
        while True:
            try:
                d = self._queue.get_nowait()
            except asyncio.QueueEmpty:
                return None
            async with self._lock:
                if d.device_id in self._removed:
                    self._all_ids.discard(d.device_id)
                    self._removed.discard(d.device_id)
                    continue
                self._checked_out[d.device_id] = d
            return d

    async def checkin(self, device_id):
        async with self._lock:
            d = self._checked_out.pop(device_id, None)
            if d and device_id not in self._removed:
                self._queue.put_nowait(d)

    async def remove(self, device_id):
        async with self._lock:
            self._removed.add(device_id)
            self._checked_out.pop(device_id, None)

    async def checkout_or_wait(self, timeout=30.0):
        deadline = time.monotonic() + timeout
        while True:
            if is_shutdown():
                return None
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return None
            try:
                d = await asyncio.wait_for(self._queue.get(), timeout=min(remaining, 2.0))
            except asyncio.TimeoutError:
                continue
            async with self._lock:
                if d.device_id in self._removed:
                    self._all_ids.discard(d.device_id)
                    self._removed.discard(d.device_id)
                    continue
                self._checked_out[d.device_id] = d
            return d


def build_device_from_external(ext, config, region='US'):
    ver = config.get_default_apk_version()
    matched = None
    eb, et = ext.device_brand.lower(), ext.device_type.lower()
    for hw in config.devices:
        if hw.brand.lower() == eb and hw.model.lower() == et and ver.is_device_compatible(int(hw.os_api)):
            matched = hw; break
    if not matched:
        for hw in config.devices:
            if hw.brand.lower() == eb and ver.is_device_compatible(int(hw.os_api)):
                matched = hw; break
    if not matched:
        c = [d for d in config.devices if ver.is_device_compatible(int(d.os_api))]
        matched = random.choice(c) if c else config.devices[0]
    d = Device(
        device_id=ext.device_id, install_id=ext.install_id,
        openudid=ext.openudid, cdid=ext.cdid,
        device_type=ext.device_type, device_brand=ext.device_brand,
        os_version=matched.os_version, os_api=matched.os_api,
        dpi=matched.dpi, resolution=matched.resolution,
        version_name=ver.version_name, version_code=ver.version_code,
        manifest_version_code=ver.manifest_version_code,
        region=region, mcc_mnc=random.choice(config.get_mcc_mnc(region)),
        registered=True)
    d._ms_token_max_uses = config.ms_token_max_uses
    return d


# ============================================
#  NUMBER API
# ============================================

class NumberAPI:
    def __init__(self, config):
        self.base_url = config.number_api_base.rstrip('/')
        self._headers = {'X-API-Key': config.number_api_key, 'Content-Type': 'application/json'}

    async def _post(self, session, endpoint, payload):
        url = self.base_url + endpoint
        for attempt in range(3):
            check_shutdown()
            try:
                async with session.post(url, headers=self._headers, json=payload,
                                        timeout=aiohttp.ClientTimeout(total=15)) as resp:
                    if resp.status == 200:
                        return await resp.json()
                    if resp.status in (400, 401, 409):
                        return None
                    if resp.status in RETRYABLE_HTTP_CODES:
                        await asyncio.sleep(jitter_delay(attempt)); continue
                    return None
            except (asyncio.TimeoutError, aiohttp.ServerTimeoutError):
                await asyncio.sleep(jitter_delay(attempt, 0.5))
            except aiohttp.ClientError as exc:
                raise NetworkError('NumberAPI: ' + str(exc)) from exc
            except ShutdownError:
                raise
            except Exception as exc:
                raise NetworkError('NumberAPI: ' + str(exc)) from exc
        return None

    async def claim(self, session, count=10, lease_seconds=600):
        data = await self._post(session, '/v1/numbers/claim', {
            'count': max(1, min(count, 500)),
            'leaseSeconds': max(30, min(lease_seconds, 86400))})
        if data:
            log.info('Claimed %d', len(data.get('items', [])))
        return data

    async def report(self, session, claim_id, results):
        if not results:
            return {'updated': 0}
        return await self._post(session, '/v1/numbers/report', {
            'claimId': claim_id, 'results': results[:500]})


# ============================================
#  DEVICE
# ============================================

_PRIVATE_SERIALIZED_FIELDS = {'_ms_token_max_uses': ('ms_token_max_uses', MS_TOKEN_MAX_USES)}


@dataclass
class Device:
    device_id: str = ''
    install_id: str = ''
    openudid: str = ''
    cdid: str = ''
    device_type: str = ''
    device_brand: str = ''
    os_version: str = ''
    os_api: str = ''
    dpi: str = ''
    resolution: str = ''
    version_name: str = ''
    version_code: str = ''
    manifest_version_code: str = ''
    region: str = 'US'
    mcc_mnc: str = ''
    registered: bool = False
    ms_token: str = ''
    ms_token_time: float = 0.0
    ms_token_uses: int = 0
    last_used: float = 0.0
    use_count: int = 0
    session_uses: int = 0
    _ms_token_max_uses: int = MS_TOKEN_MAX_USES

    @classmethod
    def generate(cls, config, region='US'):
        ver = config.get_default_apk_version()
        hw = config.random_device_hw(apk_ver=ver)
        d = cls(
            device_id=_generate_device_id(), install_id=_generate_device_id(),
            openudid=_generate_openudid(), cdid=_generate_cdid(),
            device_type=hw.model, device_brand=hw.brand,
            os_version=hw.os_version, os_api=hw.os_api,
            dpi=hw.dpi, resolution=hw.resolution,
            version_name=ver.version_name, version_code=ver.version_code,
            manifest_version_code=ver.manifest_version_code,
            region=region, mcc_mnc=random.choice(config.get_mcc_mnc(region)))
        d._ms_token_max_uses = config.ms_token_max_uses
        return d

    @classmethod
    def generate_lightweight(cls, config, region='US'):
        d = cls.generate(config, region)
        d.registered = False
        return d

    def to_dict(self):
        result = {f.name: getattr(self, f.name) for f in fields(self) if not f.name.startswith('_')}
        for internal, (key, _) in _PRIVATE_SERIALIZED_FIELDS.items():
            result[key] = getattr(self, internal)
        return result

    @classmethod
    def from_dict(cls, data, ms_token_max_uses=MS_TOKEN_MAX_USES):
        valid = {f.name for f in fields(cls) if not f.name.startswith('_')}
        d = cls(**{k: v for k, v in data.items() if k in valid})
        for internal, (key, default) in _PRIVATE_SERIALIZED_FIELDS.items():
            stored = data.get(key)
            try:
                setattr(d, internal, int(stored) if stored is not None else ms_token_max_uses)
            except (ValueError, TypeError):
                setattr(d, internal, default)
        return d

    @property
    def apk_version(self):
        return get_apk_version(self.version_name)

    @property
    def ms_token_valid(self):
        return (bool(self.ms_token)
                and (time.time() - self.ms_token_time) < MS_TOKEN_TTL_SECONDS
                and self.ms_token_uses < self._ms_token_max_uses)

    def invalidate_ms_token(self):
        self.ms_token = ''
        self.ms_token_time = 0.0
        self.ms_token_uses = 0

    def set_ms_token(self, token):
        if not token:
            return
        if token != self.ms_token:
            self.ms_token = token
            self.ms_token_time = time.time()
            self.ms_token_uses = 0
        else:
            self.ms_token_time = time.time()

    def record_ms_token_use(self):
        self.ms_token_uses += 1

    def record_session_use(self):
        self.session_uses += 1

    def needs_rotation(self, max_uses):
        return self.session_uses >= max_uses

    @property
    def user_agent(self):
        ver = self.apk_version
        return ('com.zhiliaoapp.musically/' + ver.manifest_version_code
                + ' (Linux; U; Android ' + self.os_version + '; en; '
                + self.device_type + '; Build/' + DEVICE_ROM_BUILD
                + ';tt-ok/' + ver.tt_ok_version + ')')

    def base_params(self, frozen_ts_ms=None, frozen_ts_s=None):
        ver = self.apk_version
        now_ms = frozen_ts_ms or str(int(time.time() * 1000))
        now_s = frozen_ts_s or str(int(time.time()))
        p = {
            'passport-sdk-version': ver.passport_sdk_version,
            'iid': self.install_id, 'device_id': self.device_id,
            'ac': 'wifi', 'channel': APP_CHANNEL, 'aid': APP_AID_STR,
            'app_name': 'musical_ly', 'version_code': self.version_code,
            'version_name': self.version_name, 'device_platform': 'android',
            'os': 'android', 'ab_version': self.version_name, 'ssmix': 'a',
            'device_type': self.device_type, 'device_brand': self.device_brand,
            'language': 'en', 'os_api': self.os_api, 'os_version': self.os_version,
            'openudid': self.openudid,
            'manifest_version_code': self.manifest_version_code,
            'resolution': self.resolution, 'dpi': self.dpi,
            'update_version_code': self.manifest_version_code,
            '_rticket': now_ms, 'is_pad': '0', 'current_region': self.region,
            'app_type': 'normal', 'sys_region': self.region,
            'mcc_mnc': self.mcc_mnc, 'timezone_name': 'America/New_York',
            'residence': self.region, 'app_language': 'en',
            'carrier_region': self.region, 'ac2': 'wifi', 'uoo': '0',
            'op_region': self.region, 'timezone_offset': '-14400',
            'build_number': self.version_name, 'host_abi': DEVICE_CPU_ABI,
            'locale': 'en', 'region': self.region, 'ts': now_s, 'cdid': self.cdid,
        }
        if self.ms_token_valid:
            p['msToken'] = self.ms_token
        return p

    def base_query_string(self, frozen_ts_ms=None, frozen_ts_s=None):
        return urlencode(self.base_params(frozen_ts_ms, frozen_ts_s))

    def captcha_query_string(self, extra, frozen_ts_ms=None, frozen_ts_s=None):
        params = self.base_params(frozen_ts_ms, frozen_ts_s)
        params.update(extra)
        return urlencode(params)

    def registration_payload(self):
        ver = self.apk_version
        return {
            'magic_tag': 'ss_app_log',
            'header': {
                'display_name': APP_DISPLAY_NAME,
                'update_version_code': ver.manifest_int,
                'manifest_version_code': ver.manifest_int,
                'aid': APP_AID, 'channel': APP_CHANNEL, 'package': APP_PACKAGE,
                'app_version': ver.version_name, 'version_code': ver.version_code_int,
                'sdk_version': APP_SDK_VERSION, 'os': 'Android',
                'os_version': self.os_version, 'os_api': self.os_api,
                'device_model': self.device_type, 'device_brand': self.device_brand,
                'device_manufacturer': self.device_brand, 'cpu_abi': DEVICE_CPU_ABI,
                'release_build': '1', 'density_dpi': int(self.dpi),
                'display_density': 'xhdpi', 'resolution': self.resolution,
                'language': 'en', 'timezone': -5, 'access': 'wifi',
                'not_request_sender': 0, 'rom': DEVICE_ROM_BUILD,
                'rom_version': self.os_version, 'openudid': self.openudid,
                'cdid': self.cdid, 'sig_hash': ver.sig_hash,
                'region': self.region, 'app_language': 'en', 'locale': 'en',
                'sys_region': self.region, 'carrier_region': self.region,
                'mcc_mnc': self.mcc_mnc,
            },
            '_gen_time': int(time.time()),
        }

    def xlog_payload(self):
        ver = self.apk_version
        return {
            'magic_tag': 'ss_app_log',
            'header': {
                'display_name': APP_DISPLAY_NAME,
                'update_version_code': ver.manifest_int,
                'manifest_version_code': ver.manifest_int,
                'aid': APP_AID, 'channel': APP_CHANNEL, 'package': APP_PACKAGE,
                'app_version': ver.version_name, 'version_code': ver.version_code_int,
                'sdk_version': APP_SDK_VERSION, 'os': 'Android',
                'os_version': self.os_version, 'os_api': self.os_api,
                'device_model': self.device_type, 'device_brand': self.device_brand,
                'device_manufacturer': self.device_brand, 'cpu_abi': DEVICE_CPU_ABI,
                'release_build': '1', 'density_dpi': int(self.dpi),
                'display_density': 'xhdpi', 'resolution': self.resolution,
                'language': 'en', 'timezone': -5, 'access': 'wifi',
                'not_request_sender': 0, 'rom': DEVICE_ROM_BUILD,
                'rom_version': self.os_version, 'openudid': self.openudid,
                'cdid': self.cdid, 'sig_hash': ver.sig_hash,
                'region': self.region, 'app_language': 'en', 'locale': 'en',
                'sys_region': self.region, 'carrier_region': self.region,
                'mcc_mnc': self.mcc_mnc,
                'device_id': self.device_id, 'install_id': self.install_id,
            },
            '_gen_time': int(time.time()),
        }


# ============================================
#  DEVICE POOL
# ============================================

def _validate_device_dict(data):
    if not isinstance(data, dict):
        return False
    if not DEVICE_POOL_REQUIRED_KEYS.issubset(data.keys()):
        return False
    return isinstance(data.get('device_id'), str) and isinstance(data.get('registered'), bool)


class DevicePool:
    def __init__(self, config):
        self.config = config
        self.path = config.device_pool_path
        self._pool = {}
        self._lock = asyncio.Lock()
        self._dirty = False
        self._saving = False
        self._load_sync()

    def _load_sync(self):
        if not os.path.exists(self.path):
            return
        try:
            with open(self.path, 'r', encoding='utf-8') as f:
                raw = json.load(f)
            if not isinstance(raw, dict):
                return
            total = 0
            for region, dl in raw.items():
                if isinstance(dl, list):
                    valid = [d for d in dl if _validate_device_dict(d)]
                    if valid:
                        self._pool[region] = valid
                        total += len(valid)
            log.info('Pool: %d devices, %d regions', total, len(self._pool))
        except (json.JSONDecodeError, IOError) as exc:
            log.warning('Pool load: %s', exc)

    def _save_sync(self):
        try:
            tmp = self.path + '.tmp'
            with open(tmp, 'w', encoding='utf-8') as f:
                json.dump(self._pool, f, indent=2)
                f.flush(); os.fsync(f.fileno())
            os.replace(tmp, self.path)
        except IOError as exc:
            log.error('Pool save: %s', exc)

    async def save(self, force=False):
        async with self._lock:
            if self._saving or (not self._dirty and not force):
                return
            self._saving = True; self._dirty = False
        try:
            await run_in_io(self._save_sync)
        finally:
            async with self._lock:
                self._saving = False

    async def get(self, region):
        async with self._lock:
            registered = [d for d in self._pool.get(region, []) if d.get('registered')]
            if not registered:
                return None
            chosen = min(registered, key=lambda d: d.get('last_used', 0.0))
            chosen['last_used'] = time.time()
            chosen['use_count'] = chosen.get('use_count', 0) + 1
            self._dirty = True
            return Device.from_dict(dict(chosen), ms_token_max_uses=self.config.ms_token_max_uses)

    async def add(self, device):
        async with self._lock:
            dd = device.to_dict()
            if not _validate_device_dict(dd):
                return
            region = device.region
            if region not in self._pool:
                self._pool[region] = []
            existing = {d.get('device_id') for d in self._pool[region]}
            if device.device_id in existing:
                for i, ex in enumerate(self._pool[region]):
                    if ex.get('device_id') == device.device_id:
                        self._pool[region][i] = dd; self._dirty = True; return
                return
            self._pool[region].append(dd)
            mx = self.config.device_pool_size
            if len(self._pool[region]) > mx:
                self._pool[region].sort(key=lambda d: d.get('use_count', 0))
                self._pool[region] = self._pool[region][:mx]
            self._dirty = True

    async def update(self, device):
        async with self._lock:
            region = device.region
            if region not in self._pool:
                return
            new = device.to_dict()
            if not _validate_device_dict(new):
                return
            for i, ex in enumerate(self._pool[region]):
                if ex.get('device_id') == device.device_id:
                    self._pool[region][i] = new; self._dirty = True; return

    async def remove(self, device):
        async with self._lock:
            region = device.region
            if region in self._pool:
                self._pool[region] = [d for d in self._pool[region]
                                      if d.get('device_id') != device.device_id]
                self._dirty = True

    async def count(self, region=None):
        async with self._lock:
            if region:
                return len([d for d in self._pool.get(region, []) if d.get('registered')])
            return sum(len([d for d in v if d.get('registered')]) for v in self._pool.values())


# ============================================
#  CAPTCHA
# ============================================

class CaptchaSolver:
    BASE_URL = 'https://www.sadcaptcha.com/api/v1'

    def __init__(self, config):
        self.api_key = config.sadcaptcha_key
        self._balance = -1

    @property
    def has_key(self):
        return bool(self.api_key)

    async def check_balance(self, session):
        if not self.api_key:
            return -1
        try:
            async with session.get(
                self.BASE_URL + '/license/credits',
                params={'licenseKey': self.api_key},
                timeout=aiohttp.ClientTimeout(total=10)
            ) as resp:
                if resp.status == 200:
                    data = await resp.json()
                    self._balance = data.get('credits', 0)
                    log.info('Captcha balance: %d', self._balance)
                    return self._balance
                return -1
        except Exception as exc:
            log.warning('Captcha balance: %s', exc)
            return -1

    async def solve(self, subtype, session, phone='', **kwargs):
        if self._balance == 0:
            raise CaptchaError('Balance 0')
        if not self.api_key:
            raise CaptchaError('No captcha key')
        ep_map = {'3d': '/shapes', 'shapes': '/shapes', 'slide': '/puzzle',
                  'puzzle': '/puzzle', 'rotate': '/rotate', 'icon': '/icon'}
        endpoint = ep_map.get(subtype)
        if not endpoint:
            raise CaptchaError('Unknown: ' + subtype)
        pl_map = {
            '/shapes': {'imageB64': kwargs.get('image_b64', '')},
            '/puzzle': {'puzzleImageB64': kwargs.get('puzzle_b64', ''),
                        'pieceImageB64': kwargs.get('piece_b64', '')},
            '/rotate': {'outerImageB64': kwargs.get('outer_b64', ''),
                        'innerImageB64': kwargs.get('inner_b64', '')},
            '/icon': {'challenge': kwargs.get('challenge', ''),
                      'imageB64': kwargs.get('image_b64', '')},
        }
        timeout = CAPTCHA_TIMEOUTS.get(subtype, CAPTCHA_TIMEOUT_DEFAULT)
        for attempt in range(3):
            try:
                async with session.post(
                    self.BASE_URL + endpoint, params={'licenseKey': self.api_key},
                    json=pl_map[endpoint], timeout=aiohttp.ClientTimeout(total=timeout)
                ) as resp:
                    if resp.status == 200:
                        return await resp.json()
                    if resp.status in RETRYABLE_HTTP_CODES:
                        await asyncio.sleep(jitter_delay(attempt)); continue
                    raise CaptchaError(str(resp.status))
            except (asyncio.TimeoutError, aiohttp.ServerTimeoutError):
                await asyncio.sleep(jitter_delay(attempt, 0.5))
            except (ShutdownError, CaptchaError):
                raise
            except Exception as exc:
                raise CaptchaError(str(exc)) from exc
        raise CaptchaError('Max retries')


# ============================================
#  TIKTOK SMS ENGINE
# ============================================

class TikTokSMS:
    """TikTok SMS engine. NOT safe for concurrent use."""

    def __init__(self, config, connector, proxy_mgr, captcha, hlr, pool, limiter, ext_pool=None):
        self.config = config
        self._connector = connector
        self.proxy = proxy_mgr
        self.captcha = captcha
        self.hlr = hlr
        self.pool = pool
        self.limiter = limiter
        self.ext_pool = ext_pool
        self.api_host = config.random_host()
        self.device = None
        self._ext_device_id = None
        self._cookie_jar = aiohttp.CookieJar(unsafe=True)
        self._session = None

    async def __aenter__(self):
        return self

    async def __aexit__(self, *exc):
        await self.close()

    async def _get_session(self):
        if self._session is None or self._session.closed:
            self._session = aiohttp.ClientSession(
                connector=self._connector, connector_owner=False,
                cookie_jar=self._cookie_jar)
        return self._session

    async def close(self):
        if self._session and not self._session.closed:
            await self._session.close()
            self._session = None

    def _on_device_switch(self, new_host=None):
        self._cookie_jar.clear()
        if self.device:
            self.device.invalidate_ms_token()
        if new_host is not None:
            self.api_host = new_host

    def _freeze_timestamps(self):
        now = time.time()
        return str(int(now)), str(int(now * 1000))

    async def _request(self, method, path, body=None,
                       content_type=None, proxy_url=None, phone='',
                       parse_json=True, aid=APP_AID, base_host=None,
                       allow_redirects=True):
        """Core HTTP request with signing.

        v13.9: added allow_redirects parameter. For registration/xlog
        requests this is set to False so we can handle redirects manually
        and avoid proxy SSL failures on redirected hostnames.
        """
        await self.limiter.acquire()
        check_shutdown()
        session = await self._get_session()
        base_url = ('https://' + base_host + path) if base_host else path

        body_info = _classify_body(method, body)
        ms_token_recorded = False

        for attempt in range(self.config.max_retries):
            check_shutdown()
            frozen_ts_s, frozen_ts_ms = self._freeze_timestamps()
            params_str = self.device.base_query_string(frozen_ts_ms, frozen_ts_s)
            full_url = base_url + '?' + params_str

            # Build sign_params based on SIGNER_URL_MODE
            sign_params = _make_sign_params(base_url, params_str)

            headers = _build_signing_headers(
                params_str=sign_params,
                body_info=body_info,
                user_agent=self.device.user_agent,
                frozen_ts_s=frozen_ts_s,
                frozen_ts_ms=frozen_ts_ms)

            if content_type:
                headers['Content-Type'] = content_type
            elif body_info.raw_data is not None:
                if isinstance(body_info.raw_data, str):
                    headers['Content-Type'] = 'application/x-www-form-urlencoded; charset=UTF-8'
                elif isinstance(body_info.raw_data, bytes):
                    headers['Content-Type'] = 'application/octet-stream'

            if self.device and self.device.ms_token_valid and not ms_token_recorded:
                headers[MS_TOKEN_HEADER] = self.device.ms_token
                self.device.record_ms_token_use()
                ms_token_recorded = True
            elif self.device and self.device.ms_token_valid:
                headers[MS_TOKEN_HEADER] = self.device.ms_token

            try:
                kw = {'headers': headers,
                      'timeout': aiohttp.ClientTimeout(total=self.config.request_timeout),
                      'allow_redirects': allow_redirects}
                if proxy_url:
                    kw['proxy'] = proxy_url
                if body_info.is_post and body_info.raw_data is not None:
                    kw['data'] = body_info.raw_data
                fn = session.post if body_info.is_post else session.get
                # Use yarl URL with encoded=True to prevent aiohttp
                # from re-encoding query parameters (would break signature)
                request_url = YarlURL(full_url, encoded=True)

                # === FULL REQUEST DEBUG (for author) ===
                if attempt == 0 and not isinstance(body_info.raw_data, bytes):
                    log.info('=== REQUEST DEBUG ===')
                    log.info('METHOD: %s', method)
                    log.info('SIGN_PARAMS: %s', sign_params[:500])
                    log.info('FULL_URL: %s', full_url[:500])
                    log.info('BODY: %s', str(body_info.raw_data)[:300] if body_info.raw_data else 'None')
                    _hdr_safe = {}
                    for k, v in headers.items():
                        _hdr_safe[k] = v[:80] if isinstance(v, str) and len(v) > 80 else v
                    log.info('HEADERS: %s', json.dumps(_hdr_safe, ensure_ascii=False))
                    log.info('=== END DEBUG ===')

                async with fn(request_url, **kw) as resp:
                    # DEBUG: compare actual URL sent vs what we signed
                    if attempt == 0:
                        actual_url = str(resp.url)
                        if actual_url != full_url:
                            log.warning('URL MISMATCH! signed=%s...  actual=%s...',
                                        full_url[:120], actual_url[:120])
                    self._extract_ms_token(resp)

                    # v13.9: detect redirect when allow_redirects=False
                    if not allow_redirects and resp.status in REDIRECT_HTTP_CODES:
                        location = resp.headers.get('Location', '')
                        raise NetworkError(
                            'redirect:%d->%s' % (resp.status, location),
                            retryable=True)

                    if resp.status in RETRYABLE_HTTP_CODES:
                        if resp.status == HTTP_TOO_MANY_REQUESTS:
                            await self.limiter.slow_down()
                        await asyncio.sleep(jitter_delay(attempt))
                        continue
                    await self.proxy.report_success(proxy_url)
                    if parse_json:
                        resp_data = await resp.json(content_type=None)
                        # DEBUG: log response for first attempt
                        if attempt == 0 and not isinstance(body_info.raw_data, bytes):
                            log.info('RESPONSE[%d]: %s', resp.status,
                                     json.dumps(resp_data, ensure_ascii=False)[:400] if isinstance(resp_data, dict) else str(resp_data)[:400])
                        return resp_data
                    return await resp.read()
            except (asyncio.TimeoutError, aiohttp.ServerTimeoutError):
                await self.proxy.report_failure(proxy_url)
                await asyncio.sleep(jitter_delay(attempt, 0.5))
            except aiohttp.ClientProxyConnectionError:
                await self.proxy.report_failure(proxy_url)
                new = await self.proxy.get(self.device.region if self.device else None)
                if new:
                    proxy_url = new
                await asyncio.sleep(jitter_delay(attempt, 0.5))
            except aiohttp.ClientError as exc:
                await self.proxy.report_failure(proxy_url)
                raise NetworkError(str(exc)) from exc
            except (ShutdownError, SignerError):
                raise
            except NetworkError:
                raise
            except Exception as exc:
                raise NetworkError(str(exc)) from exc
        raise NetworkError('Max retries', retryable=False)

    def _extract_ms_token(self, resp):
        token = None
        for c in resp.cookies.values():
            if c.key == MS_TOKEN_COOKIE_NAME:
                token = c.value; break
        if not token:
            token = resp.headers.get(MS_TOKEN_HEADER, '') or None
        if not token:
            try:
                filtered = self._cookie_jar.filter_cookies(str(resp.url))
                ms = filtered.get(MS_TOKEN_COOKIE_NAME) if filtered else None
                if ms and ms.value:
                    token = ms.value
            except Exception:
                pass
        if token and self.device:
            self.device.set_ms_token(token)

    async def _ensure_ms_token(self, proxy_url=None, phone=''):
        if self.device.ms_token_valid:
            return True, ''
        self.device.invalidate_ms_token()
        errors = []
        for ep in ('/passport/user/info/', '/passport/app/region_setting/'):
            try:
                await self._request('GET', 'https://' + self.api_host + ep,
                                    proxy_url=proxy_url, phone=phone)
            except (NetworkError, SignerError) as exc:
                errors.append('%s: %s' % (ep, exc))
            if self.device.ms_token_valid:
                return True, ''
        reason = '; '.join(errors) if errors else 'no token'
        log.warning('[%s] msToken failed: %s', mask_phone(phone), reason)
        return False, reason

    # v13.9: completely rewritten _register_device with redirect handling
    # and detailed error logging
    async def _register_device(self, proxy_url=None, phone=''):
        masked = mask_phone(phone)
        host_errors: List[str] = []  # v13.9: collect per-host errors

        # Build full host list including any discovered redirect targets
        hosts_to_try: List[str] = list(DEVICE_REGISTER_HOSTS)
        tried_hosts: Set[str] = set()

        for reg_host in hosts_to_try:
            if reg_host in tried_hosts:
                continue
            tried_hosts.add(reg_host)
            check_shutdown()

            reg_payload = self.device.registration_payload()
            try:
                encrypted = signer_encrypt(reg_payload)
            except SignerError as exc:
                raise DeviceError('Register encrypt: ' + str(exc)) from exc

            try:
                # v13.9: allow_redirects=False to handle redirects manually
                raw = await self._request(
                    'POST', DEVICE_REGISTER_PATH, encrypted,
                    content_type='application/octet-stream;tt-data=a',
                    proxy_url=proxy_url, phone=phone,
                    parse_json=False, base_host=reg_host,
                    allow_redirects=False)
            except NetworkError as exc:
                err_str = str(exc)
                # v13.9: detect redirect and add target host to rotation
                if err_str.startswith('redirect:'):
                    # Extract redirected host from error message
                    # Format: "redirect:3xx->https://new-host/path"
                    redirect_url = err_str.split('->', 1)[-1] if '->' in err_str else ''
                    redirect_host = _extract_redirect_host(
                        {'Location': redirect_url}, reg_host)
                    if redirect_host and redirect_host not in tried_hosts:
                        log.info('[%s] %s redirected to %s, will try directly',
                                 masked, reg_host, redirect_host)
                        hosts_to_try.append(redirect_host)
                        host_errors.append('%s: redirect->%s' % (reg_host, redirect_host))
                    else:
                        host_errors.append('%s: redirect (no usable target)' % reg_host)
                else:
                    host_errors.append('%s: %s' % (reg_host, err_str))
                    log.warning('[%s] Register %s: %s', masked, reg_host, err_str)
                continue
            except SignerError as exc:
                raise DeviceError('Register signer: ' + str(exc)) from exc

            if not raw:
                host_errors.append('%s: empty response' % reg_host)
                continue

            # Parse response
            data = None
            try:
                data = json.loads(raw)
            except (json.JSONDecodeError, ValueError):
                if HAS_EDATA_DECRYPT:
                    try:
                        data = json.loads(signer_decrypt(raw))
                    except (SignerError, json.JSONDecodeError, ValueError) as exc:
                        host_errors.append('%s: decrypt failed: %s' % (reg_host, exc))
                        raise ParseError('Register decrypt: ' + str(exc)) from exc
                else:
                    host_errors.append('%s: not JSON, no edata' % reg_host)
                    raise ParseError('Register not JSON, edata unavailable')

            if not isinstance(data, dict):
                host_errors.append('%s: response not dict' % reg_host)
                raise ParseError('Register: not dict')

            did = data.get('device_id', 0)
            if did and did != 0:
                self.device.device_id = str(did)
                self.device.install_id = str(data.get('install_id', 0))
                self.device.registered = True
                log.info('[%s] Registered: %s via %s', masked,
                         self.device.device_id, reg_host)
                return True

            # v13.9: detailed error logging instead of just "?"
            error_summary = _summarize_response(data)
            host_errors.append('%s: %s' % (reg_host, error_summary))
            log.error('[%s] Register %s: %s', masked, reg_host, error_summary)
            continue

        # v13.9: log collected errors summary when all hosts failed
        if host_errors:
            log.warning('[%s] All register hosts failed: %s',
                        masked, ' | '.join(host_errors))
        return False

    # v13.9: _send_xlog also uses allow_redirects=False and detailed logging
    async def _send_xlog(self, proxy_url=None, phone=''):
        masked = mask_phone(phone)
        host_errors: List[str] = []

        hosts_to_try: List[str] = list(DEVICE_REGISTER_HOSTS)
        tried_hosts: Set[str] = set()

        for host in hosts_to_try:
            if host in tried_hosts:
                continue
            tried_hosts.add(host)

            payload = self.device.xlog_payload()
            try:
                encrypted = signer_encrypt(payload)
            except SignerError as exc:
                log.warning('[%s] XLog encrypt: %s', masked, exc)
                return False

            try:
                raw = await self._request(
                    'POST', XLOG_PATH, encrypted,
                    content_type='application/octet-stream;tt-data=a',
                    proxy_url=proxy_url, phone=phone,
                    parse_json=False, base_host=host,
                    allow_redirects=False)
                if raw:
                    log.info('[%s] XLog OK via %s', masked, host)
                    return True
                host_errors.append('%s: empty' % host)
            except NetworkError as exc:
                err_str = str(exc)
                if err_str.startswith('redirect:'):
                    redirect_url = err_str.split('->', 1)[-1] if '->' in err_str else ''
                    redirect_host = _extract_redirect_host(
                        {'Location': redirect_url}, host)
                    if redirect_host and redirect_host not in tried_hosts:
                        log.info('[%s] XLog %s redirected to %s',
                                 masked, host, redirect_host)
                        hosts_to_try.append(redirect_host)
                        host_errors.append('%s: redirect->%s' % (host, redirect_host))
                    else:
                        host_errors.append('%s: redirect (dead end)' % host)
                else:
                    host_errors.append('%s: %s' % (host, err_str))
                    log.warning('[%s] XLog %s: %s', masked, host, err_str)
            except SignerError as exc:
                host_errors.append('%s: signer %s' % (host, exc))
                log.warning('[%s] XLog %s: signer %s', masked, host, exc)

        if host_errors:
            log.warning('[%s] All XLog hosts failed: %s',
                        masked, ' | '.join(host_errors))
        return False

    async def _activate_device(self, proxy_url=None, phone=''):
        await self._send_xlog(proxy_url, phone)
        try:
            return await self._solve_captcha_flow(
                '3d', '', self.device.region, '', 'device_activate', proxy_url, phone)
        except CaptchaError as exc:
            log.warning('[%s] Activation captcha: %s', mask_phone(phone), exc)
            return False

    async def _fetch_image_b64(self, url):
        if not url:
            return ''
        session = await self._get_session()
        try:
            async with session.get(url, timeout=aiohttp.ClientTimeout(total=10)) as resp:
                if resp.status == 200:
                    return base64.b64encode(await resp.read()).decode()
        except Exception as exc:
            log.warning('Fetch image: %s', exc)
        return ''

    async def _solve_captcha_flow(self, subtype, detail, region, verify_event,
                                  scene='device_activate', proxy_url=None, phone=''):
        frozen_ts_s, frozen_ts_ms = self._freeze_timestamps()
        captcha_extra = {
            'aid': APP_AID_STR, 'host': self.api_host, 'scene': scene,
            'device_id': self.device.device_id, 'install_id': self.device.install_id,
            'region': region or 'useast2b', 'subtype': subtype,
            'detail': detail, 'lang': 'en', 'os': 'android',
        }
        captcha_params = self.device.captcha_query_string(
            captcha_extra, frozen_ts_ms, frozen_ts_s)

        get_info = _classify_body('GET', None)
        captcha_sign = _make_sign_params(URL_CAPTCHA_GET, captcha_params)
        headers = _build_signing_headers(
            captcha_sign, get_info, self.device.user_agent, frozen_ts_s, frozen_ts_ms)

        session = await self._get_session()
        try:
            async with session.get(
                URL_CAPTCHA_GET + '?' + captcha_params, headers=headers,
                proxy=proxy_url, timeout=aiohttp.ClientTimeout(total=self.config.request_timeout)
            ) as resp:
                self._extract_ms_token(resp)
                if resp.status != 200:
                    raise CaptchaError('HTTP %d' % resp.status)
                challenge = await resp.json(content_type=None)
        except (CaptchaError, ShutdownError, SignerError):
            raise
        except Exception as exc:
            raise CaptchaError('Challenge: ' + str(exc)) from exc

        if not challenge or not isinstance(challenge, dict):
            raise CaptchaError('Challenge empty')
        cd = extract_optional_dict(challenge, 'data', 'captcha') or challenge
        question = extract_optional_dict(cd, 'question', 'captcha') if isinstance(cd, dict) else None
        if not question:
            return True

        rs = cd.get('subtype', subtype) or subtype
        url1 = question.get('url1', '') or question.get('url', '')
        url2 = question.get('url2', '')
        kwargs = {}
        if rs in ('3d', 'shapes') and url1:
            img = await self._fetch_image_b64(url1)
            if img: kwargs['image_b64'] = img
        elif rs in ('slide', 'puzzle') and url1 and url2:
            p, pc = await asyncio.gather(self._fetch_image_b64(url1), self._fetch_image_b64(url2))
            if p and pc: kwargs['puzzle_b64'] = p; kwargs['piece_b64'] = pc
        elif rs == 'rotate' and url1 and url2:
            o, i = await asyncio.gather(self._fetch_image_b64(url1), self._fetch_image_b64(url2))
            if o and i: kwargs['outer_b64'] = o; kwargs['inner_b64'] = i
        elif rs == 'icon' and url1:
            img = await self._fetch_image_b64(url1)
            if img: kwargs['image_b64'] = img; kwargs['challenge'] = question.get('tip_text', '')
        if not kwargs:
            raise CaptchaError('No captcha images')
        solution = await self.captcha.solve(rs, session, phone=phone, **kwargs)
        if not solution:
            raise CaptchaError('Solver empty')

        verify_ts_s, verify_ts_ms = self._freeze_timestamps()
        verify_params = self.device.captcha_query_string(
            {'aid': APP_AID_STR, 'host': self.api_host}, verify_ts_ms, verify_ts_s)
        verify_body = json.dumps({
            'solution': solution, 'detail': detail, 'verify_event': verify_event})

        post_info = _classify_body('POST', verify_body)
        verify_sign = _make_sign_params(URL_CAPTCHA_VERIFY, verify_params)
        verify_headers = _build_signing_headers(
            verify_sign, post_info, self.device.user_agent, verify_ts_s, verify_ts_ms)
        verify_headers['Content-Type'] = 'application/json'

        try:
            async with session.post(
                URL_CAPTCHA_VERIFY + '?' + verify_params, headers=verify_headers,
                data=verify_body, proxy=proxy_url,
                timeout=aiohttp.ClientTimeout(total=self.config.request_timeout)
            ) as resp:
                self._extract_ms_token(resp)
                vr = await resp.json(content_type=None)
        except (ShutdownError, SignerError):
            raise
        except Exception as exc:
            raise CaptchaError('Verify: ' + str(exc)) from exc
        if not vr or not isinstance(vr, dict):
            raise CaptchaError('Verify empty')
        if vr.get('code') == 200:
            return True
        raise CaptchaError('Verify code=' + str(vr.get('code')))

    async def _handle_sms_captcha(self, response_data, proxy_url=None, phone=''):
        conf = extract_captcha_config(response_data, 'sms_captcha')
        return await self._solve_captcha_flow(
            conf.get('subtype', '3d'), conf.get('detail', ''),
            conf.get('region', ''), conf.get('verify_event', ''),
            'passport_mobile_send_code', proxy_url, phone)

    async def _checkout_external(self, country, proxy_url=None, phone=''):
        if not self.ext_pool or self.ext_pool.is_empty:
            return False
        ext = await self.ext_pool.checkout_or_wait(timeout=10.0)
        if not ext:
            return False
        if self._ext_device_id:
            await self.ext_pool.checkin(self._ext_device_id)
        self._ext_device_id = ext.device_id
        self.device = build_device_from_external(ext, self.config, country)
        self.device.session_uses = 0
        self._on_device_switch(self.config.random_host())
        await self._ensure_ms_token(proxy_url, phone)
        return True

    async def _get_or_create_device(self, country, proxy_url=None, phone=''):
        if await self._checkout_external(country, proxy_url, phone):
            return True
        pooled = await self.pool.get(country)
        if pooled:
            self.device = pooled
            self.device.session_uses = 0
            self._on_device_switch(self.config.random_host())
            await self._ensure_ms_token(proxy_url, phone)
            return True
        self.device = Device.generate(self.config, country)
        self._on_device_switch(self.config.random_host())
        try:
            if not await self._register_device(proxy_url, phone):
                raise DeviceError('Registration failed')
        except ParseError as exc:
            raise DeviceError(str(exc)) from exc
        activated = await self._activate_device(proxy_url, phone)
        await self.pool.add(self.device)
        if not activated:
            log.warning('[%s] Activation failed, saved registered', mask_phone(phone))
        await self._ensure_ms_token(proxy_url, phone)
        return True

    async def _rotate_device(self, country, proxy_url=None, phone=''):
        if self._ext_device_id and self.ext_pool:
            await self.ext_pool.checkin(self._ext_device_id)
            self._ext_device_id = None
        if self.device:
            await self.pool.remove(self.device)
        return await self._get_or_create_device(country, proxy_url, phone)

    async def _get_lightweight_device(self, country, proxy_url=None, phone=''):
        if await self._checkout_external(country, proxy_url, phone):
            return True
        self.device = Device.generate_lightweight(self.config, country)
        self.device.session_uses = 0
        self._on_device_switch(self.config.random_host())
        try:
            if await self._register_device(proxy_url, phone):
                await self._send_xlog(proxy_url, phone)
                await self.pool.add(self.device)
        except (ParseError, DeviceError) as exc:
            log.warning('[%s] Lightweight reg: %s', mask_phone(phone), exc)
        await self._ensure_ms_token(proxy_url, phone)
        return True

    async def _rotate_lightweight(self, country, proxy_url=None, phone=''):
        if self._ext_device_id and self.ext_pool:
            await self.ext_pool.checkin(self._ext_device_id)
            self._ext_device_id = None
        if self.device and self.device.registered:
            await self.pool.update(self.device)
        return await self._get_lightweight_device(country, proxy_url, phone)

    async def _setup_for_send(self, phone):
        session = await self._get_session()
        info = await self.hlr.lookup(session, phone)
        if not info:
            raise HLRError('No data for ' + mask_phone(phone))
        log.info('[%s] %s +%s (%s)', mask_phone(phone),
                 info.country_name, info.country_prefix, info.carrier)
        return info.country_code, info.country_prefix, info.national_number, await self.proxy.get(info.country_code)

    async def _send_on_endpoint(self, phone, endpoint, sms_type, country,
                                prefix, national, proxy_url, extra_body,
                                is_lw, max_uses, event_tag):
        masked = mask_phone(phone)
        captcha_attempts = captcha_rotations = 0
        aid = endpoint.preferred_aid if endpoint.preferred_aid != APP_AID else APP_AID
        last_ec = 0
        had_response = False

        for attempt in range(self.config.max_retries):
            check_shutdown()
            if self.device.needs_rotation(max_uses):
                if is_lw: await self._rotate_lightweight(country, proxy_url, phone)
                else: await self._rotate_device(country, proxy_url, phone)
            await self._ensure_ms_token(proxy_url, phone)
            self.device.record_session_use()

            body = build_body_for_endpoint(endpoint, sms_type, prefix, national, extra_body)
            try:
                data = await self._request(
                    'POST', 'https://' + self.api_host + endpoint.path,
                    body, proxy_url=proxy_url, phone=phone, aid=aid)
            except NetworkError as exc:
                if exc.retryable:
                    await asyncio.sleep(random.uniform(self.config.delay_min, self.config.delay_max))
                    continue
                raise
            if not data or not isinstance(data, dict):
                await asyncio.sleep(random.uniform(self.config.delay_min, self.config.delay_max))
                continue

            had_response = True
            ec = extract_error_code(data, 'sms')
            last_ec = ec
            msg = str(data.get('message', '')).lower()

            if ec == 0:
                return {'status': 'success', 'error_code': 0,
                        'timestamp': int(time.time()), 'endpoint_tier': endpoint.tier}, False
            if ec == TT_CAPTCHA_REQUIRED:
                captcha_attempts += 1
                if captcha_attempts > MAX_CAPTCHA_ATTEMPTS:
                    raise CaptchaError('Captcha loop')
                if not self.captcha.has_key:
                    captcha_rotations += 1
                    if captcha_rotations > MAX_CAPTCHA_ROTATIONS_NO_KEY:
                        raise CaptchaError('No key')
                    if self.device and self.device.registered:
                        await self.pool.update(self.device)
                    if is_lw: await self._rotate_lightweight(country, proxy_url, phone)
                    else: await self._rotate_device(country, proxy_url, phone)
                    continue
                try:
                    if await self._handle_sms_captcha(data, proxy_url, phone): continue
                except (CaptchaError, ParseError): pass
                if self.device and self.device.registered:
                    await self.pool.update(self.device)
                if is_lw: await self._rotate_lightweight(country, proxy_url, phone)
                else: await self._rotate_device(country, proxy_url, phone)
                continue
            if ec in TT_RATE_LIMIT_CODES:
                await self.limiter.slow_down()
                if ec in TT_ANTI_SPAM_CODES: return None, True
                await asyncio.sleep(jitter_delay(attempt, 2.0, 15.0)); continue
            if ec == TT_DEVICE_BAN:
                if self.ext_pool and self._ext_device_id:
                    await self.ext_pool.remove(self._ext_device_id)
                    self._ext_device_id = None
                if is_lw: await self._rotate_lightweight(country, proxy_url, phone)
                else: await self._rotate_device(country, proxy_url, phone)
                return None, True
            if ec in TT_MSTOKEN_ERRORS:
                self.device.invalidate_ms_token()
                ok, _ = await self._ensure_ms_token(proxy_url, phone)
                if ok: continue
                raise TokenError('msToken ec=' + str(ec))
            if ec == -1 and 'success' in msg:
                return {'status': 'success', 'error_code': 0,
                        'timestamp': int(time.time()), 'endpoint_tier': endpoint.tier}, False
            # v13.9: log full response summary on unknown error codes
            log.error('[%s] ec=%d tier-%d: %s', masked, ec, endpoint.tier,
                      _summarize_response(data))
            return {'status': 'fail', 'error_code': ec,
                    'timestamp': int(time.time()), 'endpoint_tier': endpoint.tier}, False

        return {'status': 'fail',
                'error_code': last_ec if had_response and last_ec != 0 else ERR_MAX_RETRIES,
                'timestamp': int(time.time()), 'endpoint_tier': endpoint.tier}, True

    async def _send_with_fallback(self, phone, event_cfg, country, prefix, national,
                                  proxy_url, result, extra, is_lw, max_uses, event_tag):
        chain = build_endpoint_chain(event_cfg, self.config.include_deprecated_endpoints, event_tag)
        if not chain:
            raise EndpointExhaustedError('No endpoints for "%s"' % event_tag)
        last = None
        for idx, (ep, st) in enumerate(chain):
            check_shutdown()
            if idx > 0:
                self._on_device_switch(self.config.random_host())
                await asyncio.sleep(self.config.endpoint_fallback_delay)
                if is_lw: await self._rotate_lightweight(country, proxy_url, phone)
                elif self.device.needs_rotation(max_uses):
                    await self._rotate_device(country, proxy_url, phone)
            try:
                ep_result, fb = await self._send_on_endpoint(
                    phone, ep, st, country, prefix, national, proxy_url,
                    extra, is_lw, max_uses, event_tag)
            except (CaptchaError, TokenError, NetworkError, SignerError) as exc:
                log.warning('[%s] tier-%d: %s', mask_phone(phone), ep.tier, exc); continue
            if ep_result:
                last = ep_result
                if ep_result.get('status') == 'success' or not fb:
                    result.update(ep_result); return result
        if last:
            result.update(last)
        if result['status'] != 'success' and result['error_code'] == 0:
            result['error_code'] = ERR_ALL_ENDPOINTS_FAILED
        return result

    async def _checkin_external_device(self):
        if self._ext_device_id and self.ext_pool:
            try: await self.ext_pool.checkin(self._ext_device_id)
            except Exception as exc: log.warning('ext checkin: %s', exc)
            finally: self._ext_device_id = None

    async def send_event(self, phone, event='recovery'):
        is_lw = event in LIGHTWEIGHT_EVENTS
        event_cfg = get_event_config(event)
        result = {'phone': phone, 'status': 'fail', 'error_code': 0,
                  'timestamp': int(time.time()), 'event': event}
        try:
            validate_phone(phone); check_shutdown()
            country, prefix, national, proxy_url = await self._setup_for_send(phone)
            if is_lw:
                if not await self._get_lightweight_device(country, proxy_url, phone):
                    raise DeviceError('Lightweight failed')
                max_uses = self.config.recovery_max_uses
            else:
                if not await self._get_or_create_device(country, proxy_url, phone):
                    raise DeviceError('Device failed')
                max_uses = self.config.device_max_uses
            extra = EVENT_EXTRA_PARAMS.get(event, {'account_sdk_source': 'app', 'mix_mode': 1, 'multi_login': 1})
            return await self._send_with_fallback(
                phone, event_cfg, country, prefix, national, proxy_url, result, extra, is_lw, max_uses, event)
        except ShutdownError: result['error_code'] = ERR_SHUTDOWN
        except HLRError: result['error_code'] = ERR_HLR_FAILED
        except DeviceError: result['error_code'] = ERR_DEVICE_SETUP
        except CaptchaError: result['error_code'] = ERR_CAPTCHA_LOOP
        except TokenError: result['error_code'] = ERR_MSTOKEN
        except SignerError: result['error_code'] = ERR_SIGNER
        except EndpointExhaustedError: result['error_code'] = ERR_ALL_ENDPOINTS_FAILED
        except NetworkError: result['error_code'] = ERR_MAX_RETRIES
        except ConfigError: result['error_code'] = ERR_HLR_FAILED
        except Exception as exc:
            log.error('[%s] %s: %s', mask_phone(phone), type(exc).__name__, exc)
            result['error_code'] = ERR_CRASH
        finally:
            await self._checkin_external_device()
            if self.device and self.device.registered:
                await self.pool.update(self.device)
        return result


# ============================================
#  RESULT WRITER
# ============================================

def read_numbers(path):
    numbers, seen = [], set()
    with open(path, 'r', encoding='utf-8') as f:
        for row in csv.reader(f):
            if row:
                num = row[0].strip()
                if num and not num.startswith('#') and num not in seen:
                    numbers.append(num); seen.add(num)
    log.info('Loaded %d unique from %s', len(numbers), path)
    return numbers


class ResultWriter:
    def __init__(self, sp, fp):
        self._lock = asyncio.Lock()
        self._sp, self._fp = sp, fp
        self._sf = self._ff = self._sw = self._fw = None
        self.success = self.fail = 0
        self._wc = 0

    def _open_sync(self):
        sf = ff = None
        try:
            sf = open(self._sp, 'w', newline='', encoding='utf-8')
            ff = open(self._fp, 'w', newline='', encoding='utf-8')
            sw, fw = csv.writer(sf), csv.writer(ff)
            sw.writerow(['phone', 'event', 'tier', 'timestamp'])
            fw.writerow(['phone', 'event', 'error_code', 'tier', 'timestamp'])
            sf.flush(); ff.flush(); os.fsync(sf.fileno()); os.fsync(ff.fileno())
            self._sf, self._ff, self._sw, self._fw = sf, ff, sw, fw
        except Exception:
            for f in (sf, ff):
                if f:
                    try: f.close()
                    except Exception: pass
            raise

    async def open(self):
        await run_in_io(self._open_sync)

    def _write_sync(self, ok, row):
        (self._sw if ok else self._fw).writerow(row)
        (self._sf if ok else self._ff).flush()
        self._wc += 1
        if self._wc >= FSYNC_INTERVAL:
            os.fsync(self._sf.fileno()); os.fsync(self._ff.fileno())
            self._wc = 0

    async def write(self, result):
        async with self._lock:
            ok = result['status'] == 'success'
            event, tier = result.get('event', '?'), result.get('endpoint_tier', '?')
            row = ([result['phone'], event, tier, result['timestamp']] if ok
                   else [result['phone'], event, result['error_code'], tier, result['timestamp']])
            if ok: self.success += 1
            else: self.fail += 1
            await run_in_io(self._write_sync, ok, row)
            total = self.success + self.fail
            if total % 25 == 0:
                log.info('Progress: %d, %d ok, %d fail', total, self.success, self.fail)

    def _close_sync(self):
        for f in (self._sf, self._ff):
            if f:
                try: f.flush(); os.fsync(f.fileno()); f.close()
                except Exception: pass

    async def close(self):
        await run_in_io(self._close_sync)

    def summary(self):
        total = self.success + self.fail
        log.info('DONE: %d total, %d ok (%.1f%%), %d fail',
                 total, self.success, (self.success / total * 100) if total else 0, self.fail)


# ============================================
#  RESOURCE GUARD & RUNNER
# ============================================

class ResourceGuard:
    def __init__(self):
        self._pool = self._writer = self._connector = None
        self._sessions = []
        self._tasks = set()

    def register(self, pool=None, writer=None, connector=None, session=None):
        if pool: self._pool = pool
        if writer: self._writer = writer
        if connector: self._connector = connector
        if session: self._sessions.append(session)

    def register_task(self, task):
        self._tasks.add(task)
        task.add_done_callback(self._tasks.discard)

    async def cleanup(self):
        log.info('Cleaning up...')
        active = [t for t in self._tasks if not t.done()]
        if active:
            for t in active: t.cancel()
            await asyncio.wait(active, timeout=30.0)
        self._tasks.clear()
        if self._pool:
            try: await self._pool.save(force=True)
            except Exception as exc: log.error('Pool save: %s', exc)
        if self._writer:
            try: self._writer.summary(); await self._writer.close()
            except Exception: pass
        for s in self._sessions:
            if s and not s.closed:
                try: await s.close()
                except Exception: pass
        if self._connector and not self._connector.closed:
            try: await self._connector.close()
            except Exception: pass


async def run_batched(items, worker, batch_size=TASK_BATCH_SIZE, guard=None):
    processed = 0
    for start in range(0, len(items), batch_size):
        if is_shutdown(): break
        batch = items[start:start + batch_size]
        tasks = []
        for item in batch:
            if is_shutdown(): break
            task = asyncio.create_task(worker(item))
            if guard: guard.register_task(task)
            tasks.append(task)
        if tasks:
            done, _ = await asyncio.wait(tasks, return_when=asyncio.ALL_COMPLETED)
            for t in done:
                exc = t.exception()
                if exc and not isinstance(exc, (ShutdownError, asyncio.CancelledError)):
                    log.error('Task: %s', exc)
            processed += len(done)
    return processed


# ============================================
#  PROCESS CSV / API / PREWARM
# ============================================

async def process_csv(config, numbers, proxies=None, event='register',
                      threads=5, success_file='success.csv', fail_file='failed.csv'):
    _setup_signals_if_main()
    is_lw = event in LIGHTWEIGHT_EVENTS
    if is_lw: config.validate_recovery()
    else: config.validate('csv')
    ext_pool = None
    if config.device_file:
        try:
            devs = load_external_devices(config.device_file)
            if devs: ext_pool = ExternalDevicePool(devs)
        except ConfigError as exc: log.error('Device file: %s', exc); return
    writer = ResultWriter(success_file, fail_file)
    await writer.open()
    pool = DevicePool(config)
    connector = aiohttp.TCPConnector(limit=threads * 3, enable_cleanup_closed=True)
    guard = ResourceGuard()
    guard.register(pool=pool, writer=writer, connector=connector)
    sem = asyncio.Semaphore(threads)
    captcha = CaptchaSolver(config)
    hlr = HLRLookup(config)
    proxy_mgr = ProxyManager(proxies)
    limiter = RateLimiter(config.global_rps, config.global_burst)
    if captcha.has_key:
        async with aiohttp.ClientSession() as cs:
            if await captcha.check_balance(cs) == 0: await guard.cleanup(); return
    try:
        async def worker(phone):
            if is_shutdown(): return
            async with sem:
                if is_shutdown(): return
                async with TikTokSMS(config, connector, proxy_mgr, captcha,
                                     hlr, pool, limiter, ext_pool=ext_pool) as client:
                    await writer.write(await client.send_event(phone, event))
                await asyncio.sleep(random.uniform(config.delay_min, config.delay_max))
        await run_batched(numbers, worker, guard=guard)
    except asyncio.CancelledError: pass
    except Exception as exc: log.error('CSV: %s', exc)
    finally: await guard.cleanup()


def _make_api_worker(config, connector, proxy_mgr, captcha, hlr, pool,
                     limiter, ext_pool, sem, writer, event, batch_results, batch_lock):
    async def worker(item):
        if is_shutdown(): return
        phone, nid = item['phone'], item['id']
        async with sem:
            if is_shutdown(): return
            async with TikTokSMS(config, connector, proxy_mgr, captcha,
                                 hlr, pool, limiter, ext_pool=ext_pool) as client:
                result = await client.send_event(phone, event)
                await writer.write(result)
            entry = {'id': int(nid), 'status': result['status']}
            if result['status'] == 'fail': entry['note'] = 'ec=' + str(result['error_code'])
            async with batch_lock: batch_results.append(entry)
    return worker


async def process_api(config, proxies=None, event='register', threads=5,
                      claim_count=10, lease_seconds=600,
                      success_file='success.csv', fail_file='failed.csv'):
    _setup_signals_if_main()
    is_lw = event in LIGHTWEIGHT_EVENTS
    if is_lw: config.validate_recovery(need_number_api=True)
    else: config.validate('api')
    ext_pool = None
    if config.device_file:
        try:
            devs = load_external_devices(config.device_file)
            if devs: ext_pool = ExternalDevicePool(devs)
        except ConfigError as exc: log.error('Device file: %s', exc); return
    writer = ResultWriter(success_file, fail_file)
    await writer.open()
    pool = DevicePool(config)
    connector = aiohttp.TCPConnector(limit=threads * 3, enable_cleanup_closed=True)
    guard = ResourceGuard()
    guard.register(pool=pool, writer=writer, connector=connector)
    sem = asyncio.Semaphore(threads)
    captcha = CaptchaSolver(config)
    hlr = HLRLookup(config)
    proxy_mgr = ProxyManager(proxies)
    limiter = RateLimiter(config.global_rps, config.global_burst)
    number_api = NumberAPI(config)
    if captcha.has_key:
        async with aiohttp.ClientSession() as cs:
            if await captcha.check_balance(cs) == 0: await guard.cleanup(); return
    api_session = aiohttp.ClientSession(connector=connector, connector_owner=False)
    guard.register(session=api_session)
    empty_streak = 0
    try:
        while not is_shutdown():
            try: cd = await number_api.claim(api_session, claim_count, lease_seconds)
            except (NetworkError, AppError):
                empty_streak += 1
                if empty_streak >= MAX_EMPTY_CLAIMS: break
                await asyncio.sleep(min(2 ** empty_streak, 30)); continue
            if not cd or not cd.get('items'):
                empty_streak += 1
                if empty_streak >= MAX_EMPTY_CLAIMS: break
                await asyncio.sleep(min(2 ** empty_streak, 30)); continue
            empty_streak = 0
            batch_results, batch_lock = [], asyncio.Lock()
            await run_batched(cd['items'],
                              _make_api_worker(config, connector, proxy_mgr, captcha, hlr, pool,
                                               limiter, ext_pool, sem, writer, event,
                                               batch_results, batch_lock),
                              guard=guard)
            if batch_results and not is_shutdown():
                try: await number_api.report(api_session, cd.get('claimId', ''), batch_results)
                except (NetworkError, AppError): pass
            await pool.save()
            await asyncio.sleep(random.uniform(1.0, 3.0))
    except asyncio.CancelledError: pass
    except Exception as exc: log.error('API: %s', exc)
    finally: await guard.cleanup()


# v13.9: prewarm with detailed per-device error reporting
async def prewarm_pool(config, proxies=None, count=10, regions=None):
    _setup_signals_if_main()
    config.validate('prewarm')
    if not regions: regions = ['US', 'GB', 'DE', 'AT', 'VN', 'TR', 'BR']
    proxy_mgr, pool = ProxyManager(proxies), DevicePool(config)
    limiter, captcha, hlr = RateLimiter(5.0, 10), CaptchaSolver(config), HLRLookup(config)
    connector = aiohttp.TCPConnector(limit=20, enable_cleanup_closed=True)
    guard = ResourceGuard()
    guard.register(pool=pool, connector=connector)
    try:
        sem = asyncio.Semaphore(5)
        async def register_one(wi):
            region, index = wi
            async with sem:
                if is_shutdown(): return
                await limiter.acquire()
                tag = '[pw-%s-%d]' % (region, index)
                async with TikTokSMS(config, connector, proxy_mgr, captcha, hlr, pool, limiter) as client:
                    client.device = Device.generate(config, region)
                    client._on_device_switch(config.random_host())
                    purl = await proxy_mgr.get(region)
                    try:
                        if await client._register_device(purl):
                            activated = await client._activate_device(purl)
                            await pool.add(client.device)
                            log.info('%s %s %s', tag,
                                     'OK' if activated else 'registered (no activation)',
                                     client.device.device_id)
                        else:
                            # v13.9: FAIL already has detailed per-host
                            # errors logged by _register_device
                            log.warning('%s FAIL: all registration hosts exhausted', tag)
                    except DeviceError as exc:
                        log.error('%s DeviceError: %s', tag, exc)
                    except Exception as exc:
                        log.error('%s %s: %s', tag, type(exc).__name__, exc)
                await asyncio.sleep(random.uniform(0.5, 1.5))
        await run_batched([(r, i) for r in regions for i in range(count)], register_one, guard=guard)
    finally: await guard.cleanup()
    log.info('Pool: %d devices', await pool.count())


# ============================================
#  DEPENDENCY CHECK
# ============================================

def check_dependencies(apk_ver=None):
    try:
        ver = apk_ver or DEFAULT_APK_VERSION
        signerpy_ver = None
        try:
            import SignerPy as _sp
            signerpy_ver = getattr(_sp, '__version__', getattr(_sp, 'VERSION', None))
        except Exception: pass
        log.info('SignerPy: %s', signerpy_ver or 'unknown')
        modules = ['sign']
        if HAS_SIGNERPY_GET: modules.append('get')
        if HAS_TTENCRYPT: modules.append('ttencrypt')
        if HAS_ENC: modules.append('enc')
        if HAS_EDATA_DECRYPT: modules.append('edata')
        log.info('Modules: %s', ', '.join(modules))

        test_params = _build_test_params(ver=ver)

        log.info('Testing sign(params=..., payload="", version=%d)...', SIGNER_GORGON_VERSION)
        result = signer_sign(params=test_params, payload='')
        if not result.get('x-argus'): log.error('x-argus missing'); return False
        if not result.get('x-gorgon'): log.error('x-gorgon missing'); return False
        log.info('x-argus: %d chars, x-gorgon: %s...', len(result.get('x-argus', '')),
                 result.get('x-gorgon', '')[:12])

        test_body = 'type=5&mobile=123'
        log.info('Testing sign(payload="%s")...', test_body)
        body_result = signer_sign(params=test_params, payload=test_body)
        manual_stub = _compute_ss_stub_str(test_body)
        signer_stub = body_result.get('x-ss-stub', '')
        if signer_stub == manual_stub:
            log.info('x-ss-stub matches: %s', manual_stub[:16])
        else:
            log.info('x-ss-stub: signer=%s manual=%s (using manual)',
                     signer_stub[:16] if signer_stub else 'empty', manual_stub[:16])

        test_binary = b'\x00\x01\x02\xff\xfe\xfd'
        bin_info = _classify_body('POST', test_binary)
        assert bin_info.sign_payload == '', 'Binary should have empty sign_payload'
        assert bin_info.ss_stub == hashlib.md5(test_binary).hexdigest().upper()
        assert bin_info.raw_data is test_binary, 'Binary raw_data should be original bytes'
        log.info('Binary body classification OK (sign_payload empty, stub from bytes)')

        txt_info = _classify_body('POST', test_body)
        assert txt_info.sign_payload == test_body, 'Text should have body as sign_payload'
        assert txt_info.raw_data == test_body
        log.info('Text body classification OK (sign_payload = body)')

        if HAS_SIGNERPY_GET:
            try:
                gr = signer_get(params=test_params)
                log.info('get() OK: x-gorgon=%s', 'present' if gr.get('x-gorgon') else 'missing')
            except Exception as exc:
                log.warning('get() failed: %s', exc)

        try:
            enc = signer_encrypt({'magic_tag': 'test', 'header': {'aid': APP_AID}})
            log.info('TTEncrypt OK: %d bytes', len(enc))
            enc_info = _classify_body('POST', enc)
            assert enc_info.sign_payload == '', 'Encrypted should classify as binary'
            log.info('Encrypted payload classification OK')
        except SignerError as exc:
            log.warning('Encryption: %s', exc)

        # v13.9: test _summarize_response
        test_resp = {'error_code': 1105, 'message': '', 'data': {'error_code': 40001}}
        summary = _summarize_response(test_resp)
        assert '1105' in summary and '40001' in summary
        log.info('Response summarizer OK: %s', summary)

        log.info('SignerPy OK (ver=%s, gorgon=%d, sign_mode=%s)',
                 ver.version_name, SIGNER_GORGON_VERSION, SIGNER_URL_MODE)
        return True
    except ImportError as exc:
        log.error('SignerPy not installed: %s', exc); return False
    except SignerError as exc:
        log.error('SignerPy: %s', exc); return False
    except Exception as exc:
        log.error('SignerPy: %s: %s', type(exc).__name__, exc); return False


# ============================================
#  CLI
# ============================================

def parse_proxies(proxy_arg=None, proxy_file=None):
    proxies = []
    if proxy_arg: proxies.append(proxy_arg)
    if proxy_file and os.path.exists(proxy_file):
        with open(proxy_file, 'r', encoding='utf-8') as f:
            for line in f:
                s = line.strip()
                if s and not s.startswith('#'): proxies.append(s)
    return proxies or None


def main():
    _setup_signals()
    parser = argparse.ArgumentParser(description='TikTok SMS v13.9')
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument('--input', '-i', default=None)
    source.add_argument('--api', action='store_true')
    source.add_argument('--prewarm', action='store_true')
    parser.add_argument('--event', '-e', default='register', choices=list(VALID_EVENTS))
    parser.add_argument('--success', '-s', default='success.csv')
    parser.add_argument('--fail', '-f', default='failed.csv')
    parser.add_argument('--proxy', '-p', default=None)
    parser.add_argument('--proxy-file', default=None)
    parser.add_argument('--threads', '-t', type=int, default=5)
    parser.add_argument('--config', '-c', default='config.json')
    parser.add_argument('--claim-count', type=int, default=None)
    parser.add_argument('--lease-seconds', type=int, default=None)
    parser.add_argument('--pool-count', type=int, default=10)
    parser.add_argument('--pool-regions', nargs='+', default=None)
    parser.add_argument('--rps', type=float, default=None)
    parser.add_argument('--skip-check', action='store_true')
    parser.add_argument('--include-deprecated', action='store_true')
    parser.add_argument('--version', default=None, choices=[v.version_name for v in APK_VERSIONS])
    parser.add_argument('--device-file', default=None)
    parser.add_argument('--sign-mode', default=None,
                        choices=['query', 'path_query', 'full_url'],
                        help='What to pass to sign(params=): query, path_query, or full_url')

    args = parser.parse_args()
    config = load_config(args.config)
    overrides = {}
    if args.rps is not None: overrides['global_rps'] = args.rps
    if args.include_deprecated: overrides['include_deprecated_endpoints'] = True
    if args.version: overrides['default_version'] = args.version
    if args.device_file: overrides['device_file'] = args.device_file
    if args.sign_mode:
        global SIGNER_URL_MODE
        SIGNER_URL_MODE = args.sign_mode
        log.info('Sign mode: %s', SIGNER_URL_MODE)
    if overrides: config = config.with_overrides(**overrides)

    if not args.skip_check:
        if not check_dependencies(config.get_default_apk_version()): sys.exit(1)

    proxies = parse_proxies(args.proxy, args.proxy_file)
    cc = args.claim_count if args.claim_count is not None else config.claim_count
    ls = args.lease_seconds if args.lease_seconds is not None else config.lease_seconds
    ver = config.get_default_apk_version()
    log.info('APK: %s (stability=%s)', ver.version_name, ver.stability)
    if ver.is_outdated(VERSION_STALENESS_DAYS):
        log.warning('%s > %dd old', ver.version_name, VERSION_STALENESS_DAYS)

    event = args.event
    chain = build_endpoint_chain(get_event_config(event), config.include_deprecated_endpoints, event)
    log.info('Event: %s (type=%d)', event, get_event_config(event).sms_type)
    log.info('Chain: %s', ' → '.join('t%d(%d)' % (ep.tier, st) for ep, st in chain))

    try:
        if args.prewarm:
            if event in LIGHTWEIGHT_EVENTS: log.warning('Prewarm not needed for %s', event); return
            asyncio.run(prewarm_pool(config, proxies, args.pool_count, args.pool_regions))
        elif args.api:
            asyncio.run(process_api(config, proxies, event, args.threads, cc, ls, args.success, args.fail))
        else:
            numbers = read_numbers(args.input)
            if not numbers: log.error('No numbers'); sys.exit(1)
            asyncio.run(process_csv(config, numbers, proxies, event, args.threads, args.success, args.fail))
    except ConfigError as exc:
        log.error('Config: %s', exc); sys.exit(1)


if __name__ == '__main__':
    main()