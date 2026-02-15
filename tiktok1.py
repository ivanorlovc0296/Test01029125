"""
TikTok SMS Module v10.2

HTTP module for initiating SMS delivery via TikTok's internal API.
Supports CSV and Number API input, device pooling, captcha solving,
proxy rotation, rate limiting, and graceful shutdown.

Uses tiktok-signer for authentication signatures and encryption.
Install: pip install tiktok-signer

Usage:
    python tiktok_sms.py -i numbers.csv --threads 5 -p "host:port:user:pass"
    python tiktok_sms.py --api --claim-count 10 --threads 5
    python tiktok_sms.py --prewarm --pool-count 20

Required: config.json or environment variables for API keys.
"""

import asyncio
import aiohttp
import atexit
import hashlib
import json
import random
import time
import base64
import logging
import csv
import argparse
import sys
import os
import signal
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import urlencode
from dataclasses import dataclass, replace, fields, field
from typing import (
    Optional, List, Any, Dict, Tuple,
    Protocol, runtime_checkable,
)
from tiktok_signer import TikTokSigner

if sys.platform == 'win32':
    asyncio.set_event_loop_policy(
        asyncio.WindowsSelectorEventLoopPolicy())

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s')
log = logging.getLogger('tiktok_sms')


# ============================================
#  CONSTANTS
# ============================================

# TikTok error codes
TT_CAPTCHA_REQUIRED = 1107
TT_DEVICE_BAN = 1109
TT_RATE_LIMIT_CODES = (1105, 2, 3)
TT_MSTOKEN_ERRORS = (1003, 1004)

# Internal error codes
ERR_HLR_FAILED = -1
ERR_DEVICE_SETUP = -2
ERR_MAX_RETRIES = -3
ERR_CAPTCHA_LOOP = -4
ERR_SHUTDOWN = -5
ERR_MSTOKEN = -6
ERR_PROXY_EXHAUSTED = -7
ERR_CONFIG = -8
ERR_CRASH = -99

# HTTP
RETRYABLE_HTTP_CODES = (429, 500, 502, 503, 504)
HTTP_TOO_MANY_REQUESTS = 429

# Limits
MAX_CAPTCHA_ATTEMPTS = 2
MAX_EMPTY_CLAIMS = 3
MAX_PROXY_CONSECUTIVE_FAILS = 3
PROXY_BLACKLIST_BASE_SECONDS = 30
PROXY_BLACKLIST_CAP_SECONDS = 300

# App identity — all str for consistency in
# query params and JSON payloads.
# Use int(APP_AID) where numeric type is needed.
APP_AID = '1233'
APP_PACKAGE = 'com.zhiliaoapp.musically'
APP_DISPLAY_NAME = 'TikTok'
APP_CHANNEL = 'googleplay'
APP_SDK_VERSION = '3.0.0'

# Device hardware
DEVICE_ID_MIN = 7_000_000_000_000_000_000
DEVICE_ID_MAX = 7_999_999_999_999_999_999
DEVICE_ROM_BUILD = 'TP1A.220624.014'
DEVICE_CPU_ABI = 'arm64-v8a'

# Minimum Android API level that all APK
# versions in the registry require. Used in
# Device.generate() to filter incompatible
# hardware profiles.
APK_MIN_SDK = 23


# ============================================
#  APK VERSION REGISTRY
# ============================================
# Each TikTok APK version requires a matched set
# of parameters. Mixing values across versions
# causes X-Argus mismatch (error 1105/1109).
#
# Fields:
#   version_name: APK version string
#   version_code: short code for query params
#   manifest_version_code: from AndroidManifest
#   tt_ok_version: OkHttp interceptor version
#   gorgon_prefix: expected X-Gorgon hex prefix
#   signer_sdk_ver: tiktok-signer sdk_ver param
#   signer_sdk_ver_code: tiktok-signer
#       sdk_ver_code param
#   signer_lc_id: tiktok-signer lc_id param
#   passport_sdk_version: query param value
#   sig_hash: MD5 of APK signing certificate
#   stability: stable | deprecated
#   release_date: YYYY-MM-DD for staleness check
#   target_sdk: target SDK level from manifest

@dataclass(frozen=True)
class APKVersion:
    version_name: str
    version_code: str
    manifest_version_code: str
    tt_ok_version: str
    gorgon_prefix: str
    signer_sdk_ver: str
    signer_sdk_ver_code: int
    signer_lc_id: int
    passport_sdk_version: str
    sig_hash: str
    stability: str
    release_date: str = ''
    target_sdk: int = 35

    @property
    def manifest_int(self) -> int:
        try:
            return int(
                self.manifest_version_code)
        except (ValueError, TypeError):
            return 2024309020

    @property
    def version_code_int(self) -> int:
        try:
            return int(self.version_code)
        except (ValueError, TypeError):
            return 430902

    def is_outdated(
            self, days: int = 90) -> bool:
        """Check if version is older than N days.
        Returns False if release_date not set."""
        if not self.release_date:
            return False
        try:
            from datetime import (
                datetime, timedelta)
            rd = datetime.strptime(
                self.release_date, '%Y-%m-%d')
            return (
                datetime.now() - rd
                > timedelta(days=days))
        except (ValueError, ImportError):
            return False


# MD5 of the APK signing certificate for
# com.zhiliaoapp.musically.
# This is NOT a secret — it's the same for every
# user who installs TikTok from any distribution
# channel. TikTok's server checks it during
# device_register to verify the client is a
# genuine build.
_DEFAULT_SIG_HASH = (
    '194326e82c84a639a52e5c023116f12a')

# Version registry — ordered by preference
# (most recommended first). Default selection
# uses the first entry.
#
# 43.9.2: Current stable, gorgon_prefix 8701
#          confirmed from APK analysis.
#          target_sdk=35, min_sdk=23.
#
# 37.0.4: Legacy fallback. Still works with
#          tiktok-signer but uses older signing
#          algorithm (gorgon 8404).
#
# 37.0.3, 37.0.2: Deprecated — kept for pool
#          backward compatibility only.
APK_VERSIONS: Tuple[APKVersion, ...] = (
    APKVersion(
        version_name='43.9.2',
        version_code='430902',
        manifest_version_code='2024309020',
        tt_ok_version='3.15.2-tiktok',
        gorgon_prefix='8701',
        signer_sdk_ver=(
            'v05.03.00-alpha.5-ov-android'),
        signer_sdk_ver_code=85196064,
        signer_lc_id=2142840551,
        passport_sdk_version='26',
        sig_hash=_DEFAULT_SIG_HASH,
        stability='stable',
        release_date='2025-02-14',
        target_sdk=35,
    ),
    APKVersion(
        version_name='37.0.4',
        version_code='370004',
        manifest_version_code='2023700040',
        tt_ok_version='3.15.1-tiktok',
        gorgon_prefix='8404',
        signer_sdk_ver=(
            'v05.01.02-alpha.7-ov-android'),
        signer_sdk_ver_code=83952160,
        signer_lc_id=2142840551,
        passport_sdk_version='25',
        sig_hash=_DEFAULT_SIG_HASH,
        stability='stable',
        release_date='2024-01-15',
        target_sdk=34,
    ),
    APKVersion(
        version_name='37.0.3',
        version_code='370003',
        manifest_version_code='2023700030',
        tt_ok_version='3.15.1-tiktok',
        gorgon_prefix='8404',
        signer_sdk_ver=(
            'v05.01.02-alpha.7-ov-android'),
        signer_sdk_ver_code=83952160,
        signer_lc_id=2142840551,
        passport_sdk_version='25',
        sig_hash=_DEFAULT_SIG_HASH,
        stability='deprecated',
        release_date='2024-01-10',
        target_sdk=34,
    ),
    APKVersion(
        version_name='37.0.2',
        version_code='370002',
        manifest_version_code='2023700020',
        tt_ok_version='3.15.1-tiktok',
        gorgon_prefix='8404',
        signer_sdk_ver=(
            'v05.01.02-alpha.7-ov-android'),
        signer_sdk_ver_code=83952160,
        signer_lc_id=2142840551,
        passport_sdk_version='25',
        sig_hash=_DEFAULT_SIG_HASH,
        stability='deprecated',
        release_date='2024-01-05',
        target_sdk=34,
    ),
)

# Build lookup by version_name for fast access
_APK_VERSION_MAP: Dict[str, APKVersion] = {
    v.version_name: v for v in APK_VERSIONS
}

# Default version (most recommended)
DEFAULT_APK_VERSION = APK_VERSIONS[0]


def get_apk_version(
        name: str) -> APKVersion:
    """Look up APKVersion by version_name.
    Returns default if not found."""
    return _APK_VERSION_MAP.get(
        name, DEFAULT_APK_VERSION)


# --- ms_token lifecycle ---
#
# ms_token is a server-issued session token
# returned via Set-Cookie or x-ms-token header.
# It has two independent expiry dimensions:
#
# 1. TIME-BASED (TTL): token expires ~270s after
#    issue. After that, TikTok returns 1003/1004.
#
# 2. USE-BASED: even within TTL, TikTok bans
#    tokens after 40-80 requests from the same
#    device+token pair. Symptoms: silent SMS
#    non-delivery (no error code, just no SMS).
#
# We track both via Device.ms_token_time (TTL)
# and Device.ms_token_uses (counter). The
# ms_token_valid property checks BOTH conditions.
# When either is exceeded, _ensure_ms_token()
# fetches a fresh token from /passport/user/info.
#
# MAX_USES is set conservatively below the
# observed ban threshold to maintain delivery.
MS_TOKEN_TTL_SECONDS = 270
MS_TOKEN_MAX_USES = 35
MS_TOKEN_COOKIE_NAME = 'msToken'
MS_TOKEN_HEADER = 'x-ms-token'

# --- Device rotation ---
#
# TikTok fingerprints devices and applies
# progressive throttling: after ~50-80 SMS
# requests from one device_id, delivery rate
# drops sharply. We rotate proactively before
# hitting that threshold.
DEVICE_MAX_USES_PER_SESSION = 45

# Captcha timeouts per type (seconds)
CAPTCHA_TIMEOUTS: Dict[str, int] = {
    '3d': 45, 'shapes': 45,
    'slide': 20, 'puzzle': 20,
    'rotate': 25, 'icon': 30,
}
CAPTCHA_TIMEOUT_DEFAULT = 30

# Rate limiter
RATE_LIMIT_BACKOFF_FACTOR = 0.7
RATE_LIMIT_MIN_RPS = 1.0

# Task batching
TASK_BATCH_SIZE = 50

# PII masking
PII_VISIBLE_CHARS = 4

# Device pool validation
DEVICE_POOL_REQUIRED_KEYS = frozenset({
    'device_id', 'install_id', 'registered',
    'version_name', 'device_type', 'region',
})

# TikTok API endpoints
URL_DEVICE_REGISTER = (
    'https://log-boot.tiktokv.com'
    '/service/2/device_register/')
URL_CAPTCHA_GET = (
    'https://verify.tiktok.com/captcha/get')
URL_CAPTCHA_VERIFY = (
    'https://verify.tiktok.com/captcha/verify')

# Version staleness warning threshold (days)
VERSION_STALENESS_DAYS = 90


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
    if len(clean) <= PII_VISIBLE_CHARS * 2:
        return clean[:2] + '***'
    prefix = clean[:3]
    suffix = clean[-PII_VISIBLE_CHARS:]
    mid = len(clean) - len(prefix) - len(suffix)
    return f'{prefix}{"*" * mid}{suffix}'


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


class ParseError(AppError):
    """JSON/response parsing failures."""


class DeviceError(AppError):
    """Device registration or activation failure."""


class CaptchaError(AppError):
    """Captcha solving failure."""


class ProxyError(AppError):
    """All proxies exhausted."""


class TokenError(AppError):
    """ms_token acquisition failure."""


class ShutdownError(AppError):
    """Graceful shutdown in progress."""


class ConfigError(AppError):
    """Missing or invalid configuration."""


class HLRError(AppError):
    """HLR lookup returned no data or failed."""


# ============================================
#  SHUTDOWN
# ============================================

shutdown_event = asyncio.Event()


def _setup_signals():
    def _handler(sig, _):
        log.info(f'Signal {sig}, shutting down...')
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
    return phone.lstrip('+')


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


def truncate_header(value: str,
                    length: int = 40) -> str:
    """Truncate header value for safe logging."""
    if not value:
        return '<empty>'
    if len(value) <= length:
        return value
    return f'{value[:length]}...'


# ============================================
#  PROTOCOLS
# ============================================

@runtime_checkable
class HLRProvider(Protocol):
    async def lookup(
            self, session: aiohttp.ClientSession,
            phone: str) -> Optional[dict]: ...


@runtime_checkable
class CaptchaProvider(Protocol):
    async def solve(
            self, subtype: str,
            session: aiohttp.ClientSession,
            phone: str = '',
            **kw) -> Optional[dict]: ...
    async def check_balance(
            self,
            session: aiohttp.ClientSession
    ) -> int: ...


@runtime_checkable
class NumberProvider(Protocol):
    async def claim(
            self, session: aiohttp.ClientSession,
            count: int,
            lease_seconds: int
    ) -> Optional[dict]: ...
    async def report(
            self, session: aiohttp.ClientSession,
            claim_id: str,
            results: List[dict]
    ) -> Optional[dict]: ...


# ============================================
#  RATE LIMITER
# ============================================

class RateLimiter:
    def __init__(self, rate: float = 10.0,
                 burst: int = 20):
        self._rate = rate
        self._burst = burst
        self._tokens = float(burst)
        self._last_refill = time.monotonic()
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
                log.info(
                    f'Rate limiter -> '
                    f'{self._rate:.1f} req/s')


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
                    f'Proxy {self.host}:'
                    f'{self.port}'
                    f' blacklisted {duration}s')

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
                f'Proxy pool: '
                f'{len(self._entries)} loaded')

    @staticmethod
    def _parse(
            proxy: str
    ) -> Optional['ProxyManager._Entry']:
        clean = proxy.strip()
        for pfx in (
                'http://', 'https://',
                'socks5://'):
            clean = clean.replace(pfx, '')
        host = port = user = password = ''
        parts = clean.split(':')
        if len(parts) == 4:
            host, port, user, password = parts
        elif '@' in clean:
            auth, server = clean.rsplit('@', 1)
            ap = auth.split(':', 1)
            sp = server.split(':')
            if len(sp) == 2 and len(ap) == 2:
                host, port = sp
                user, password = ap
        elif len(parts) == 2:
            host, port = parts
        else:
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
            best.blacklisted_until = 0
            return self._build_url(
                best, country_code)

    @staticmethod
    def _build_url(
            entry: '_Entry',
            country_code: Optional[str]
    ) -> str:
        password = entry.password
        if country_code:
            if 'COUNTRY_CODE' in password:
                password = password.replace(
                    'COUNTRY_CODE', country_code)
            elif 'country-' not in password:
                password = (
                    f'{password}_country-'
                    f'{country_code}'
                    f'_streaming-1')
        if entry.user:
            return (
                f'http://{entry.user}:{password}'
                f'@{entry.host}:{entry.port}')
        return (
            f'http://{entry.host}:{entry.port}')

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

@dataclass(frozen=True)
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
    delay_min: float = 0.5
    delay_max: float = 2.0
    device_pool_path: str = 'device_pool.json'
    device_pool_size: int = 50
    global_rps: float = 10.0
    global_burst: int = 20

    # Default APK version name — must exist in
    # APK_VERSIONS registry. Override via
    # config.json "default_version" or
    # --version CLI flag.
    default_version: str = '43.9.2'

    # Proactive rotation thresholds
    # (overridable via config.json)
    ms_token_max_uses: int = MS_TOKEN_MAX_USES
    device_max_uses: int = (
        DEVICE_MAX_USES_PER_SESSION)

    # Enable verbose logging for registration
    # and auth header diagnostics
    debug_registration: bool = False

    # Device hardware profiles
    # Format: (brand, model, os_api, os_version,
    #          dpi, resolution)
    #
    # Devices with os_api >= target_sdk of the
    # chosen APK version are preferred. All
    # devices must have os_api >= APK_MIN_SDK
    # (23).
    #
    # Android 15 / API 35 devices are listed
    # first for compatibility with 43.9.2
    # (target_sdk=35).
    devices: Tuple[
        Tuple[str, str, str, str, str, str],
        ...] = (
        # Android 15 (API 35) — best for 43.9.2
        ('Google', 'Pixel 9', '35', '15',
         '420', '1080*2424'),
        ('Google', 'Pixel 9 Pro', '35', '15',
         '512', '1280*2856'),
        ('Google', 'Pixel 9 Pro XL', '35', '15',
         '512', '1344*2992'),
        ('Samsung', 'SM-S928B', '35', '15',
         '480', '1440*3120'),
        ('Samsung', 'SM-S926B', '35', '15',
         '480', '1440*3120'),
        # Android 14 (API 34)
        ('Google', 'Pixel 8', '34', '14',
         '420', '1080*2400'),
        ('Google', 'Pixel 8 Pro', '34', '14',
         '512', '1344*2992'),
        ('Google', 'Pixel 7 Pro', '34', '14',
         '512', '1440*3120'),
        ('Samsung', 'SM-S918B', '34', '14',
         '480', '1440*3088'),
        ('Samsung', 'SM-A546B', '34', '14',
         '400', '1080*2340'),
        ('Xiaomi', '2304FPN6DC', '34', '14',
         '440', '1080*2400'),
        ('OnePlus', 'CPH2449', '34', '14',
         '480', '1240*2772'),
        # Android 13 (API 33)
        ('Google', 'Pixel 7', '33', '13',
         '420', '1080*2400'),
        ('Samsung', 'SM-G998B', '33', '13',
         '480', '1440*3200'),
        ('Xiaomi', 'MI 13', '33', '13',
         '440', '1080*2400'),
        ('OnePlus', 'NE2215', '33', '13',
         '420', '1080*2400'),
    )

    mcc_mnc: Tuple[
        Tuple[str, Tuple[str, ...]], ...] = (
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
        'api16-normal-c-useast2a.tiktokv.com',
        'api22-normal-c-useast1a.tiktokv.com',
        'api19-normal-c-useast1a.tiktokv.com',
        'api16-normal-c-useast1a.tiktokv.com',
    )

    def __post_init__(self):
        cache = {
            code: mncs
            for code, mncs in self.mcc_mnc}
        object.__setattr__(
            self, '_mcc_cache', cache)

    def validate(self, mode: str = 'csv') -> None:
        missing = []
        if mode in ('csv', 'api'):
            if not self.sadcaptcha_key:
                missing.append(
                    'sadcaptcha_key /'
                    ' SADCAPTCHA_KEY')
            if not self.hlr_api_key:
                missing.append(
                    'hlr_api_key / HLR_API_KEY')
        if mode == 'api':
            if not self.number_api_base:
                missing.append(
                    'number_api_base /'
                    ' NUMBER_API_BASE')
            if not self.number_api_key:
                missing.append(
                    'number_api_key /'
                    ' NUMBER_API_KEY')
        if mode == 'prewarm':
            if not self.sadcaptcha_key:
                missing.append(
                    'sadcaptcha_key /'
                    ' SADCAPTCHA_KEY')
        if missing:
            raise ConfigError(
                f'Missing: {", ".join(missing)}.'
                f' Set in config.json or'
                f' env vars.')

        # Validate default_version exists in
        # registry
        if (self.default_version
                not in _APK_VERSION_MAP):
            raise ConfigError(
                f'default_version'
                f' "{self.default_version}"'
                f' not in APK_VERSIONS.'
                f' Available:'
                f' {list(_APK_VERSION_MAP.keys())}'
            )

    def get_mcc_mnc(
            self, region: str
    ) -> Tuple[str, ...]:
        cache: Dict = object.__getattribute__(
            self, '_mcc_cache')
        return cache.get(
            region,
            cache.get('US', ('310260',)))

    def random_device_hw(
            self,
            apk_ver: Optional[
                APKVersion] = None
    ) -> Tuple[str, ...]:
        """Select a random hardware profile.

        If apk_ver is provided, prefer devices
        whose os_api >= apk_ver.target_sdk.
        Falls back to any device if no
        compatible ones exist.
        All devices have os_api >= APK_MIN_SDK
        (23) by construction.
        """
        if apk_ver is not None:
            target = apk_ver.target_sdk
            compatible = [
                d for d in self.devices
                if int(d[2]) >= target]
            if compatible:
                return random.choice(
                    compatible)
        return random.choice(self.devices)

    def get_default_apk_version(
            self) -> APKVersion:
        return get_apk_version(
            self.default_version)

    def random_host(self) -> str:
        return random.choice(self.api_hosts)

    def with_overrides(
            self, **kwargs) -> 'AppConfig':
        return replace(self, **kwargs)


def load_config(
        path: str = 'config.json') -> AppConfig:
    overrides: Dict[str, Any] = {}
    valid_keys = {
        f.name for f in fields(AppConfig)
        if f.name not in (
            'devices', 'mcc_mnc', 'api_hosts')}

    if os.path.exists(path):
        try:
            with open(path, 'r') as f:
                raw = json.load(f)
            for key, val in raw.items():
                if key in valid_keys:
                    overrides[key] = val
            log.info(f'Config: {path}')
        except (json.JSONDecodeError,
                IOError) as exc:
            log.warning(
                f'Config error ({path}): {exc}')

    env_map = {
        'SADCAPTCHA_KEY': (
            'sadcaptcha_key', str),
        'HLR_API_KEY': (
            'hlr_api_key', str),
        'HLR_API_URL': (
            'hlr_api_url', str),
        'NUMBER_API_BASE': (
            'number_api_base', str),
        'NUMBER_API_KEY': (
            'number_api_key', str),
        'DEVICE_POOL_PATH': (
            'device_pool_path', str),
    }
    for env_key, (conf_key, conv) in (
            env_map.items()):
        val = os.environ.get(env_key)
        if val:
            try:
                overrides[conf_key] = conv(val)
            except (ValueError, TypeError):
                pass

    return AppConfig(**overrides)


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
        url = f'{self.base_url}{endpoint}'
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
                        try:
                            return (
                                await resp.json())
                        except (
                            json.JSONDecodeError,
                            aiohttp
                            .ContentTypeError
                        ) as exc:
                            raise ParseError(
                                f'NumberAPI:'
                                f' {exc}')
                    if resp.status in (
                            400, 401, 409):
                        text = await resp.text()
                        log.error(
                            f'NumberAPI'
                            f' {resp.status}:'
                            f' {text[:200]}')
                        return None
                    if resp.status in (
                            RETRYABLE_HTTP_CODES):
                        await asyncio.sleep(
                            jitter_delay(attempt))
                        continue
                    text = await resp.text()
                    log.error(
                        f'NumberAPI'
                        f' {resp.status}:'
                        f' {text[:200]}')
                    return None
            except (
                asyncio.TimeoutError,
                aiohttp.ServerTimeoutError
            ):
                await asyncio.sleep(
                    jitter_delay(attempt, 0.5))
            except aiohttp.ClientError as exc:
                raise NetworkError(
                    f'NumberAPI:'
                    f' {type(exc).__name__}:'
                    f' {exc}')
            except (ShutdownError, ParseError):
                raise
            except Exception as exc:
                raise AppError(
                    f'NumberAPI:'
                    f' {type(exc).__name__}:'
                    f' {exc}')
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
            log.info(
                f'Claimed'
                f' {len(data.get("items", []))}'
                f' (claim='
                f'{data.get("claimId", "?")})')
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
                f'Report: updated='
                f'{data.get("updated", 0)}')
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
            phone: str) -> Optional[dict]:
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
                        try:
                            data = (
                                await resp.json())
                        except (
                            json.JSONDecodeError,
                            aiohttp
                            .ContentTypeError
                        ) as exc:
                            raise ParseError(
                                f'HLR {masked}:'
                                f' {exc}')
                        if data.get('success'):
                            info = (
                                data.get('data')
                                or {})
                            return {
                                'country_code':
                                    info.get(
                                        'country_'
                                        'code',
                                        'US'),
                                'country_prefix':
                                    strip_plus(
                                        info.get(
                                            'country'
                                            '_prefix'
                                            , '')),
                                'national_number':
                                    info.get(
                                        'national'
                                        '_number',
                                        phone_clean
                                    ),
                                'country_name':
                                    info.get(
                                        'country_'
                                        'name',
                                        ''),
                                'carrier':
                                    info.get(
                                        'carrier',
                                        ''),
                            }
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
                    f'HLR {masked}:'
                    f' {type(exc).__name__}:'
                    f' {exc}')
            except (ShutdownError, ParseError):
                raise
            except Exception as exc:
                raise AppError(
                    f'HLR {masked}:'
                    f' {type(exc).__name__}:'
                    f' {exc}')
        return None


# ============================================
#  DEVICE
# ============================================

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

    @classmethod
    def generate(
            cls, config: AppConfig,
            region: str = 'US') -> 'Device':
        ver = config.get_default_apk_version()
        hw = config.random_device_hw(
            apk_ver=ver)
        brand, model, os_api = hw[0], hw[1], hw[2]
        os_ver, dpi, res = hw[3], hw[4], hw[5]

        # Validate os_api >= APK_MIN_SDK
        hw_api = int(os_api)
        if hw_api < APK_MIN_SDK:
            log.warning(
                f'Device {model} os_api='
                f'{os_api} < min_sdk='
                f'{APK_MIN_SDK},'
                f' may cause issues')

        return cls(
            device_id=str(random.randint(
                DEVICE_ID_MIN, DEVICE_ID_MAX)),
            install_id=str(random.randint(
                DEVICE_ID_MIN, DEVICE_ID_MAX)),
            openudid=hashlib.md5(
                f'{random.random()}'
                f'{time.time()}'
                .encode()).hexdigest()[:16],
            cdid=(
                f'{random.randint(10000000, 99999999):08x}'
                f'-'
                f'{random.randint(1000, 9999):04x}'
                f'-'
                f'{random.randint(1000, 9999):04x}'
                f'-'
                f'{random.randint(1000, 9999):04x}'
                f'-'
                f'{random.randint(100000000000, 999999999999):012x}'
            ),
            device_type=model,
            device_brand=brand,
            os_version=os_ver, os_api=os_api,
            dpi=dpi, resolution=res,
            version_name=ver.version_name,
            version_code=ver.version_code,
            manifest_version_code=(
                ver.manifest_version_code),
            region=region,
            mcc_mnc=random.choice(
                config.get_mcc_mnc(region)),
        )

    def to_dict(self) -> dict:
        return {
            f.name: getattr(self, f.name)
            for f in fields(self)}

    @classmethod
    def from_dict(
            cls, data: dict) -> 'Device':
        valid_names = {
            f.name for f in fields(cls)}
        return cls(**{
            k: v for k, v in data.items()
            if k in valid_names})

    @property
    def apk_version(self) -> APKVersion:
        """Resolve APKVersion from this device's
        version_name. All version-dependent
        parameters (sig_hash, signer params,
        passport-sdk-version, tt-ok version)
        are derived from the returned object.
        """
        return get_apk_version(
            self.version_name)

    @property
    def ms_token_valid(self) -> bool:
        """Check both TTL and use-count.

        See ms_token lifecycle docs in constants
        section for rationale on dual-check.
        """
        if not self.ms_token:
            return False
        age_ok = (
            (time.time() - self.ms_token_time)
            < MS_TOKEN_TTL_SECONDS)
        uses_ok = (
            self.ms_token_uses
            < MS_TOKEN_MAX_USES)
        return age_ok and uses_ok

    def invalidate_ms_token(self) -> None:
        self.ms_token = ''
        self.ms_token_time = 0.0
        self.ms_token_uses = 0

    def set_ms_token(self, token: str) -> None:
        self.ms_token = token
        self.ms_token_time = time.time()
        self.ms_token_uses = 0

    def record_ms_token_use(self) -> None:
        """Increment ms_token use counter.
        Called once per API request in _request().
        """
        self.ms_token_uses += 1

    def record_session_use(self) -> None:
        """Increment per-session device counter.
        Called once per send_code attempt.
        """
        self.session_uses += 1

    def needs_rotation(
            self, max_uses: int) -> bool:
        """Check if device needs proactive
        rotation based on session use count."""
        return self.session_uses >= max_uses

    @property
    def manifest_int(self) -> int:
        return self.apk_version.manifest_int

    @property
    def user_agent(self) -> str:
        ver = self.apk_version
        return (
            f'com.zhiliaoapp.musically'
            f'/{ver.manifest_version_code}'
            f' (Linux; U; Android'
            f' {self.os_version}; en;'
            f' {self.device_type};'
            f' Build/{DEVICE_ROM_BUILD};'
            f'tt-ok/{ver.tt_ok_version})')

    def base_params(self) -> Dict[str, str]:
        ver = self.apk_version
        now_ms = str(int(time.time() * 1000))
        now_s = str(int(time.time()))
        params: Dict[str, str] = {
            'passport-sdk-version':
                ver.passport_sdk_version,
            'iid': self.install_id,
            'device_id': self.device_id,
            'ac': 'wifi',
            'channel': APP_CHANNEL,
            'aid': APP_AID,
            'app_name': 'musical_ly',
            'version_code': self.version_code,
            'version_name': self.version_name,
            'device_platform': 'android',
            'os': 'android',
            'ab_version': self.version_name,
            'ssmix': 'a',
            'device_type': self.device_type,
            'device_brand': self.device_brand,
            'language': 'en',
            'os_api': self.os_api,
            'os_version': self.os_version,
            'openudid': self.openudid,
            'manifest_version_code':
                self.manifest_version_code,
            'resolution': self.resolution,
            'dpi': self.dpi,
            'update_version_code':
                self.manifest_version_code,
            '_rticket': now_ms,
            'is_pad': '0',
            'current_region': self.region,
            'app_type': 'normal',
            'sys_region': self.region,
            'mcc_mnc': self.mcc_mnc,
            'timezone_name':
                'America/New_York',
            'residence': self.region,
            'app_language': 'en',
            'carrier_region': self.region,
            'ac2': 'wifi',
            'uoo': '0',
            'op_region': self.region,
            'timezone_offset': '-14400',
            'build_number': self.version_name,
            'host_abi': DEVICE_CPU_ABI,
            'locale': 'en',
            'region': self.region,
            'ts': now_s,
            'cdid': self.cdid,
        }
        if self.ms_token_valid:
            params['msToken'] = self.ms_token
        return params

    def registration_payload(self) -> dict:
        ver = self.apk_version
        return {
            'magic_tag': 'ss_app_log',
            'header': {
                'display_name':
                    APP_DISPLAY_NAME,
                'update_version_code':
                    ver.manifest_int,
                'manifest_version_code':
                    ver.manifest_int,
                'aid': int(APP_AID),
                'channel': APP_CHANNEL,
                'package': APP_PACKAGE,
                'app_version':
                    ver.version_name,
                'version_code':
                    ver.version_code_int,
                'sdk_version':
                    APP_SDK_VERSION,
                'os': 'Android',
                'os_version': self.os_version,
                'os_api': self.os_api,
                'device_model':
                    self.device_type,
                'device_brand':
                    self.device_brand,
                'device_manufacturer':
                    self.device_brand,
                'cpu_abi': DEVICE_CPU_ABI,
                'release_build': '1',
                'density_dpi': int(self.dpi),
                'display_density': 'xhdpi',
                'resolution': self.resolution,
                'language': 'en',
                'timezone': -5,
                'access': 'wifi',
                'not_request_sender': 0,
                'rom': DEVICE_ROM_BUILD,
                'rom_version':
                    self.os_version,
                'openudid': self.openudid,
                'cdid': self.cdid,
                'sig_hash': ver.sig_hash,
                'region': self.region,
                'app_language': 'en',
                'locale': 'en',
                'sys_region': self.region,
                'carrier_region': self.region,
                'mcc_mnc': self.mcc_mnc,
            },
            '_gen_time': int(time.time()),
        }

    def validate_payload(self) -> List[str]:
        """Validate device fields before
        registration. Returns list of issues
        (empty = valid)."""
        issues: List[str] = []
        ver = self.apk_version

        if not self.device_id:
            issues.append(
                'device_id is empty')
        if not self.install_id:
            issues.append(
                'install_id is empty')
        if not self.openudid:
            issues.append(
                'openudid is empty')
        if not self.cdid:
            issues.append(
                'cdid is empty')
        if not self.device_type:
            issues.append(
                'device_type is empty')
        if not self.device_brand:
            issues.append(
                'device_brand is empty')
        if not self.os_version:
            issues.append(
                'os_version is empty')
        if not self.os_api:
            issues.append(
                'os_api is empty')
        if not self.dpi:
            issues.append(
                'dpi is empty')
        if not self.resolution:
            issues.append(
                'resolution is empty')
        if not self.version_name:
            issues.append(
                'version_name is empty')

        # Type checks for payload fields
        try:
            int(self.dpi)
        except (ValueError, TypeError):
            issues.append(
                f'dpi "{self.dpi}"'
                f' not numeric')

        # Verify os_api >= APK_MIN_SDK
        try:
            hw_api = int(self.os_api)
            if hw_api < APK_MIN_SDK:
                issues.append(
                    f'os_api {hw_api}'
                    f' < min_sdk'
                    f' {APK_MIN_SDK}')
        except (ValueError, TypeError):
            issues.append(
                f'os_api "{self.os_api}"'
                f' not numeric')

        # Verify version consistency
        if (self.version_name
                != ver.version_name):
            issues.append(
                f'version_name mismatch:'
                f' device={self.version_name}'
                f' vs apk={ver.version_name}')
        if (self.version_code
                != ver.version_code):
            issues.append(
                f'version_code mismatch:'
                f' device={self.version_code}'
                f' vs apk={ver.version_code}')
        if (self.manifest_version_code
                != ver.manifest_version_code):
            issues.append(
                f'manifest mismatch:'
                f' device='
                f'{self.manifest_version_code}'
                f' vs apk='
                f'{ver.manifest_version_code}')

        # Warn if deprecated version
        if ver.stability == 'deprecated':
            issues.append(
                f'version {ver.version_name}'
                f' is deprecated — consider'
                f' upgrading to'
                f' {DEFAULT_APK_VERSION.version_name}'
            )

        return issues


# ============================================
#  DEVICE POOL
# ============================================

def _validate_device_dict(data: Any) -> bool:
    if not isinstance(data, dict):
        return False
    return DEVICE_POOL_REQUIRED_KEYS.issubset(
        data.keys())


class DevicePool:

    def __init__(self, config: AppConfig):
        self.config = config
        self.path = config.device_pool_path
        self._pool: Dict[str, List[dict]] = {}
        self._lock = asyncio.Lock()
        self._dirty = False
        self._load_sync()

    def _load_sync(self) -> None:
        if not os.path.exists(self.path):
            log.info(
                f'No pool at {self.path}')
            return
        try:
            with open(self.path, 'r') as f:
                raw = json.load(f)
            if not isinstance(raw, dict):
                log.warning(
                    'Pool file root not dict')
                return
            total = 0
            skipped = 0
            for region, dl in raw.items():
                if not isinstance(dl, list):
                    continue
                valid = [
                    d for d in dl
                    if _validate_device_dict(d)]
                skipped += len(dl) - len(valid)
                if valid:
                    self._pool[region] = valid
                    total += len(valid)
            if skipped:
                log.warning(
                    f'Pool: skipped {skipped}'
                    f' invalid entries')
            log.info(
                f'Pool: {total} devices,'
                f' {len(self._pool)} regions')
        except (json.JSONDecodeError,
                IOError) as exc:
            log.warning(f'Pool load: {exc}')

    def _save_sync(self) -> None:
        try:
            tmp = f'{self.path}.tmp'
            with open(tmp, 'w') as f:
                json.dump(
                    self._pool, f, indent=2)
            if (sys.platform == 'win32'
                    and os.path.exists(
                        self.path)):
                os.remove(self.path)
            os.rename(tmp, self.path)
            self._dirty = False
        except IOError as exc:
            log.error(f'Pool save: {exc}')

    async def save(
            self, force: bool = False) -> None:
        async with self._lock:
            if self._dirty or force:
                await run_in_io(self._save_sync)

    async def get(
            self,
            region: str) -> Optional[Device]:
        async with self._lock:
            dd = self._pool.get(region, [])
            registered = [
                d for d in dd
                if d.get('registered')]
            if not registered:
                return None
            registered.sort(
                key=lambda d:
                d.get('last_used', 0))
            chosen = registered[0]
            chosen['last_used'] = time.time()
            chosen['use_count'] = (
                chosen.get('use_count', 0) + 1)
            self._dirty = True
            return Device.from_dict(
                dict(chosen))

    async def add(
            self, device: Device) -> None:
        async with self._lock:
            dd = device.to_dict()
            if not _validate_device_dict(dd):
                log.warning(
                    'Refusing invalid'
                    ' device dict')
                return
            region = device.region
            if region not in self._pool:
                self._pool[region] = []
            self._pool[region].append(dd)
            mx = self.config.device_pool_size
            if len(self._pool[region]) > mx:
                self._pool[region].sort(
                    key=lambda d:
                    d.get('use_count', 0),
                    reverse=True)
                self._pool[region] = (
                    self._pool[region][:mx])
            self._dirty = True

    async def update(
            self, device: Device) -> None:
        async with self._lock:
            region = device.region
            if region not in self._pool:
                return
            new_data = device.to_dict()
            if not _validate_device_dict(
                    new_data):
                return
            tid = device.device_id
            for idx, existing in enumerate(
                    self._pool[region]):
                if existing.get(
                        'device_id') == tid:
                    self._pool[region][idx] = (
                        new_data)
                    self._dirty = True
                    return

    async def remove(
            self, device: Device) -> None:
        async with self._lock:
            region = device.region
            if region in self._pool:
                tid = device.device_id
                self._pool[region] = [
                    d for d
                    in self._pool[region]
                    if d.get(
                        'device_id') != tid]
                self._dirty = True

    async def count(
            self,
            region: Optional[str] = None
    ) -> int:
        async with self._lock:
            if region:
                return len([
                    d for d in self._pool.get(
                        region, [])
                    if d.get('registered')])
            return sum(
                len([d for d in devs
                     if d.get('registered')])
                for devs
                in self._pool.values())


# ============================================
#  CAPTCHA
# ============================================

class CaptchaSolver:
    BASE_URL = (
        'https://www.sadcaptcha.com/api/v1')

    def __init__(self, config: AppConfig):
        self.api_key = config.sadcaptcha_key
        self._balance: int = -1

    async def check_balance(
            self,
            session: aiohttp.ClientSession
    ) -> int:
        try:
            async with session.get(
                f'{self.BASE_URL}'
                f'/license/credits',
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
                        f'Captcha balance:'
                        f' {self._balance}')
                    return self._balance
                return -1
        except Exception as exc:
            log.warning(
                f'Captcha balance: {exc}')
            return -1

    async def _call(
            self,
            session: aiohttp.ClientSession,
            endpoint: str, payload: dict,
            timeout: float,
            phone: str = ''
    ) -> Optional[dict]:
        masked = mask_phone(phone)
        for attempt in range(3):
            try:
                async with session.post(
                    f'{self.BASE_URL}{endpoint}',
                    params={
                        'licenseKey':
                            self.api_key},
                    json=payload,
                    timeout=(
                        aiohttp.ClientTimeout(
                            total=timeout))
                ) as resp:
                    if resp.status == 200:
                        try:
                            result = (
                                await resp.json())
                            log.info(
                                f'[{masked}]'
                                f' Solved'
                                f' ({endpoint})')
                            return result
                        except (
                            json.JSONDecodeError,
                            aiohttp
                            .ContentTypeError
                        ) as exc:
                            raise ParseError(
                                f'Captcha:'
                                f' {exc}')
                    if resp.status in (
                            RETRYABLE_HTTP_CODES):
                        await asyncio.sleep(
                            jitter_delay(attempt))
                        continue
                    text = await resp.text()
                    raise CaptchaError(
                        f'{resp.status}:'
                        f' {text[:150]}')
            except (
                asyncio.TimeoutError,
                aiohttp.ServerTimeoutError
            ):
                await asyncio.sleep(
                    jitter_delay(attempt, 0.5))
            except aiohttp.ClientError as exc:
                raise NetworkError(
                    f'Captcha:'
                    f' {type(exc).__name__}:'
                    f' {exc}')
            except (
                ShutdownError, ParseError,
                CaptchaError
            ):
                raise
            except Exception as exc:
                raise CaptchaError(
                    f'{type(exc).__name__}:'
                    f' {exc}')
        raise CaptchaError('Max retries')

    async def solve(
            self, subtype: str,
            session: aiohttp.ClientSession,
            phone: str = '',
            **kwargs) -> Optional[dict]:
        if self._balance == 0:
            raise CaptchaError('Balance 0')
        ep_map = {
            '3d': '/shapes',
            'shapes': '/shapes',
            'slide': '/puzzle',
            'puzzle': '/puzzle',
            'rotate': '/rotate',
            'icon': '/icon',
        }
        endpoint = ep_map.get(subtype)
        if not endpoint:
            raise CaptchaError(
                f'Unknown subtype: {subtype}')
        pl_map = {
            '/shapes': {
                'imageB64': kwargs.get(
                    'image_b64', '')},
            '/puzzle': {
                'puzzleImageB64': kwargs.get(
                    'puzzle_b64', ''),
                'pieceImageB64': kwargs.get(
                    'piece_b64', '')},
            '/rotate': {
                'outerImageB64': kwargs.get(
                    'outer_b64', ''),
                'innerImageB64': kwargs.get(
                    'inner_b64', '')},
            '/icon': {
                'challenge': kwargs.get(
                    'challenge', ''),
                'imageB64': kwargs.get(
                    'image_b64', '')},
        }
        timeout = CAPTCHA_TIMEOUTS.get(
            subtype, CAPTCHA_TIMEOUT_DEFAULT)
        return await self._call(
            session, endpoint,
            pl_map[endpoint],
            timeout, phone)


# ============================================
#  TIKTOK SMS ENGINE
# ============================================

class TikTokSMS:
    """SMS sending engine.

    Uses tiktok-signer for all crypto.
    Isolated cookies per instance,
    shared connector for pooling.

    Note on sdk-version header:
    tiktok-signer's generate_headers() produces
    all required auth headers including
    x-ss-req-ticket, x-tt-trace-id, x-ss-stub,
    x-ladon, x-gorgon, x-khronos, x-argus.
    The legacy 'sdk-version: 2' header was used
    by older signing libraries (SignerPy) as a
    flag for their internal routing. tiktok-signer
    does not require or produce it — the signing
    algorithm version is determined internally
    from version_name/version_code parameters.
    TikTok's server does NOT check for this header.
    """

    def __init__(
            self, config: AppConfig,
            connector: aiohttp.TCPConnector,
            proxy_mgr: ProxyManager,
            captcha: CaptchaProvider,
            hlr: HLRProvider,
            pool: DevicePool,
            limiter: RateLimiter):
        self.config = config
        self._connector = connector
        self.proxy = proxy_mgr
        self.captcha = captcha
        self.hlr = hlr
        self.pool = pool
        self.limiter = limiter
        self.api_host = config.random_host()
        self.device: Optional[Device] = None
        self._cookie_jar = aiohttp.CookieJar(
            unsafe=True)
        self._session: Optional[
            aiohttp.ClientSession] = None

    async def _get_session(
            self) -> aiohttp.ClientSession:
        if (self._session is None
                or self._session.closed):
            self._session = (
                aiohttp.ClientSession(
                    connector=self._connector,
                    connector_owner=False,
                    cookie_jar=(
                        self._cookie_jar)))
        return self._session

    async def close(self) -> None:
        if (self._session
                and not self._session.closed):
            await self._session.close()
            self._session = None

    def _generate_auth_headers(
            self, params_str: str,
            body: Any = None
    ) -> Dict[str, str]:
        """Generate auth headers.

        All signer parameters (sdk_ver,
        sdk_ver_code, lc_id, version_name,
        version_code) are derived from the
        device's APKVersion to ensure
        consistency.

        device_id passed here MUST match the
        device_id used in device_register —
        X-Argus includes device_id in its
        signature and TikTok verifies the match
        server-side (mismatch = 1109).
        """
        ver = self.device.apk_version
        cookie_str = ''
        if self.device.ms_token_valid:
            cookie_str = (
                f'msToken='
                f'{self.device.ms_token}')

        auth = TikTokSigner.generate_headers(
            params=params_str,
            data=body,
            device_id=(
                self.device.device_id),
            aid=int(APP_AID),
            lc_id=ver.signer_lc_id,
            sdk_ver=ver.signer_sdk_ver,
            sdk_ver_code=(
                ver.signer_sdk_ver_code),
            version_name=ver.version_name,
            version_code=ver.manifest_int,
            cookie=(
                cookie_str or None),
            unix=int(time.time()),
        )

        # Validate X-Gorgon prefix
        gorgon = auth.get('x-gorgon', '')
        if gorgon:
            if not gorgon.startswith(
                    ver.gorgon_prefix):
                level = (
                    log.error
                    if self.config
                    .debug_registration
                    else log.warning)
                level(
                    f'X-Gorgon prefix'
                    f' mismatch:'
                    f' expected'
                    f' {ver.gorgon_prefix},'
                    f' got {gorgon[:4]}.'
                    f' Signer may not match'
                    f' APK'
                    f' {ver.version_name}.'
                    f' Try: pip install'
                    f' --upgrade'
                    f' tiktok-signer')

        headers = {
            'User-Agent':
                self.device.user_agent,
            'Accept-Encoding': 'gzip',
            'Connection': 'Keep-Alive',
        }
        if self.device.ms_token_valid:
            headers[MS_TOKEN_HEADER] = (
                self.device.ms_token)

        headers.update(auth)

        if self.config.debug_registration:
            self._log_auth_headers(
                auth, params_str, body)

        return headers

    @staticmethod
    def _log_auth_headers(
            auth: Dict[str, str],
            params_str: str,
            body: Any) -> None:
        """Log auth header details for
        debugging registration issues."""
        log.debug(
            f'Auth headers generated'
            f' ({len(auth)} keys):')
        for key in sorted(auth.keys()):
            val = auth[key]
            log.debug(
                f'  {key}:'
                f' {truncate_header(val)}')
        body_desc = '<none>'
        if body is not None:
            if isinstance(body, bytes):
                body_desc = (
                    f'<bytes len={len(body)}>')
            elif isinstance(body, str):
                body_desc = (
                    f'<str len={len(body)}>')
            elif isinstance(body, dict):
                body_desc = (
                    f'<dict keys='
                    f'{list(body.keys())}>')
        log.debug(
            f'  params_len='
            f'{len(params_str)},'
            f' body={body_desc}')

    async def _request(
            self, method: str, url: str,
            params_dict: Dict[str, str],
            body: Any = None,
            content_type: Optional[str] = None,
            proxy_url: Optional[str] = None,
            phone: str = '',
            parse_json: bool = True
    ) -> Optional[Any]:
        masked = mask_phone(phone)
        await self.limiter.acquire()
        check_shutdown()

        session = await self._get_session()
        params_str = urlencode(params_dict)
        headers = self._generate_auth_headers(
            params_str, body)

        if content_type:
            headers['Content-Type'] = (
                content_type)
        elif body is not None:
            if isinstance(body, str):
                headers['Content-Type'] = (
                    'application/'
                    'x-www-form-urlencoded;'
                    ' charset=UTF-8')
            elif isinstance(body, bytes):
                headers['Content-Type'] = (
                    'application/octet-stream')

        full_url = f'{url}?{params_str}'

        # Track ms_token usage per request
        if (self.device
                and self.device.ms_token_valid):
            self.device.record_ms_token_use()

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
                if (method == 'POST'
                        and body is not None):
                    kw['data'] = body

                fn = (
                    session.post
                    if method == 'POST'
                    else session.get)

                async with fn(
                        full_url, **kw) as resp:
                    self._extract_ms_token(resp)

                    if resp.status in (
                            RETRYABLE_HTTP_CODES):
                        wait = jitter_delay(
                            attempt)
                        log.warning(
                            f'[{masked}]'
                            f' HTTP'
                            f' {resp.status}'
                            f' (attempt'
                            f' {attempt + 1}),'
                            f' retry'
                            f' {wait:.1f}s')
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

                    if parse_json:
                        try:
                            return (
                                await resp.json(
                                    content_type=(
                                        None)))
                        except (
                            json.JSONDecodeError,
                            aiohttp
                            .ContentTypeError
                        ) as exc:
                            text = (
                                await resp.text())
                            raise ParseError(
                                f'JSON: {exc},'
                                f' {text[:200]}')
                    else:
                        return (
                            await resp.read())

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
                    self.device.region
                    if self.device else None)
                if new and new != proxy_url:
                    proxy_url = new
                await asyncio.sleep(
                    jitter_delay(attempt, 0.5))

            except aiohttp.ClientError as exc:
                await (
                    self.proxy.report_failure(
                        proxy_url))
                raise NetworkError(
                    f'{type(exc).__name__}:'
                    f' {exc}')

            except (ShutdownError, ParseError):
                raise

            except Exception as exc:
                raise AppError(
                    f'{type(exc).__name__}:'
                    f' {exc}')

        raise NetworkError(
            'Max retries exhausted',
            retryable=False)

    def _extract_ms_token(
            self,
            resp: aiohttp.ClientResponse
    ) -> None:
        for cookie in resp.cookies.values():
            if cookie.key == (
                    MS_TOKEN_COOKIE_NAME):
                self.device.set_ms_token(
                    cookie.value)
                return
        hv = resp.headers.get(
            MS_TOKEN_HEADER, '')
        if hv:
            self.device.set_ms_token(hv)

    # ---- ms_token ----

    async def _ensure_ms_token(
            self,
            proxy_url: Optional[str] = None,
            phone: str = '') -> bool:
        """Acquire fresh ms_token if missing,
        expired (TTL), or use-count exceeded.
        """
        if self.device.ms_token_valid:
            return True

        masked = mask_phone(phone)
        if self.device.ms_token_uses >= (
                self.config.ms_token_max_uses):
            log.info(
                f'[{masked}] ms_token'
                f' used'
                f' {self.device.ms_token_uses}x,'
                f' rotating')

        self.device.invalidate_ms_token()
        for endpoint in (
            f'https://{self.api_host}'
            f'/passport/user/info/',
            f'https://{self.api_host}'
            f'/passport/app/'
            f'region_setting/',
        ):
            try:
                await self._request(
                    'GET', endpoint,
                    self.device.base_params(),
                    proxy_url=proxy_url,
                    phone=phone)
            except (NetworkError, ParseError):
                pass
            if self.device.ms_token_valid:
                return True
        return False

    # ---- Device registration ----

    async def _register_device(
            self,
            proxy_url: Optional[str] = None,
            phone: str = '') -> bool:
        masked = mask_phone(phone)

        # Validate payload before sending
        issues = (
            self.device.validate_payload())
        if issues:
            for issue in issues:
                log.error(
                    f'[{masked}] Payload'
                    f' validation: {issue}')
            # Filter out deprecation warnings
            # — they are non-fatal
            fatal = [
                i for i in issues
                if 'deprecated' not in i]
            if fatal:
                raise DeviceError(
                    f'Payload validation'
                    f' failed:'
                    f' {len(fatal)} issues')

        payload = (
            self.device
            .registration_payload())

        if self.config.debug_registration:
            self._log_registration_payload(
                masked, payload)

        # TikTokSigner.encrypt() accepts dict,
        # str, or bytes. Dict is serialized to
        # JSON internally then encrypted.
        encrypted = TikTokSigner.encrypt(payload)

        if self.config.debug_registration:
            log.info(
                f'[{masked}] Encrypted'
                f' payload:'
                f' {len(encrypted)} bytes')

        try:
            raw = await self._request(
                'POST', URL_DEVICE_REGISTER,
                self.device.base_params(),
                encrypted,
                content_type=(
                    'application/'
                    'octet-stream;'
                    'tt-data=a'),
                proxy_url=proxy_url,
                phone=phone,
                parse_json=False)
        except (NetworkError, AppError) as exc:
            log.error(
                f'[{masked}]'
                f' Register: {exc}')
            return False

        if not raw:
            return False

        data = None
        decode_method = 'unknown'
        try:
            data = json.loads(raw)
            decode_method = 'plaintext_json'
        except (json.JSONDecodeError,
                ValueError):
            try:
                data = json.loads(
                    TikTokSigner.decrypt(raw))
                decode_method = (
                    'decrypted_json')
            except Exception as exc:
                raise ParseError(
                    f'Register decrypt:'
                    f' {exc}')

        if not isinstance(data, dict):
            raise ParseError(
                'Register response not dict')

        if self.config.debug_registration:
            self._log_registration_response(
                masked, data, decode_method)

        did = data.get('device_id', 0)
        if did and did != 0:
            self.device.device_id = str(did)
            self.device.install_id = str(
                data.get('install_id', 0))
            self.device.registered = True
            log.info(
                f'[{masked}] Registered:'
                f' {self.device.device_id}')
            return True

        # Registration failed — diagnose
        self._log_registration_failure(
            masked, data)
        return False

    @staticmethod
    def _log_registration_payload(
            masked: str,
            payload: dict) -> None:
        """Log registration payload for
        debugging."""
        header = payload.get('header', {})
        log.info(
            f'[{masked}] Registration'
            f' payload:')
        log.info(
            f'  aid={header.get("aid")}'
            f' (type='
            f'{type(header.get("aid")).__name__}'
            f')')
        log.info(
            f'  app_version='
            f'{header.get("app_version")}')
        log.info(
            f'  version_code='
            f'{header.get("version_code")}'
            f' (type='
            f'{type(header.get("version_code")).__name__}'
            f')')
        log.info(
            f'  manifest='
            f'{header.get("manifest_version_code")}'
            f' (type='
            f'{type(header.get("manifest_version_code")).__name__}'
            f')')
        log.info(
            f'  sig_hash='
            f'{header.get("sig_hash")}')
        log.info(
            f'  device_model='
            f'{header.get("device_model")}')
        log.info(
            f'  os_version='
            f'{header.get("os_version")}')
        log.info(
            f'  os_api='
            f'{header.get("os_api")}')
        log.info(
            f'  region='
            f'{header.get("region")}')

    @staticmethod
    def _log_registration_response(
            masked: str, data: dict,
            decode_method: str) -> None:
        """Log registration response for
        debugging."""
        log.info(
            f'[{masked}] Registration'
            f' response'
            f' (decode={decode_method}):')
        log.info(
            f'  device_id='
            f'{data.get("device_id", "?")}')
        log.info(
            f'  install_id='
            f'{data.get("install_id", "?")}')
        # Log any error fields
        for key in (
                'error_code', 'message',
                'status_code', 'error'):
            if key in data:
                log.info(
                    f'  {key}='
                    f'{data[key]}')

    @staticmethod
    def _log_registration_failure(
            masked: str,
            data: dict) -> None:
        """Log diagnostic info when device_id=0.

        Common causes and their indicators:
        - sig_hash outdated: error about
          signature verification
        - APK version unsupported: error about
          update required
        - X-Argus mismatch: error 1105/1109
        - Proxy blocked: error about region or
          IP restriction
        - Missing params: error about required
          fields
        - tt-ok version mismatch: error about
          client version
        """
        ec = data.get(
            'error_code',
            data.get('status_code', '?'))
        msg = data.get(
            'message',
            data.get('error', '?'))
        log.error(
            f'[{masked}] Registration'
            f' failed (device_id=0):'
            f' error_code={ec},'
            f' message={str(msg)[:200]}')

        # Provide hints based on error
        msg_lower = str(msg).lower()
        ec_str = str(ec)
        if 'signature' in msg_lower:
            log.error(
                f'[{masked}] HINT:'
                f' sig_hash may be'
                f' outdated or APK'
                f' signing key changed')
        if 'update' in msg_lower:
            log.error(
                f'[{masked}] HINT:'
                f' APK version may be'
                f' too old — try'
                f' --version 43.9.2')
        if ('1105' in ec_str
                or '1109' in ec_str):
            log.error(
                f'[{masked}] HINT:'
                f' X-Argus/X-Gorgon'
                f' mismatch — signer'
                f' may not match APK'
                f' version. Try:'
                f' pip install --upgrade'
                f' tiktok-signer')
        if 'region' in msg_lower:
            log.error(
                f'[{masked}] HINT:'
                f' Proxy may be blocked'
                f' or wrong region')

    # ---- Captcha helpers ----

    async def _fetch_image_b64(
            self, url: str,
            phone: str = '') -> str:
        if not url:
            return ''
        session = await self._get_session()
        try:
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

    async def _extract_captcha_kwargs(
            self, subtype: str,
            question: dict,
            phone: str = ''
    ) -> Dict[str, str]:
        if not question:
            return {}
        kwargs: Dict[str, str] = {}
        url1 = (
            question.get('url1', '')
            or question.get('url', ''))
        url2 = question.get('url2', '')

        if subtype in ('3d', 'shapes'):
            if url1:
                img = (
                    await self._fetch_image_b64(
                        url1, phone))
                if img:
                    kwargs['image_b64'] = img
        elif subtype in ('slide', 'puzzle'):
            if url1 and url2:
                p, pc = await asyncio.gather(
                    self._fetch_image_b64(
                        url1, phone),
                    self._fetch_image_b64(
                        url2, phone))
                if p and pc:
                    kwargs['puzzle_b64'] = p
                    kwargs['piece_b64'] = pc
        elif subtype == 'rotate':
            if url1 and url2:
                o, i = await asyncio.gather(
                    self._fetch_image_b64(
                        url1, phone),
                    self._fetch_image_b64(
                        url2, phone))
                if o and i:
                    kwargs['outer_b64'] = o
                    kwargs['inner_b64'] = i
        elif subtype == 'icon':
            if url1:
                img = (
                    await self._fetch_image_b64(
                        url1, phone))
                if img:
                    kwargs['image_b64'] = img
                    kwargs['challenge'] = (
                        question.get(
                            'tip_text', ''))
        return kwargs

    async def _solve_captcha_flow(
            self, subtype: str,
            detail: str,
            region: str,
            verify_event: str,
            scene: str = 'device_activate',
            proxy_url: Optional[str] = None,
            phone: str = '') -> bool:
        masked = mask_phone(phone)
        challenge = await self._request(
            'GET', URL_CAPTCHA_GET, {
                'aid': APP_AID,
                'host': self.api_host,
                'scene': scene,
                'device_id': (
                    self.device.device_id),
                'install_id': (
                    self.device.install_id),
                'region': (
                    region or 'useast2b'),
                'subtype': subtype,
                'detail': detail,
                'lang': 'en',
                'os': 'android',
            },
            proxy_url=proxy_url,
            phone=phone)

        if (not challenge
                or not isinstance(
                    challenge, dict)):
            raise CaptchaError(
                'Challenge failed')

        cd = challenge.get('data', challenge)
        if not isinstance(cd, dict):
            raise CaptchaError(
                'Challenge data invalid')

        question = cd.get('question')
        if (not question
                or not isinstance(
                    question, dict)):
            log.info(
                f'[{masked}] No captcha'
                f' — auto-passed')
            return True

        rs = (
            cd.get('subtype', subtype)
            or subtype)
        kwargs = (
            await
            self._extract_captcha_kwargs(
                rs, question, phone))
        if not kwargs:
            raise CaptchaError(
                'No captcha images'
                ' extracted')

        session = await self._get_session()
        solution = await self.captcha.solve(
            rs, session,
            phone=phone, **kwargs)
        if not solution:
            raise CaptchaError(
                'Solver returned empty')

        vr = await self._request(
            'POST', URL_CAPTCHA_VERIFY,
            {'aid': APP_AID,
             'host': self.api_host},
            json.dumps({
                'solution': solution,
                'detail': detail,
                'verify_event':
                    verify_event}),
            content_type='application/json',
            proxy_url=proxy_url,
            phone=phone)

        if (not vr
                or not isinstance(vr, dict)):
            raise CaptchaError(
                'Verify returned empty')
        if (vr.get('code') == 200
                or 'success' in (
                    str(vr).lower())):
            return True
        raise CaptchaError(
            f'Verify failed:'
            f' {vr.get("code")}')

    async def _activate_device(
            self,
            proxy_url: Optional[str] = None,
            phone: str = '') -> bool:
        try:
            return (
                await self._solve_captcha_flow(
                    '3d', '',
                    self.device.region, '',
                    'device_activate',
                    proxy_url, phone))
        except CaptchaError as exc:
            log.warning(
                f'[{mask_phone(phone)}]'
                f' Activate: {exc}')
            return False

    async def _handle_sms_captcha(
            self, response_data: dict,
            proxy_url: Optional[str] = None,
            phone: str = '') -> bool:
        if not isinstance(
                response_data, dict):
            return False
        raw_conf = safe_get(
            response_data, 'data',
            'verify_center_decision_conf',
            default='')
        if not raw_conf:
            raise CaptchaError(
                'No captcha config'
                ' in response')
        try:
            conf = (
                json.loads(raw_conf)
                if isinstance(raw_conf, str)
                else raw_conf)
        except (json.JSONDecodeError,
                TypeError) as exc:
            raise ParseError(
                f'Captcha conf parse:'
                f' {exc}')
        if not isinstance(conf, dict):
            raise ParseError(
                'Captcha conf not dict')
        return await self._solve_captcha_flow(
            conf.get('subtype', '3d'),
            conf.get('detail', ''),
            conf.get('region', ''),
            conf.get('verify_event', ''),
            'passport_mobile_send_code',
            proxy_url, phone)

    # ---- Device setup ----

    async def _get_or_create_device(
            self, country: str,
            proxy_url: Optional[str] = None,
            phone: str = '') -> bool:
        masked = mask_phone(phone)
        pooled = await self.pool.get(country)
        if pooled:
            self.device = pooled
            self.device.session_uses = 0
            self.api_host = (
                self.config.random_host())
            self._cookie_jar.clear()
            log.info(
                f'[{masked}] Pooled'
                f' device'
                f' {self.device.device_id}'
                f' (used'
                f' {self.device.use_count}x,'
                f' ver='
                f'{self.device.version_name})')
            await self._ensure_ms_token(
                proxy_url, phone)
            return True

        log.info(
            f'[{masked}] Registering'
            f' new device'
            f' for {country}...')
        self.device = Device.generate(
            self.config, country)
        self.api_host = (
            self.config.random_host())
        self._cookie_jar.clear()

        try:
            if not await (
                    self._register_device(
                        proxy_url, phone)):
                raise DeviceError(
                    'Registration'
                    ' returned false')
        except ParseError as exc:
            raise DeviceError(str(exc))

        await self._activate_device(
            proxy_url, phone)
        await self._ensure_ms_token(
            proxy_url, phone)
        await self.pool.add(self.device)
        return True

    async def _rotate_device(
            self, country: str,
            proxy_url: Optional[str] = None,
            phone: str = '') -> bool:
        if self.device:
            await self.pool.remove(
                self.device)
        return (
            await self._get_or_create_device(
                country, proxy_url, phone))

    # ---- Setup phase ----

    async def _setup_for_send(
            self, phone: str
    ) -> Tuple[str, str, str, Optional[str]]:
        masked = mask_phone(phone)
        session = await self._get_session()
        info = await self.hlr.lookup(
            session, phone)
        if not info:
            raise HLRError(
                f'HLR lookup returned'
                f' no data for {masked}')

        country = info['country_code']
        prefix = info['country_prefix']
        national = info['national_number']
        log.info(
            f'[{masked}]'
            f' {info["country_name"]}'
            f' +{prefix}'
            f' ({info.get("carrier", "?")})')

        proxy_url = await self.proxy.get(
            country)

        if not await (
                self._get_or_create_device(
                    country,
                    proxy_url, phone)):
            raise DeviceError(
                'Device setup failed')

        return (
            country, prefix,
            national, proxy_url)

    # ---- Retry loop ----

    async def _send_with_retries(
            self, phone: str,
            sms_type: int,
            country: str, prefix: str,
            national: str,
            proxy_url: Optional[str],
            result: Dict[str, Any]
    ) -> Dict[str, Any]:
        masked = mask_phone(phone)
        captcha_attempts = 0

        for attempt in range(
                self.config.max_retries):
            check_shutdown()

            # Proactive device rotation
            if self.device.needs_rotation(
                    self.config.device_max_uses):
                log.info(
                    f'[{masked}] Device'
                    f' used'
                    f' {self.device.session_uses}'
                    f'x, proactive rotation')
                await self._rotate_device(
                    country, proxy_url, phone)

            # Proactive ms_token refresh
            if not self.device.ms_token_valid:
                await self._ensure_ms_token(
                    proxy_url, phone)

            self.device.record_session_use()

            log.info(
                f'[{masked}] attempt'
                f' {attempt + 1}'
                f'/{self.config.max_retries}'
                f' (dev='
                f'{self.device.session_uses}'
                f', tok='
                f'{self.device.ms_token_uses}'
                f', ver='
                f'{self.device.version_name}'
                f')')

            body = urlencode({
                'type': sms_type,
                'mobile_prefix': prefix,
                'mobile': national,
                'account_sdk_source': 'app',
                'mix_mode': 1,
                'multi_login': 1,
            })

            try:
                data = await self._request(
                    'POST',
                    f'https://'
                    f'{self.api_host}'
                    f'/passport/mobile/'
                    f'send_code/',
                    self.device.base_params(),
                    body,
                    proxy_url=proxy_url,
                    phone=phone)
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
                        self.config.delay_min,
                        self.config.delay_max))
                continue

            ec = safe_get(
                data, 'data', 'error_code',
                default=None)
            if ec is None:
                ec = safe_get(
                    data, 'error_code',
                    default=-1)
            try:
                ec = int(ec)
            except (ValueError, TypeError):
                ec = -1

            msg = str(
                data.get('message', '')
            ).lower()

            # SUCCESS
            if ec == 0:
                log.info(
                    f'[{masked}]'
                    f' ✓ SMS sent')
                result['status'] = 'success'
                result['error_code'] = 0
                result['timestamp'] = int(
                    time.time())
                return result

            # CAPTCHA
            if ec == TT_CAPTCHA_REQUIRED:
                captcha_attempts += 1
                log.info(
                    f'[{masked}] Captcha'
                    f' ({captcha_attempts}'
                    f'/'
                    f'{MAX_CAPTCHA_ATTEMPTS})')
                if (captcha_attempts
                        > MAX_CAPTCHA_ATTEMPTS):
                    raise CaptchaError(
                        'Captcha loop'
                        ' exceeded')
                try:
                    if await (
                        self
                        ._handle_sms_captcha(
                            data,
                            proxy_url,
                            phone)):
                        await asyncio.sleep(
                            random.uniform(
                                self.config
                                .delay_min,
                                self.config
                                .delay_max))
                        continue
                except (
                    CaptchaError, ParseError
                ):
                    pass
                await self._rotate_device(
                    country, proxy_url, phone)
                continue

            # RATE LIMIT
            if ec in TT_RATE_LIMIT_CODES:
                log.warning(
                    f'[{masked}]'
                    f' Rate limit {ec},'
                    f' backing off')
                await self.limiter.slow_down()
                await asyncio.sleep(
                    jitter_delay(
                        attempt, 2.0, 15.0))
                continue

            # DEVICE BAN
            if ec == TT_DEVICE_BAN:
                log.warning(
                    f'[{masked}]'
                    f' Device ban {ec},'
                    f' rotating')
                await self._rotate_device(
                    country, proxy_url, phone)
                continue

            # MS_TOKEN ERROR
            if ec in TT_MSTOKEN_ERRORS:
                log.warning(
                    f'[{masked}]'
                    f' ms_token error {ec},'
                    f' refreshing')
                self.device.invalidate_ms_token()
                if await (
                        self._ensure_ms_token(
                            proxy_url, phone)):
                    continue
                raise TokenError(
                    f'Refresh failed'
                    f' after error {ec}')

            # FALLBACK
            if ec == -1 and (
                    'success' in msg):
                log.info(
                    f'[{masked}]'
                    f' ✓ SMS sent'
                    f' (message-based)')
                result['status'] = 'success'
                result['error_code'] = 0
                result['timestamp'] = int(
                    time.time())
                return result

            # UNKNOWN
            log.error(
                f'[{masked}]'
                f' ✗ error={ec},'
                f' msg='
                f'{data.get("message", "")[:100]}'
            )
            result['error_code'] = ec
            return result

        result['error_code'] = ERR_MAX_RETRIES
        return result

    # ---- Public entry point ----

    async def send_sms(
            self, phone: str,
            sms_type: int = 5
    ) -> Dict[str, Any]:
        result: Dict[str, Any] = {
            'phone': phone,
            'status': 'fail',
            'error_code': 0,
            'timestamp': int(time.time()),
        }
        try:
            check_shutdown()
            (country, prefix,
             national, proxy_url) = (
                await self._setup_for_send(
                    phone))
            return (
                await self._send_with_retries(
                    phone, sms_type,
                    country, prefix,
                    national, proxy_url,
                    result))

        except ShutdownError:
            result['error_code'] = (
                ERR_SHUTDOWN)
        except HLRError as exc:
            log.error(
                f'[{mask_phone(phone)}]'
                f' HLR: {exc}')
            result['error_code'] = (
                ERR_HLR_FAILED)
        except DeviceError as exc:
            log.error(
                f'[{mask_phone(phone)}]'
                f' Device: {exc}')
            result['error_code'] = (
                ERR_DEVICE_SETUP)
        except CaptchaError as exc:
            log.error(
                f'[{mask_phone(phone)}]'
                f' Captcha: {exc}')
            result['error_code'] = (
                ERR_CAPTCHA_LOOP)
        except TokenError as exc:
            log.error(
                f'[{mask_phone(phone)}]'
                f' Token: {exc}')
            result['error_code'] = (
                ERR_MSTOKEN)
        except NetworkError as exc:
            log.error(
                f'[{mask_phone(phone)}]'
                f' Network: {exc}')
            result['error_code'] = (
                ERR_MAX_RETRIES)
        except ParseError as exc:
            log.error(
                f'[{mask_phone(phone)}]'
                f' Parse: {exc}')
            result['error_code'] = (
                ERR_MAX_RETRIES)
        except AppError as exc:
            log.error(
                f'[{mask_phone(phone)}]'
                f' App: {exc}')
            result['error_code'] = ERR_CRASH
        except Exception as exc:
            log.error(
                f'[{mask_phone(phone)}]'
                f' {type(exc).__name__}:'
                f' {exc}')
            result['error_code'] = ERR_CRASH
        finally:
            if (self.device
                    and self.device.registered):
                await self.pool.update(
                    self.device)
            await self.close()
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
        f'Loaded {len(numbers)} from {path}')
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

    def _open_sync(self) -> None:
        self._sf = open(
            self._sp, 'w', newline='')
        self._ff = open(
            self._fp, 'w', newline='')
        self._sw = csv.writer(self._sf)
        self._fw = csv.writer(self._ff)
        self._sw.writerow(
            ['phone', 'timestamp'])
        self._fw.writerow(
            ['phone', 'error_code',
             'timestamp'])
        self._sf.flush()
        self._ff.flush()

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

    async def write(
            self,
            result: Dict[str, Any]) -> None:
        async with self._lock:
            ok = (
                result['status'] == 'success')
            if ok:
                row = [
                    result['phone'],
                    result['timestamp']]
                self.success += 1
            else:
                row = [
                    result['phone'],
                    result['error_code'],
                    result['timestamp']]
                self.fail += 1
            await run_in_io(
                self._write_sync, ok, row)
            total = self.success + self.fail
            if total % 25 == 0:
                log.info(
                    f'Progress: {total},'
                    f' {self.success} ok,'
                    f' {self.fail} fail')

    def _close_sync(self) -> None:
        for f in (self._sf, self._ff):
            if f:
                try:
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
            f'DONE: {total} total,'
            f' {self.success} ok'
            f' ({rate:.1f}%),'
            f' {self.fail} fail')


# ============================================
#  FINALIZER
# ============================================

class Finalizer:

    def __init__(self):
        self._pool: Optional[
            DevicePool] = None
        self._writer: Optional[
            ResultWriter] = None
        self._connector: Optional[
            aiohttp.TCPConnector] = None
        self._sessions: List[
            aiohttp.ClientSession] = []

    def register(
            self,
            pool: Optional[
                DevicePool] = None,
            writer: Optional[
                ResultWriter] = None,
            connector: Optional[
                aiohttp.TCPConnector] = None,
            session: Optional[
                aiohttp.ClientSession] = None
    ) -> None:
        if pool:
            self._pool = pool
        if writer:
            self._writer = writer
        if connector:
            self._connector = connector
        if session:
            self._sessions.append(session)

    async def finalize(self) -> None:
        log.info('Finalizing...')
        if self._pool:
            try:
                await self._pool.save(
                    force=True)
            except Exception as exc:
                log.error(
                    f'Pool save: {exc}')
        if self._writer:
            try:
                self._writer.summary()
                await self._writer.close()
            except Exception as exc:
                log.error(
                    f'Writer: {exc}')
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
                        f'Task exception:'
                        f' {exc}')
            processed += len(done)
    return processed


# ============================================
#  PROCESS CSV
# ============================================

async def process_csv(
        config: AppConfig,
        numbers: List[str],
        proxies: Optional[List[str]] = None,
        sms_type: int = 5,
        threads: int = 5,
        success_file: str = 'success.csv',
        fail_file: str = 'failed.csv'
) -> None:
    config.validate('csv')

    writer = ResultWriter(
        success_file, fail_file)
    await writer.open()
    pool = DevicePool(config)
    connector = aiohttp.TCPConnector(
        limit=threads * 3,
        enable_cleanup_closed=True)
    finalizer = Finalizer()
    finalizer.register(
        pool=pool, writer=writer,
        connector=connector)

    sem = asyncio.Semaphore(threads)
    captcha = CaptchaSolver(config)
    hlr = HLRLookup(config)
    proxy_mgr = ProxyManager(proxies)
    limiter = RateLimiter(
        config.global_rps,
        config.global_burst)

    async with aiohttp.ClientSession() as cs:
        bal = await captcha.check_balance(cs)
        if bal == 0:
            log.error('Captcha balance 0')
            await finalizer.finalize()
            return

    log.info(
        f'Pool:'
        f' {await pool.count()} devices')

    try:
        async def worker(
                phone: str) -> None:
            if shutdown_event.is_set():
                return
            async with sem:
                if shutdown_event.is_set():
                    return
                client = TikTokSMS(
                    config, connector,
                    proxy_mgr, captcha,
                    hlr, pool, limiter)
                result = (
                    await client.send_sms(
                        phone, sms_type))
                await writer.write(result)
                await asyncio.sleep(
                    random.uniform(
                        config.delay_min,
                        config.delay_max))

        await run_batched(numbers, worker)

    except asyncio.CancelledError:
        log.info(
            'CSV processing cancelled')
    except Exception as exc:
        log.error(
            f'CSV:'
            f' {type(exc).__name__}:'
            f' {exc}')
    finally:
        await finalizer.finalize()


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
#  PROCESS API
# ============================================

async def process_api(
        config: AppConfig,
        proxies: Optional[List[str]] = None,
        sms_type: int = 5,
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
    pool = DevicePool(config)
    connector = aiohttp.TCPConnector(
        limit=threads * 3,
        enable_cleanup_closed=True)
    finalizer = Finalizer()
    finalizer.register(
        pool=pool, writer=writer,
        connector=connector)

    sem = asyncio.Semaphore(threads)
    captcha = CaptchaSolver(config)
    hlr = HLRLookup(config)
    proxy_mgr = ProxyManager(proxies)
    limiter = RateLimiter(
        config.global_rps,
        config.global_burst)
    number_api = NumberAPI(config)

    async with aiohttp.ClientSession() as cs:
        bal = await captcha.check_balance(cs)
        if bal == 0:
            log.error('Captcha balance 0')
            await finalizer.finalize()
            return

    log.info(
        f'Pool:'
        f' {await pool.count()} devices')

    total_claimed = 0
    batch_num = 0
    empty_streak = 0

    api_session = aiohttp.ClientSession(
        connector=connector,
        connector_owner=False)
    finalizer.register(session=api_session)

    try:
        while not shutdown_event.is_set():
            batch_num += 1
            log.info(
                f'=== Batch {batch_num}:'
                f' claiming'
                f' {claim_count} ===')

            try:
                cd = await number_api.claim(
                    api_session,
                    claim_count,
                    lease_seconds)
            except (
                NetworkError, AppError
            ) as exc:
                log.error(
                    f'Claim: {exc}')
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
                log.warning(
                    f'Empty claim'
                    f' ({empty_streak}'
                    f'/{MAX_EMPTY_CLAIMS})')
                if (empty_streak
                        >= MAX_EMPTY_CLAIMS):
                    break
                await asyncio.sleep(
                    min(
                        2 ** empty_streak,
                        30))
                continue

            empty_streak = 0
            claim_id = cd.get(
                'claimId', '')
            items = cd['items']
            total_claimed += len(items)
            log.info(
                f'Batch {batch_num}:'
                f' {len(items)} numbers')

            collector = BatchCollector()

            async def worker(
                    item: dict) -> None:
                if shutdown_event.is_set():
                    return
                phone = item['phone']
                nid = item['id']
                async with sem:
                    if (
                        shutdown_event
                        .is_set()
                    ):
                        return
                    client = TikTokSMS(
                        config, connector,
                        proxy_mgr, captcha,
                        hlr, pool, limiter)
                    result = (
                        await client.send_sms(
                            phone, sms_type))
                    await writer.write(
                        result)
                    entry: Dict[str, Any] = {
                        'id': nid,
                        'status':
                            result['status']}
                    if (result['status']
                            == 'fail'):
                        entry['note'] = (
                            f'error_code='
                            f'{result["error_code"]}'
                        )
                    await collector.add(
                        entry)
                    await asyncio.sleep(
                        random.uniform(
                            config.delay_min,
                            config.delay_max))

            await run_batched(
                items, worker)

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
                        f'Report: {exc}')

            await pool.save()
            await asyncio.sleep(
                random.uniform(1.0, 3.0))

        log.info(
            f'Total claimed:'
            f' {total_claimed}')

    except asyncio.CancelledError:
        log.info('API cancelled')
    except Exception as exc:
        log.error(
            f'API:'
            f' {type(exc).__name__}:'
            f' {exc}')
    finally:
        await finalizer.finalize()


# ============================================
#  PREWARM
# ============================================

async def prewarm_pool(
        config: AppConfig,
        proxies: Optional[List[str]] = None,
        count: int = 10,
        regions: Optional[List[str]] = None
) -> None:
    """Pre-register devices into pool.

    Uses TikTokSigner.encrypt(dict) for payload
    encryption — the library serializes dict to
    JSON internally before encrypting.

    All signer parameters are derived from the
    device's APKVersion for consistency.
    """
    config.validate('prewarm')

    if not regions:
        regions = [
            'US', 'GB', 'DE', 'AT',
            'VN', 'TR', 'BR']

    proxy_mgr = ProxyManager(proxies)
    pool = DevicePool(config)
    limiter = RateLimiter(5.0, 10)
    connector = aiohttp.TCPConnector(
        limit=20,
        enable_cleanup_closed=True)

    td = count * len(regions)
    log.info(
        f'Prewarm: {count}'
        f' × {len(regions)}'
        f' = {td} devices'
        f' (version='
        f'{config.default_version})')

    region_sessions: Dict[
        str, aiohttp.ClientSession] = {
        r: aiohttp.ClientSession(
            connector=connector,
            connector_owner=False,
            cookie_jar=(
                aiohttp.CookieJar(
                    unsafe=True)))
        for r in regions
    }

    try:
        sem = asyncio.Semaphore(5)

        async def register_one(
                wi: Tuple[str, int]
        ) -> None:
            region, index = wi
            async with sem:
                if shutdown_event.is_set():
                    return
                await limiter.acquire()

                device = Device.generate(
                    config, region)
                ver = device.apk_version
                proxy_url = (
                    await proxy_mgr.get(
                        region))
                tag = (
                    f'[pw-{region}-{index}]')

                # Validate before sending
                issues = (
                    device.validate_payload())
                if issues:
                    fatal = [
                        i for i in issues
                        if 'deprecated'
                        not in i]
                    for issue in issues:
                        log.warning(
                            f'{tag}'
                            f' Validation:'
                            f' {issue}')
                    if fatal:
                        log.error(
                            f'{tag}'
                            f' Skipping:'
                            f' {len(fatal)}'
                            f' fatal issues')
                        return

                payload = (
                    device
                    .registration_payload())

                if config.debug_registration:
                    header = payload.get(
                        'header', {})
                    log.info(
                        f'{tag} Payload:'
                        f' aid='
                        f'{header.get("aid")}'
                        f' ver='
                        f'{header.get("app_version")}'
                        f' manifest='
                        f'{header.get("manifest_version_code")}'
                        f' sig='
                        f'{header.get("sig_hash")}'
                        f' device='
                        f'{header.get("device_model")}'
                        f' os_api='
                        f'{header.get("os_api")}'
                    )

                encrypted = (
                    TikTokSigner.encrypt(
                        payload))

                if config.debug_registration:
                    log.info(
                        f'{tag} Encrypted:'
                        f' {len(encrypted)}'
                        f' bytes')

                ps = urlencode(
                    device.base_params())

                auth = (
                    TikTokSigner
                    .generate_headers(
                        params=ps,
                        data=encrypted,
                        device_id=(
                            device
                            .device_id),
                        aid=int(APP_AID),
                        lc_id=(
                            ver.signer_lc_id),
                        sdk_ver=(
                            ver.signer_sdk_ver),
                        sdk_ver_code=(
                            ver
                            .signer_sdk_ver_code
                        ),
                        version_name=(
                            ver
                            .version_name),
                        version_code=(
                            ver
                            .manifest_int),
                        unix=int(
                            time.time()),
                    ))

                # Validate X-Gorgon prefix
                gorgon = auth.get(
                    'x-gorgon', '')
                if gorgon:
                    if not gorgon.startswith(
                            ver.gorgon_prefix):
                        level = (
                            log.error
                            if config
                            .debug_registration
                            else log.warning)
                        level(
                            f'{tag}'
                            f' X-Gorgon prefix'
                            f' mismatch:'
                            f' expected'
                            f' {ver.gorgon_prefix},'
                            f' got'
                            f' {gorgon[:4]}.'
                            f' Try: pip install'
                            f' --upgrade'
                            f' tiktok-signer')

                if config.debug_registration:
                    log.info(
                        f'{tag} Auth'
                        f' headers'
                        f' ({len(auth)}'
                        f' keys):')
                    for key in sorted(
                            auth.keys()):
                        log.info(
                            f'{tag}  {key}:'
                            f' {truncate_header(auth[key])}'
                        )

                headers = {
                    'User-Agent': (
                        device.user_agent),
                    'Accept-Encoding':
                        'gzip',
                    'Content-Type': (
                        'application/'
                        'octet-stream;'
                        'tt-data=a'),
                }
                headers.update(auth)

                if config.debug_registration:
                    log.info(
                        f'{tag}'
                        f' User-Agent:'
                        f' {device.user_agent}')
                    log.info(
                        f'{tag}'
                        f' URL params'
                        f' len={len(ps)}')

                url = (
                    f'{URL_DEVICE_REGISTER}'
                    f'?{ps}')

                session = (
                    region_sessions[region])
                try:
                    kw: Dict[str, Any] = {
                        'headers': headers,
                        'data': encrypted,
                        'timeout': (
                            aiohttp
                            .ClientTimeout(
                                total=15)),
                    }
                    if proxy_url:
                        kw['proxy'] = (
                            proxy_url)

                    async with (
                        session.post(
                            url, **kw)
                    ) as resp:
                        raw = (
                            await resp.read())
                        
                        # === CRITICAL DEBUG - FULL RESPONSE ===
                        import json as _dbg_json
                        log.info(f'{tag} ===== RAW RESPONSE START =====')
                        log.info(f'{tag} HTTP Status: {resp.status}')
                        log.info(f'{tag} Response Headers:')
                        for hname, hval in resp.headers.items():
                            log.info(f'{tag}   {hname}: {hval}')
                        log.info(f'{tag} Raw bytes length: {len(raw)}')
                        log.info(f'{tag} Raw bytes (first 500): {raw[:500]}')
                        log.info(f'{tag} Raw bytes (full): {raw}')
                        try:
                            _temp_data = _dbg_json.loads(raw)
                            log.info(f'{tag} Parsed JSON:')
                            log.info(f'{tag} {_dbg_json.dumps(_temp_data, indent=2, ensure_ascii=False)}')
                        except Exception as _e:
                            log.info(f'{tag} Could not parse as JSON: {_e}')
                        log.info(f'{tag} ===== RAW RESPONSE END =====')
                        # === END CRITICAL DEBUG ===

                        if (config
                                .debug_registration
                        ):
                            log.info(
                                f'{tag}'
                                f' Response:'
                                f' HTTP'
                                f' {resp.status},'
                                f' {len(raw)}'
                                f' bytes')
                            # Log response
                            # headers
                            for rh in (
                                'x-tt-logid',
                                'x-tt-trace-id',
                                'content-type',
                            ):
                                rv = (
                                    resp.headers
                                    .get(rh, ''))
                                if rv:
                                    log.info(
                                        f'{tag}'
                                        f'  {rh}:'
                                        f' {rv[:80]}'
                                    )

                        data = None
                        decode_method = (
                            'unknown')
                        try:
                            data = (
                                json.loads(raw))
                            decode_method = (
                                'plaintext')
                        except (
                            json
                            .JSONDecodeError,
                            ValueError
                        ):
                            try:
                                data = (
                                    json.loads(
                                        TikTokSigner
                                        .decrypt(
                                            raw)))
                                decode_method = (
                                    'decrypted')
                            except Exception:
                                pass

                        if (config
                                .debug_registration
                        ):
                            log.info(
                                f'{tag}'
                                f' Decode:'
                                f' {decode_method}')
                            if (data
                                    and isinstance(
                                        data,
                                        dict)):
                                for dk in (
                                    'device_id',
                                    'install_id',
                                    'error_code',
                                    'message',
                                    'status_code',
                                ):
                                    if dk in data:
                                        log.info(
                                            f'{tag}'
                                            f'  {dk}='
                                            f'{data[dk]}'
                                        )

                        if (data
                                and isinstance(
                                    data, dict)
                                and data.get(
                                    'device_id',
                                    0)):
                            device.device_id = (
                                str(data[
                                    'device_id'
                                ]))
                            device.install_id = (
                                str(data.get(
                                    'install_id',
                                    0)))
                            device.registered = (
                                True)
                            await pool.add(
                                device)
                            await (
                                proxy_mgr
                                .report_success(
                                    proxy_url))
                            log.info(
                                f'{tag} ✓'
                                f' {device.device_id}'
                            )
                        else:
                            await (
                                proxy_mgr
                                .report_failure(
                                    proxy_url))
                            # Diagnose failure
                            ec = '?'
                            msg = '?'
                            if (data
                                    and isinstance(
                                        data,
                                        dict)):
                                ec = data.get(
                                    'error_code',
                                    data.get(
                                        'status_code',
                                        '?'))
                                msg = str(
                                    data.get(
                                        'message',
                                        data.get(
                                            'error',
                                            '?'))
                                )[:150]
                            log.warning(
                                f'{tag}'
                                f' ✗ failed'
                                f' (ec={ec},'
                                f' msg={msg})')
                            # Hints
                            msg_l = str(
                                msg).lower()
                            ec_s = str(ec)
                            if ('signature'
                                    in msg_l):
                                log.error(
                                    f'{tag}'
                                    f' HINT:'
                                    f' sig_hash'
                                    f' may be'
                                    f' outdated')
                            if ('update'
                                    in msg_l):
                                log.error(
                                    f'{tag}'
                                    f' HINT:'
                                    f' APK too'
                                    f' old')
                            if ('1105'
                                    in ec_s
                                    or '1109'
                                    in ec_s):
                                log.error(
                                    f'{tag}'
                                    f' HINT:'
                                    f' signer'
                                    f' mismatch')

                except asyncio.TimeoutError:
                    await (
                        proxy_mgr
                        .report_failure(
                            proxy_url))
                    log.warning(
                        f'{tag}'
                        f' ✗ timeout')
                except (
                    aiohttp.ClientError
                ) as exc:
                    await (
                        proxy_mgr
                        .report_failure(
                            proxy_url))
                    log.error(
                        f'{tag} ✗'
                        f' {type(exc).__name__}'
                    )
                except Exception as exc:
                    log.error(
                        f'{tag} ✗'
                        f' {type(exc).__name__}'
                        f': {exc}')

                await asyncio.sleep(
                    random.uniform(0.5, 1.5))

        work_items: List[
            Tuple[str, int]] = [
            (r, idx)
            for r in regions
            for idx in range(count)
        ]

        await run_batched(
            work_items, register_one)

    finally:
        for s in region_sessions.values():
            if not s.closed:
                try:
                    await s.close()
                except Exception:
                    pass
        await pool.save(force=True)
        if not connector.closed:
            await connector.close()

    tr = await pool.count()
    log.info(
        f'Pool ready: {tr} devices')


# ============================================
#  DEPENDENCY CHECK
# ============================================

def check_dependencies() -> bool:
    """Verify tiktok-signer is installed and
    functional.

    Checks:
    1. generate_headers() returns dict with
       required auth keys
    2. encrypt(dict) returns non-empty bytes
    3. decrypt() round-trip (warning only)
    4. encrypt(dict) specifically tested since
       our code passes dict payloads directly
       (not pre-serialized JSON strings)
    5. X-Gorgon prefix validation against
       default APK version
    """
    try:
        ver = DEFAULT_APK_VERSION

        # 1. Header generation with version
        #    params from registry
        result = TikTokSigner.generate_headers(
            params='test=1',
            device_id='7123456789012345678',
            aid=int(APP_AID),
            lc_id=ver.signer_lc_id,
            sdk_ver=ver.signer_sdk_ver,
            sdk_ver_code=(
                ver.signer_sdk_ver_code),
            version_name=ver.version_name,
            version_code=ver.manifest_int,
        )
        if not isinstance(result, dict):
            log.error(
                'tiktok-signer:'
                ' generate_headers()'
                ' returned non-dict')
            return False

        required_headers = {
            'x-argus', 'x-gorgon',
            'x-khronos'}
        missing = (
            required_headers - result.keys())
        if missing:
            log.error(
                f'tiktok-signer:'
                f' missing required headers'
                f' {missing}')
            return False

        # Validate X-Gorgon prefix
        gorgon = result.get('x-gorgon', '')
        if gorgon:
            if gorgon.startswith(
                    ver.gorgon_prefix):
                log.info(
                    f'X-Gorgon prefix OK:'
                    f' {gorgon[:4]}'
                    f' (expected'
                    f' {ver.gorgon_prefix}'
                    f' for'
                    f' {ver.version_name})')
            else:
                log.warning(
                    f'X-Gorgon prefix'
                    f' mismatch:'
                    f' got {gorgon[:4]},'
                    f' expected'
                    f' {ver.gorgon_prefix}'
                    f' for APK'
                    f' {ver.version_name}.'
                    f' Try: pip install'
                    f' --upgrade'
                    f' tiktok-signer')

        # 2. Encryption with dict input
        # (matches our actual usage pattern)
        test_payload = {
            'magic_tag': 'ss_app_log',
            'header': {'aid': 1233},
            '_gen_time': int(time.time()),
        }
        encrypted = TikTokSigner.encrypt(
            test_payload)
        if not isinstance(encrypted, bytes):
            log.error(
                'tiktok-signer:'
                ' encrypt(dict)'
                ' returned non-bytes')
            return False
        if not encrypted:
            log.error(
                'tiktok-signer:'
                ' encrypt(dict)'
                ' returned empty')
            return False

        # 3. Decryption round-trip
        # (non-critical — some versions may
        # not support decrypt)
        try:
            decrypted = (
                TikTokSigner.decrypt(
                    encrypted))
            if decrypted:
                parsed = json.loads(decrypted)
                if parsed.get(
                        'magic_tag'
                ) != 'ss_app_log':
                    log.warning(
                        'tiktok-signer:'
                        ' decrypt()'
                        ' round-trip mismatch')
        except Exception:
            log.warning(
                'tiktok-signer:'
                ' decrypt() non-critical'
                ' fail')

        # 4. Signing with body data
        # (matches send_code flow)
        body_result = (
            TikTokSigner.generate_headers(
                params='aid=1233',
                data='type=5&mobile=123',
                device_id='7123456789012345678',
                aid=int(APP_AID),
                lc_id=ver.signer_lc_id,
                sdk_ver=ver.signer_sdk_ver,
                sdk_ver_code=(
                    ver.signer_sdk_ver_code),
                version_name=ver.version_name,
                version_code=ver.manifest_int,
            ))
        if 'x-argus' not in body_result:
            log.error(
                'tiktok-signer:'
                ' signing with body'
                ' missing x-argus')
            return False

        log.info(
            f'tiktok-signer OK'
            f' (ver={ver.version_name},'
            f' sdk={ver.signer_sdk_ver},'
            f' headers:'
            f' {", ".join(sorted(result.keys()))}'
            f')')
        return True

    except ImportError as exc:
        log.error(
            f'tiktok-signer not installed:'
            f' {exc}.'
            f' Run:'
            f' pip install tiktok-signer')
        return False
    except Exception as exc:
        log.error(
            f'tiktok-signer check:'
            f' {type(exc).__name__}:'
            f' {exc}')
        return False


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
                if (s and not
                        s.startswith('#')):
                    proxies.append(s)
    return proxies if proxies else None


def main():
    _setup_signals()

    parser = argparse.ArgumentParser(
        description=(
            'TikTok SMS Module v10.2'),
        epilog=(
            'Requires:'
            ' pip install tiktok-signer'))

    source = (
        parser
        .add_mutually_exclusive_group(
            required=True))
    source.add_argument(
        '--input', '-i', default=None,
        help='CSV file with numbers')
    source.add_argument(
        '--api', action='store_true',
        help='Use Number API')
    source.add_argument(
        '--prewarm', action='store_true',
        help='Pre-register devices')

    parser.add_argument(
        '--success', '-s',
        default='success.csv')
    parser.add_argument(
        '--fail', '-f',
        default='failed.csv')
    parser.add_argument(
        '--proxy', '-p', default=None,
        help='Single proxy string')
    parser.add_argument(
        '--proxy-file', default=None,
        help='File with proxies')
    parser.add_argument(
        '--threads', '-t',
        type=int, default=5)
    parser.add_argument(
        '--type', type=int, default=5,
        choices=[1, 5],
        help='1=register, 5=reset')
    parser.add_argument(
        '--config', '-c',
        default='config.json')
    parser.add_argument(
        '--claim-count',
        type=int, default=None)
    parser.add_argument(
        '--lease-seconds',
        type=int, default=None)
    parser.add_argument(
        '--pool-count',
        type=int, default=10)
    parser.add_argument(
        '--pool-regions',
        nargs='+', default=None)
    parser.add_argument(
        '--rps', type=float, default=None,
        help='Global RPS limit')
    parser.add_argument(
        '--skip-check',
        action='store_true')
    parser.add_argument(
        '--debug-registration',
        action='store_true',
        help=(
            'Enable verbose registration'
            ' logging'))
    parser.add_argument(
        '--version',
        default=None,
        choices=[
            v.version_name
            for v in APK_VERSIONS],
        help=(
            'APK version to use'
            f' (default:'
            f' {DEFAULT_APK_VERSION.version_name})'
        ))
    args = parser.parse_args()

    if not args.skip_check:
        if not check_dependencies():
            sys.exit(1)

    config = load_config(args.config)

    # Apply CLI overrides
    overrides: Dict[str, Any] = {}
    if args.rps is not None:
        overrides['global_rps'] = args.rps
    if args.debug_registration:
        overrides['debug_registration'] = True
    if args.version is not None:
        overrides['default_version'] = (
            args.version)
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
        log.info(
            f'Proxies:'
            f' {len(proxies)} loaded')

    ver = config.get_default_apk_version()
    log.info(
        f'APK version:'
        f' {ver.version_name}'
        f' (stability={ver.stability},'
        f' tt-ok={ver.tt_ok_version},'
        f' gorgon={ver.gorgon_prefix},'
        f' passport-sdk='
        f'{ver.passport_sdk_version},'
        f' target-sdk={ver.target_sdk})')

    # Version staleness warning
    if ver.is_outdated(
            VERSION_STALENESS_DAYS):
        log.warning(
            f'APK version'
            f' {ver.version_name}'
            f' (released'
            f' {ver.release_date})'
            f' is older than'
            f' {VERSION_STALENESS_DAYS}'
            f' days — consider'
            f' updating')

    # Deprecated version warning
    if ver.stability == 'deprecated':
        log.warning(
            f'APK version'
            f' {ver.version_name}'
            f' is deprecated.'
            f' Recommended:'
            f' --version'
            f' {DEFAULT_APK_VERSION.version_name}')

    try:
        if args.prewarm:
            log.info(
                f'Prewarm:'
                f' {args.pool_count}'
                f' per region')
            asyncio.run(prewarm_pool(
                config, proxies,
                args.pool_count,
                args.pool_regions))
        elif args.api:
            log.info(
                f'API mode:'
                f' batch={cc},'
                f' lease={ls}s,'
                f' threads='
                f'{args.threads},'
                f' type={args.type}')
            asyncio.run(process_api(
                config, proxies,
                args.type,
                args.threads,
                cc, ls,
                args.success,
                args.fail))
        else:
            numbers = read_numbers(
                args.input)
            if not numbers:
                log.error(
                    'No numbers found')
                sys.exit(1)
            log.info(
                f'CSV mode:'
                f' {len(numbers)} numbers,'
                f' threads='
                f'{args.threads},'
                f' type={args.type}')
            asyncio.run(process_csv(
                config, numbers, proxies,
                args.type,
                args.threads,
                args.success,
                args.fail))
    except ConfigError as exc:
        log.error(
            f'Config error: {exc}')
        sys.exit(1)


if __name__ == '__main__':
    main()