"""
TikTok SMS v7.0 — Direct Pipeline
Server version (Linux/Windows)

Pipeline:
  1. Device register (log16 host, JSON body)
  2. Warmup (app_alert_check, feed)
  3. send_code (full Argus/Gorgon/Ladon signing)
  4. Captcha handling:
     a) hcaptcha auto-pass (code=200, success) -> retry send_code
     b) slide puzzle -> cv2 solve -> verify -> retry send_code
     c) 3d captcha -> fallback to JustScrape API
  5. Retry send_code after captcha
  6. Rate limit (ec=7) -> rotate proxy, new device
  7. Empty response -> rotate proxy, new device

Requirements:
  pip install requests pycryptodome opencv-python numpy

Usage:
  python tiktok_sms.py +5588951570521
  python tiktok_sms.py +5588951570521 --region br --type 33
  python tiktok_sms.py +5588951570521 --no-proxy
  python tiktok_sms.py +5588951570521 --proxy user:pass@host:port
  python tiktok_sms.py +5588951570521 --batch +18304034231 +18194146343
  python tiktok_sms.py --test-proxy --region br
"""

import time
import string
import random
import base64
import requests
import json
import hashlib
import uuid
import ctypes
import logging
import argparse
import sys
from urllib.parse import urlencode, parse_qs, quote
from os import urandom
from struct import unpack
from base64 import b64encode
from hashlib import md5

import cv2
import numpy as np
from Crypto.Cipher.AES import new as aes_new, MODE_CBC, block_size
from Crypto.Util.Padding import pad

import urllib3
urllib3.disable_warnings()


# ============================================================
# LOGGING
# ============================================================

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger("tiktok")


# ============================================================
# CONFIG
# ============================================================

REGISTER_HOST = "log16-normal-alisg.tiktokv.com"
API_HOST = "api16-normal-c-useast2a.tiktokv.com"
CAPTCHA_TT_HOST = "rc-verification-i18n.tiktokv.com"

# JustScrape captcha API (fallback for 3d captcha)
CAPTCHA_API_HOST = "http://91.98.69.217:9962"
CAPTCHA_API_KEY = "fSm1K4p0TPxqx7ONBkcGNAbC"

AID = 1233
LICENSE_ID = 1611921764
APP_NAME = "musical_ly"
VERSION_CODE = "370004"
VERSION_NAME = "37.0.4"
MANIFEST_VERSION = "2023700040"
BUILD_NUMBER = "37.0.4"
CHANNEL = "googleplay"
SDK_VER_STR = "v04.04.05-ov-android"
SDK_VER_INT = 134744640

DEVICE_TYPE = "SO-51A"
DEVICE_BRAND = "sony"
OS_VERSION = "14"
OS_API = "34"
DPI = "512"
RESOLUTION = "1344*2992"
HOST_ABI = "armeabi-v7a"

PROXY_USER = "iproyal1982"
PROXY_PASS = "Vm3U6A8e"
PROXY_HOST = "geo.iproyal.com"
PROXY_PORT = "12321"

MAX_CAPTCHA_RETRIES = 3
MAX_SEND_RETRIES = 2
MAX_PER_SESSION = 3

WARMUP_DELAY = (2.0, 4.0)
REQUEST_DELAY = (1.5, 3.0)
POST_CAPTCHA_DELAY = (2.0, 4.0)


# ============================================================
# REGION PROFILES
# ============================================================

REGIONS = {
    "br": {"lang": "pt", "tz": "America/Sao_Paulo", "tz_off": "-10800",
           "carrier": "BR", "mcc": "72410", "locale": "pt"},
    "co": {"lang": "es", "tz": "America/Bogota", "tz_off": "-18000",
           "carrier": "CO", "mcc": "732101", "locale": "es"},
    "us": {"lang": "en", "tz": "America/New_York", "tz_off": "-18000",
           "carrier": "US", "mcc": "310260", "locale": "en"},
    "ca": {"lang": "en", "tz": "America/Toronto", "tz_off": "-18000",
           "carrier": "CA", "mcc": "302220", "locale": "en"},
    "it": {"lang": "it", "tz": "Europe/Rome", "tz_off": "3600",
           "carrier": "IT", "mcc": "22210", "locale": "it"},
    "de": {"lang": "de", "tz": "Europe/Berlin", "tz_off": "3600",
           "carrier": "DE", "mcc": "26201", "locale": "de"},
    "ae": {"lang": "en", "tz": "Asia/Dubai", "tz_off": "14400",
           "carrier": "AE", "mcc": "42402", "locale": "en"},
}

PHONE_COUNTRY = {
    "55": "br", "57": "co", "1": "us", "39": "it", "49": "de",
    "971": "ae", "44": "gb", "33": "fr", "34": "es", "52": "mx",
    "7": "ru", "380": "ua", "48": "pl", "61": "au", "81": "jp",
}

AREA_CODES = {
    "55": "55", "57": "57", "1": "1", "39": "39", "49": "49",
    "971": "971", "44": "44", "33": "33", "34": "34",
}


def detect_country(phone):
    clean = phone.lstrip("+")
    for length in [3, 2, 1]:
        pref = clean[:length]
        if pref in PHONE_COUNTRY:
            return PHONE_COUNTRY[pref]
    return "us"


def detect_area(phone):
    clean = phone.lstrip("+")
    for pref in sorted(AREA_CODES, key=len, reverse=True):
        if clean.startswith(pref):
            return AREA_CODES[pref]
    return "1"


# ============================================================
# SM3 HASH
# ============================================================

class SM3:
    def __init__(self):
        self.IV = [
            1937774191, 1226093241, 388252375, 3666478592,
            2842636476, 372324522, 3817729613, 2969243214,
        ]
        self.TJ = [2043430169] * 16 + [2055708042] * 48

    def _rl(self, a, k):
        k %= 32
        return ((a << k) & 0xFFFFFFFF) | ((a & 0xFFFFFFFF) >> (32 - k))

    def _FFJ(self, X, Y, Z, j):
        return X ^ Y ^ Z if j < 16 else (X & Y) | (X & Z) | (Y & Z)

    def _GGJ(self, X, Y, Z, j):
        return X ^ Y ^ Z if j < 16 else (X & Y) | ((~X) & Z)

    def _P0(self, X):
        return X ^ self._rl(X, 9) ^ self._rl(X, 17)

    def _P1(self, X):
        return X ^ self._rl(X, 15) ^ self._rl(X, 23)

    def _CF(self, Vi, Bi):
        W = []
        for i in range(16):
            w = 0x1000000
            d = 0
            for k in range(i * 4, (i + 1) * 4):
                d += Bi[k] * w
                w = int(w / 0x100)
            W.append(d)
        for j in range(16, 68):
            W.append(
                self._P1(W[j - 16] ^ W[j - 9] ^ self._rl(W[j - 3], 15))
                ^ self._rl(W[j - 13], 7) ^ W[j - 6]
            )
        W1 = [W[j] ^ W[j + 4] for j in range(64)]
        A, B, C, D, E, F, G, H = Vi
        for j in range(64):
            SS1 = self._rl(
                ((self._rl(A, 12)) + E + self._rl(self.TJ[j], j)) & 0xFFFFFFFF, 7)
            SS2 = SS1 ^ self._rl(A, 12)
            TT1 = (self._FFJ(A, B, C, j) + D + SS2 + W1[j]) & 0xFFFFFFFF
            TT2 = (self._GGJ(E, F, G, j) + H + SS1 + W[j]) & 0xFFFFFFFF
            D, C, B, A = C, self._rl(B, 9), A, TT1
            H, G, F, E = G, self._rl(F, 19), E, self._P0(TT2)
        return [
            A & 0xFFFFFFFF ^ Vi[0], B & 0xFFFFFFFF ^ Vi[1],
            C & 0xFFFFFFFF ^ Vi[2], D & 0xFFFFFFFF ^ Vi[3],
            E & 0xFFFFFFFF ^ Vi[4], F & 0xFFFFFFFF ^ Vi[5],
            G & 0xFFFFFFFF ^ Vi[6], H & 0xFFFFFFFF ^ Vi[7],
        ]

    def hash(self, msg: bytes) -> bytes:
        msg = bytearray(msg)
        l1 = len(msg)
        msg.append(0x80)
        r = (l1 % 64) + 1
        end = 56 if r <= 56 else 120
        msg.extend(b"\x00" * (end - r))
        bl = l1 * 8
        bls = []
        for _ in range(8):
            bls.append(bl % 0x100)
            bl = int(bl / 0x100)
        msg.extend(reversed(bls))
        gc = len(msg) // 64
        B = [msg[i * 64: (i + 1) * 64] for i in range(gc)]
        V = [self.IV]
        for i in range(gc):
            V.append(self._CF(V[i], B[i]))
        res = b""
        for x in V[-1]:
            res += int(x).to_bytes(4, "big")
        return res


# ============================================================
# SIMON CIPHER
# ============================================================

def _sb(val, pos):
    return 1 if val & (1 << pos) else 0


def _srl(v, n):
    return ((v << n) | (v >> (64 - n))) & 0xFFFFFFFFFFFFFFFF


def _srr(v, n):
    return ((v << (64 - n)) | (v >> n)) & 0xFFFFFFFFFFFFFFFF


def _key_exp(key):
    for i in range(4, 72):
        tmp = _srr(key[i - 1], 3) ^ key[i - 3]
        tmp ^= _srr(tmp, 1)
        key[i] = (ctypes.c_ulonglong(~key[i - 4]).value ^ tmp
                  ^ _sb(0x3DC94C3A046D678B, (i - 4) % 62) ^ 3)
    return key


def simon_enc(pt, k, c=0):
    key = [0] * 72
    key[:4] = k[:4]
    key = _key_exp(key)
    xi, xi1 = pt
    for i in range(72):
        tmp = xi1
        f = _srl(xi1, 1) if c == 1 else _srl(xi1, 1) & _srl(xi1, 8)
        xi1 = (xi ^ f ^ _srl(xi1, 2) ^ key[i]) & 0xFFFFFFFFFFFFFFFF
        xi = tmp
    return [xi, xi1]


# ============================================================
# PROTOBUF ENCODER (minimal)
# ============================================================

class _PW:
    def __init__(self):
        self.d = bytearray()

    def w0(self, b):
        self.d.append(b & 0xFF)

    def w(self, bs):
        self.d.extend(bs)

    def wv(self, v):
        v &= 0xFFFFFFFF
        while v > 0x80:
            self.w0((v & 0x7F) | 0x80)
            v >>= 7
        self.w0(v & 0x7F)

    def ws(self, bs):
        self.wv(len(bs))
        self.w(bs)


def pb_encode(fields: dict) -> bytes:
    w = _PW()
    for idx, val in fields.items():
        if isinstance(val, int):
            w.wv((idx << 3) | 0)
            w.wv(val)
        elif isinstance(val, str):
            w.wv((idx << 3) | 2)
            w.ws(val.encode("utf-8"))
        elif isinstance(val, bytes):
            w.wv((idx << 3) | 2)
            w.ws(val)
        elif isinstance(val, dict):
            w.wv((idx << 3) | 2)
            w.ws(pb_encode(val))
    return bytes(w.d)


# ============================================================
# ARGUS SIGNING
# ============================================================

SIGN_KEY = (b"\xac\x1a\xda\xae\x95\xa7\xaf\x94\xa5\x11J\xb3\xb3\xa9}\xd8"
            b"\x00P\xaa\n91L@R\x8c\xae\xc9RV\xc2\x8c")
SM3_OUT = (b"\xfcx\xe0\xa9ez\x0ct\x8c\xe5\x15Y\x90<\xcf\x03"
           b"Q\x0eQ\xd3\xcf\xf22\xd7\x13C\xe8\x8a2\x1cS\x04")


def _enc_pb(data, l):
    data = list(data)
    xor_a = data[:8]
    for i in range(8, l):
        data[i] ^= xor_a[i % 8]
    return bytes(data[::-1])


def _body_hash(stub=None):
    sm3 = SM3()
    return sm3.hash(bytes(16))[:6] if not stub else sm3.hash(bytes.fromhex(stub))[:6]


def _query_hash(q=None):
    sm3 = SM3()
    return sm3.hash(bytes(16))[:6] if not q else sm3.hash(q.encode())[:6]


def argus_sign(query, stub=None, ts=None, aid=AID):
    if ts is None:
        ts = int(time.time())

    params = parse_qs(query)
    device_id = params.get("device_id", ["0"])[0]

    bean = {
        1: 0x20200929 << 1,
        2: 2,
        3: random.randint(0, 0x7FFFFFFF),
        4: str(aid),
        5: device_id,
        6: str(LICENSE_ID),
        7: params.get("app_version", [VERSION_NAME])[0],
        8: SDK_VER_STR,
        9: SDK_VER_INT,
        10: bytes(8),
        12: ts << 1,
        13: _body_hash(stub),
        14: _query_hash(query),
        16: "",
        20: "none",
        21: 738,
        25: 2,
    }

    protobuf = pad(pb_encode(bean), block_size)
    new_len = len(protobuf)
    key = SM3_OUT[:32]
    kl = []
    enc_pb = bytearray(new_len)

    for i in range(2):
        kl += list(unpack("<QQ", key[i * 16: i * 16 + 16]))

    for i in range(new_len // 16):
        pt = list(unpack("<QQ", protobuf[i * 16: i * 16 + 16]))
        ct = simon_enc(pt, kl)
        enc_pb[i * 16: i * 16 + 8] = ct[0].to_bytes(8, "little")
        enc_pb[i * 16 + 8: i * 16 + 16] = ct[1].to_bytes(8, "little")

    buf = _enc_pb(b"\xf2\xf7\xfc\xff\xf2\xf7\xfc\xff" + enc_pb, new_len + 8)
    buf = b"\xa6n\xad\x9fw\x01\xd0\x0c\x18" + buf + b"ao"
    cipher = aes_new(md5(SIGN_KEY[:16]).digest(), MODE_CBC, md5(SIGN_KEY[16:]).digest())

    return b64encode(b"\xf2\x81" + cipher.encrypt(pad(buf, block_size))).decode()


# ============================================================
# GORGON SIGNING
# ============================================================

def gorgon_sign(params, unix, data=None, cookies=None):
    def _h(s):
        return hashlib.md5(s.encode()).hexdigest()

    base = _h(params)
    base += _h(data) if data else "0" * 32
    base += _h(cookies) if cookies else "0" * 32

    KEY = [
        0xDF, 0x77, 0xB9, 0x40, 0xB9, 0x9B, 0x84, 0x83,
        0xD1, 0xB9, 0xCB, 0xD1, 0xF7, 0xC2, 0xB9, 0x85,
        0xC3, 0xD0, 0xFB, 0xC3,
    ]

    pl = []
    for i in range(0, 12, 4):
        t = base[8 * i: 8 * (i + 1)]
        for j in range(4):
            pl.append(int(t[j * 2: (j + 1) * 2], 16))
    pl.extend([0x0, 0x6, 0xB, 0x1C])
    H = int(unix)
    pl += [(H >> 24) & 0xFF, (H >> 16) & 0xFF, (H >> 8) & 0xFF, H & 0xFF]

    eor = [a ^ b for a, b in zip(pl, KEY)]

    for i in range(20):
        hs = hex(eor[i])[2:].zfill(2)
        C = int(hs[1:] + hs[:1], 16)
        D = eor[(i + 1) % 20]
        E = C ^ D
        bits = bin(E)[2:].zfill(8)
        F = int(bits[::-1], 2)
        eor[i] = ((F ^ 0xFFFFFFFF) ^ 20) & 0xFF

    result = "".join(hex(x)[2:].zfill(2) for x in eor)

    return {
        "x-ss-req-ticket": str(int(unix * 1000)),
        "x-khronos": str(int(unix)),
        "x-gorgon": f"0404b0d30000{result}",
    }


# ============================================================
# LADON SIGNING
# ============================================================

def _md5b(data):
    return hashlib.md5(data).hexdigest()


def _pad_size(s):
    m = s % 16
    return s + (16 - m) if m else s


def _pkcs7_pad(buf, dl, bs, mod):
    pb = mod - (dl % mod)
    if dl + pb > bs:
        return -pb
    for i in range(pb):
        buf[dl + i] = pb
    return pb


def __ROR64(val, cnt):
    cnt %= 64
    lo = ctypes.c_ulonglong(val.value << (64 - cnt)).value
    return ctypes.c_ulonglong(val.value >> cnt).value | lo


def _ladon_input(ht, inp):
    d0 = int.from_bytes(inp[:8], "little")
    d1 = int.from_bytes(inp[8:], "little")
    for i in range(0x22):
        h = int.from_bytes(ht[i * 8: (i + 1) * 8], "little")
        d1 = (h ^ (d0 + ((d1 >> 8) | (d1 << 56)))) & 0xFFFFFFFFFFFFFFFF
        d0 = (d1 ^ ((d0 >> 0x3D) | (d0 << 3))) & 0xFFFFFFFFFFFFFFFF
    out = bytearray(16)
    out[:8] = d0.to_bytes(8, "little")
    out[8:] = d1.to_bytes(8, "little")
    return bytes(out)


def _enc_ladon(md5hex, data, size):
    ht = bytearray(288)
    ht[:32] = md5hex
    temp = [int.from_bytes(ht[i * 8: (i + 1) * 8], "little") for i in range(4)]
    b0, b8 = temp[0], temp[1]
    temp = temp[2:]
    for i in range(0x22):
        x8 = __ROR64(ctypes.c_ulonglong(b8), 8) & 0xFFFFFFFFFFFFFFFF
        x8 = (x8 + b0) & 0xFFFFFFFFFFFFFFFF
        x8 ^= i
        temp.append(x8)
        x8r = (x8 ^ __ROR64(ctypes.c_ulonglong(b0), 61)) & 0xFFFFFFFFFFFFFFFF
        ht[(i + 1) * 8: (i + 2) * 8] = x8r.to_bytes(8, "little")
        b0 = x8r
        b8 = temp[0]
        temp.pop(0)
    ns = _pad_size(size)
    inp = bytearray(ns)
    inp[:size] = data
    _pkcs7_pad(inp, size, ns, 16)
    out = bytearray(ns)
    for i in range(ns // 16):
        out[i * 16: (i + 1) * 16] = _ladon_input(ht, inp[i * 16: (i + 1) * 16])
    return out


def ladon_encrypt(khronos, lc_id=LICENSE_ID, aid=AID):
    rb = urandom(4)
    data = f"{khronos}-{lc_id}-{aid}"
    keygen = rb + str(aid).encode()
    mh = _md5b(keygen)
    size = len(data)
    ns = _pad_size(size)
    out = bytearray(ns + 4)
    out[:4] = rb
    out[4:] = _enc_ladon(mh.encode(), data.encode(), size)
    return base64.b64encode(bytes(out)).decode()


# ============================================================
# COMBINED SIGN
# ============================================================

def tt_sign(params, payload=None, cookie=None, aid=AID):
    stub = hashlib.md5(payload.encode()).hexdigest() if payload else None
    unix = time.time()
    ts = int(unix)

    result = gorgon_sign(params, unix, payload, cookie)
    result["x-ladon"] = ladon_encrypt(ts, LICENSE_ID, aid)
    result["x-argus"] = argus_sign(params, stub, ts, aid)

    if payload:
        result["content-length"] = str(len(payload))
    if stub:
        result["x-ss-stub"] = stub.upper()

    return result


# ============================================================
# PUZZLE SOLVER (cv2 template matching)
# ============================================================

class PuzzleSolver:
    def __init__(self, b64_puzzle, b64_piece):
        self.puzzle = b64_puzzle
        self.piece = b64_piece

    def get_position(self):
        puzzle = self._sobel(self._decode(self.piece))
        piece = self._sobel(self._decode(self.puzzle))

        results = []
        for method in [cv2.TM_CCOEFF_NORMED, cv2.TM_CCORR_NORMED]:
            matched = cv2.matchTemplate(puzzle, piece, method)
            _, max_val, _, max_loc = cv2.minMaxLoc(matched)
            results.append((max_loc[0], max_val))

        # Edge detection pass
        pg = cv2.cvtColor(puzzle, cv2.COLOR_BGR2GRAY) if len(puzzle.shape) == 3 else puzzle
        cg = cv2.cvtColor(piece, cv2.COLOR_BGR2GRAY) if len(piece.shape) == 3 else piece
        ep = cv2.Canny(cv2.GaussianBlur(pg, (3, 3), 0), 50, 150)
        ec = cv2.Canny(cv2.GaussianBlur(cg, (3, 3), 0), 50, 150)
        matched = cv2.matchTemplate(ep, ec, cv2.TM_CCOEFF_NORMED)
        _, max_val, _, max_loc = cv2.minMaxLoc(matched)
        results.append((max_loc[0], max_val))

        results.sort(key=lambda x: x[1], reverse=True)
        return results[0][0]

    def _decode(self, b64):
        if isinstance(b64, str):
            b64 = b64.encode()
        arr = np.frombuffer(base64.b64decode(b64), dtype=np.uint8)
        img = cv2.imdecode(arr, cv2.IMREAD_UNCHANGED)
        if img is None:
            raise ValueError("image decode failed")
        if len(img.shape) == 2:
            img = cv2.cvtColor(img, cv2.COLOR_GRAY2BGR)
        elif img.shape[2] == 4:
            img = cv2.cvtColor(img, cv2.COLOR_RGBA2BGR)
        return img

    def _sobel(self, img):
        gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY) if len(img.shape) == 3 else img
        gray = cv2.GaussianBlur(gray, (3, 3), 0)
        gx = cv2.convertScaleAbs(cv2.Sobel(gray, cv2.CV_16S, 1, 0, ksize=3))
        gy = cv2.convertScaleAbs(cv2.Sobel(gray, cv2.CV_16S, 0, 1, ksize=3))
        return cv2.addWeighted(gx, 0.5, gy, 0.5, 0)


# ============================================================
# PROXY
# ============================================================

def build_proxy(country, user=PROXY_USER, pwd=PROXY_PASS, session_id=None):
    if not session_id:
        session_id = "".join(random.choices(string.ascii_lowercase + string.digits, k=10))
    auth = (f"{user}:{pwd}_country-{country.lower()}"
            f"_streaming-1_session-{session_id}_lifetime-30m")
    url = f"http://{auth}@{PROXY_HOST}:{PROXY_PORT}"
    return {"http": url, "https": url}, session_id


def parse_custom_proxy(proxy_str):
    """Accept user:pass@host:port or host:port:user:pass"""
    if "@" in proxy_str:
        url = f"http://{proxy_str}"
    else:
        parts = proxy_str.split(":")
        if len(parts) == 4:
            host, port, user, pwd = parts
            url = f"http://{user}:{pwd}@{host}:{port}"
        else:
            url = f"http://{proxy_str}"
    return {"http": url, "https": url}


def test_proxy(proxy_dict):
    try:
        r = requests.get("http://ip-api.com/json/", proxies=proxy_dict,
                         timeout=15, verify=False)
        d = r.json()
        log.info(f"Proxy OK: {d.get('query')} ({d.get('countryCode')}, {d.get('city')})")
        return True
    except Exception as e:
        log.error(f"Proxy DEAD: {e}")
        return False


# ============================================================
# TIKTOK CLIENT
# ============================================================

class TikTokClient:
    def __init__(self, region, proxy_dict=None):
        self.region = region.lower()
        self.prof = REGIONS.get(self.region, REGIONS["us"])

        self.session = requests.Session()
        if proxy_dict:
            self.session.proxies = proxy_dict
        self.session.verify = False

        self.did = None
        self.iid = None
        self.openudid = hashlib.md5(uuid.uuid4().bytes).hexdigest()[:16]
        self.cdid = str(uuid.uuid4())
        self.ms_token = None
        self.verify_fp = None

        self.ua = (
            f"com.zhiliaoapp.musically/{MANIFEST_VERSION} "
            f"(Linux; U; Android {OS_VERSION}; "
            f"{self.prof['lang']}_{self.region.upper()}; "
            f"{DEVICE_TYPE}; Build/TP1A; tt-ok/3.12.13.4-tiktok)"
        )

    # -------------------- DEVICE REGISTRATION --------------------

    def register_device(self):
        log.info("Registering device...")
        url = f"https://{REGISTER_HOST}/service/2/device_register/"

        body = {
            "magic_tag": "ss_app_log",
            "header": {
                "display_name": "TikTok",
                "update_version_code": int(MANIFEST_VERSION),
                "manifest_version_code": int(MANIFEST_VERSION),
                "app_version_minor": "",
                "aid": AID,
                "channel": CHANNEL,
                "package": "com.zhiliaoapp.musically",
                "app_version": VERSION_NAME,
                "version_code": int(VERSION_CODE),
                "sdk_version": "2.3.4.i18n",
                "os": "Android",
                "os_version": OS_VERSION,
                "os_api": OS_API,
                "device_model": DEVICE_TYPE,
                "device_brand": DEVICE_BRAND,
                "device_manufacturer": DEVICE_BRAND,
                "cpu_abi": HOST_ABI,
                "release_build": "1",
                "density_dpi": int(DPI),
                "display_density": "mdpi",
                "resolution": RESOLUTION,
                "language": self.prof["lang"],
                "timezone": int(self.prof["tz_off"]) // 3600,
                "access": "wifi",
                "not_request_sender": 0,
                "cdid": self.cdid,
                "sig_hash": "194326e82c84a639a52e5c023116f12a",
                "openudid": self.openudid,
                "clientudid": str(uuid.uuid4()),
                "region": self.region.upper(),
                "tz_name": self.prof["tz"],
                "tz_offset": int(self.prof["tz_off"]),
                "sim_region": self.prof["carrier"].lower(),
                "carrier_region": self.prof["carrier"],
                "mcc_mnc": self.prof["mcc"],
            },
        }

        params = {
            "aid": str(AID), "app_name": APP_NAME,
            "version_code": VERSION_CODE,
            "device_platform": "android",
            "device_type": DEVICE_TYPE,
            "os_version": OS_VERSION,
        }

        headers = {
            "User-Agent": self.ua,
            "Content-Type": "application/json; charset=utf-8",
            "Accept-Encoding": "gzip",
        }

        try:
            resp = self.session.post(url, params=params, json=body,
                                     headers=headers, timeout=15)
            data = resp.json()
            did = data.get("device_id") or data.get("device_id_str")
            iid = data.get("install_id") or data.get("install_id_str")
            if did and iid:
                self.did, self.iid = str(did), str(iid)
                self._cookies()
                log.info(f"Device OK: did={self.did} iid={self.iid}")
                return True
            log.error(f"Register failed: {json.dumps(data)[:300]}")
            return False
        except Exception as e:
            log.error(f"Register error: {e}")
            return False

    # -------------------- WARMUP --------------------

    def warmup(self):
        log.info("Warming device...")
        bp = self._params()

        for ep in ["/aweme/v1/app_alert_check/"]:
            self._signed_get(ep, bp)
            time.sleep(random.uniform(*WARMUP_DELAY))

        # Feed
        fp = {**bp, "count": "6", "type": "0", "max_cursor": "0", "pull_type": "1"}
        self._signed_get("/aweme/v1/feed/", fp)
        time.sleep(random.uniform(*REQUEST_DELAY))

    # -------------------- SEND CODE --------------------

    def send_code(self, phone, sms_type=33):
        area = detect_area(phone)
        log.info(f"send_code: {phone} area={area} type={sms_type}")

        bp = self._params()
        query = urlencode(bp)

        body_d = {
            "phone_number": phone,
            "area": area,
            "country_code": area,
            "type": str(sms_type),
            "aid": str(AID),
            "account_sdk_source": "app",
            "mix_mode": "1",
            "multi_login": "1",
        }
        body = urlencode(body_d)
        sig = tt_sign(query, body)

        headers = {
            "User-Agent": self.ua,
            "Accept-Encoding": "gzip",
            "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
            "X-Tt-Store-Region": self.region,
            "X-Tt-Store-Region-Src": "did",
        }
        headers.update(sig)

        url = f"https://{API_HOST}/passport/mobile/send_code/v1/?{query}"

        try:
            resp = self.session.post(url, data=body, headers=headers, timeout=15)
            self._cookies()

            if resp.status_code == 200 and len(resp.content) == 0:
                log.warning("EMPTY RESPONSE — device flagged")
                return {"ok": False, "ec": -1, "msg": "empty_response", "captcha": False}

            data = resp.json()
            ec = data.get("data", {}).get("error_code", data.get("error_code", -1))
            msg = data.get("data", {}).get("description", data.get("message", ""))
            log.info(f"send_code result: ec={ec} msg={msg}")

            if ec == 0:
                return {"ok": True, "ec": 0, "msg": msg, "captcha": False, "raw": data}

            if ec in (1105, 1107):
                conf = data.get("data", {}).get("captcha", data.get("captcha", {}))
                return {"ok": False, "ec": ec, "msg": msg, "captcha": True, "conf": conf}

            if ec == 7:
                return {"ok": False, "ec": 7, "msg": "rate_limit", "captcha": False}

            return {"ok": False, "ec": ec, "msg": msg, "captcha": False, "raw": data}

        except Exception as e:
            log.error(f"send_code error: {e}")
            return {"ok": False, "ec": -1, "msg": str(e), "captcha": False}

    # -------------------- CAPTCHA --------------------

    def solve_captcha(self, conf=None):
        """
        Handle all captcha types:
        - hcaptcha auto-pass (code=200, success)
        - slide puzzle (cv2 local solve + signed verify)
        - 3d shapes (JustScrape API fallback)
        """
        log.info("Handling captcha...")

        detail = conf.get("detail", "") if conf else ""
        server_sdk_env = conf.get("server_sdk_env", "") if conf else ""

        for attempt in range(MAX_CAPTCHA_RETRIES):
            log.info(f"Captcha attempt {attempt + 1}/{MAX_CAPTCHA_RETRIES}")

            challenge = self._captcha_get(detail, server_sdk_env)
            if not challenge:
                time.sleep(2)
                continue

            code = challenge.get("code", 0)
            msg_sub = challenge.get("msg_sub_code", "")
            message = challenge.get("message", "")

            log.info(f"captcha/get: code={code} msg_sub={msg_sub} message={message}")

            # ---- AUTO-PASS ----
            if code == 200 and msg_sub == "success":
                log.info("Captcha auto-passed!")
                return True

            cdata = challenge.get("data", {})
            challenges = cdata.get("challenges", [])

            if not challenges:
                if code == 200:
                    log.info("No challenges but code=200 — passed")
                    return True
                log.error("No challenges in response")
                log.debug(f"Response: {json.dumps(challenge)[:500]}")
                time.sleep(2)
                continue

            ch = challenges[0]
            mode = ch.get("mode", "")
            captcha_id = ch.get("id", "")
            verify_id = cdata.get("verify_id", "")
            q = ch.get("question", {})

            log.info(f"Captcha mode={mode} id={captcha_id[:30]}")

            # ---- HCAPTCHA ----
            if mode == "hcaptcha":
                if captcha_id == "abc" or code == 200 or msg_sub == "success":
                    log.info("hcaptcha auto-passed (placeholder)")
                    return True
                api_key = q.get("apiKey", "")
                log.warning(f"Real hcaptcha required, apiKey={api_key[:30]}")
                log.warning("Cannot solve real hcaptcha locally")
                return False

            # ---- 3D SHAPES ----
            if mode == "3d":
                log.info("3D captcha detected, trying JustScrape solver...")
                return self._solve_3d_via_api(ch, cdata, detail, server_sdk_env)

            # ---- SLIDE PUZZLE ----
            url1 = q.get("url1", "")
            url2 = q.get("url2", "")

            if not url1 or not url2:
                if code == 200:
                    log.info("No images but code=200 — passed")
                    return True
                log.error(f"Missing images for mode={mode}")
                log.debug(f"Question: {json.dumps(q)[:300]}")
                time.sleep(2)
                continue

            log.info("Slide captcha, downloading images...")

            try:
                puzzle_img = self.session.get(url1, timeout=10).content
                piece_img = self.session.get(url2, timeout=10).content
                log.info(f"Images: puzzle={len(puzzle_img)}b piece={len(piece_img)}b")
            except Exception as e:
                log.error(f"Image download failed: {e}")
                time.sleep(2)
                continue

            solver = PuzzleSolver(
                base64.b64encode(puzzle_img),
                base64.b64encode(piece_img),
            )
            pos = solver.get_position()
            log.info(f"Slide position: {pos}")

            tip_y = q.get("tip_y", 140)
            n = random.randint(50, 100)
            moves = []
            for i in range(n):
                pr = (i + 1) / n
                yo = random.randint(-2, 2) if 0 < i < n - 1 else 0
                moves.append({
                    "relative_time": i * n + random.randint(-5, 5),
                    "x": round(pos * pr),
                    "y": tip_y + yo,
                })

            vfy_payload = {
                "modified_img_width": 552,
                "id": captcha_id,
                "mode": "slide",
                "reply": moves,
                "verify_id": verify_id,
            }

            result = self._captcha_verify(vfy_payload, detail, server_sdk_env)

            if self._check_verify_result(result):
                log.info("Slide captcha SOLVED!")
                return True

            log.warning(f"Slide verify failed, retrying...")
            time.sleep(random.uniform(2, 4))

        log.error("All captcha attempts exhausted")
        return False

    def _solve_3d_via_api(self, ch, cdata, detail, server_sdk_env):
        """Fallback: solve 3D captcha via JustScrape API"""
        q = ch.get("question", {})
        url1 = q.get("url1", "")

        if not url1:
            log.error("No image URL for 3D captcha")
            return False

        try:
            img = self.session.get(url1, timeout=10).content
            img_b64 = base64.b64encode(img).decode()
        except Exception as e:
            log.error(f"3D image download failed: {e}")
            return False

        # Solve via JustScrape
        log.info("Sending to JustScrape /captcha/3d...")
        try:
            resp = requests.post(
                f"{CAPTCHA_API_HOST}/captcha/3d",
                json={"image_base64": img_b64, "modified_img_width": 348},
                headers={"x-api-key": CAPTCHA_API_KEY},
                timeout=30,
            )
            solution = resp.json()
            log.info(f"3D solver: {solution}")
        except Exception as e:
            log.error(f"3D solver error: {e}")
            return False

        # E2E verify via JustScrape
        log.info("Trying JustScrape e2e verify...")
        try:
            sdk_env = server_sdk_env or json.dumps(
                {"idc": "useast2b", "region": "I18N", "server_type": "passport"})

            resp = requests.post(
                f"{CAPTCHA_API_HOST}/captcha/verify",
                json={
                    "device_id": self.did or "0",
                    "iid": "0",
                    "detail": detail,
                    "region": self.region,
                    "server_sdk_env": sdk_env,
                    "verify_fp": self.verify_fp or "",
                    "ms_token": self.ms_token or "",
                },
                headers={"x-api-key": CAPTCHA_API_KEY},
                timeout=60,
            )
            data = resp.json()
            log.info(f"E2E verify: {data}")
            return data.get("status") in ("success", "info")
        except Exception as e:
            log.error(f"E2E verify error: {e}")
            return False

    def _captcha_get(self, detail="", server_sdk_env=""):
        params = self._captcha_params(detail, server_sdk_env)
        sig = tt_sign(params, "")

        headers = self._captcha_headers()
        headers.update(sig)

        try:
            resp = self.session.get(
                f"https://{CAPTCHA_TT_HOST}/captcha/get?{params}",
                headers=headers, timeout=15,
            )
            self._cookies()
            data = resp.json()
            log.debug(f"captcha/get raw: {json.dumps(data)[:500]}")
            return data
        except Exception as e:
            log.error(f"captcha/get error: {e}")
            return None

    def _captcha_verify(self, payload, detail="", server_sdk_env=""):
        params = self._captcha_params(detail, server_sdk_env)
        body_str = json.dumps(payload)
        sig = tt_sign(params, body_str)

        headers = self._captcha_headers()
        headers.update(sig)

        try:
            resp = self.session.post(
                f"https://{CAPTCHA_TT_HOST}/captcha/verify?{params}",
                headers=headers, json=payload, timeout=15,
            )
            self._cookies()
            log.info(f"captcha/verify: {resp.status_code} {resp.text[:300]}")
            return resp.text
        except Exception as e:
            log.error(f"captcha/verify error: {e}")
            return None

    def _check_verify_result(self, result):
        if not result:
            return False
        try:
            rd = json.loads(result) if isinstance(result, str) else result
            if rd.get("code") == 200:
                return True
            if rd.get("msg_sub_code") == "success":
                return True
        except:
            pass
        return "success" in str(result).lower()

    def _captcha_params(self, detail="", server_sdk_env=""):
        if not server_sdk_env:
            server_sdk_env = quote(json.dumps(
                {"idc": "useast2b", "region": "I18N", "server_type": "passport"}
            ), safe="")

        return (
            f"lang={self.prof['lang']}"
            f"&app_name={APP_NAME}"
            f"&h5_sdk_version=2.33.7&h5_sdk_use_type=cdn&sdk_version=2.3.4.i18n"
            f"&iid={self.iid}&did={self.did}&device_id={self.did}"
            f"&ch={CHANNEL}&aid={AID}&os_type=0&mode=slide"
            f"&tmp={int(time.time())}{random.randint(111, 999)}"
            f"&platform=app&webdriver=undefined"
            f"&verify_host=https%3A%2F%2F{CAPTCHA_TT_HOST}%2F"
            f"&locale={self.prof['locale']}&channel={CHANNEL}&app_key"
            f"&vc={VERSION_CODE}&app_version={VERSION_NAME}"
            f"&session_id&region=i18n"
            f"&use_native_report=1&use_jsb_request=1"
            f"&orientation=2&resolution=720*1280"
            f"&os_version={OS_VERSION}&device_brand={DEVICE_BRAND}"
            f"&device_model={DEVICE_TYPE}&os_name=Android"
            f"&version_code={VERSION_CODE}&device_type={DEVICE_TYPE}"
            f"&device_platform=Android&type=verify"
            f"&detail={detail}"
            f"&server_sdk_env={server_sdk_env}"
            f"&imagex_domain"
            f"&subtype=slide&challenge_code=99996"
            f"&triggered_region=i18n"
        )

    def _captcha_headers(self):
        return {
            "X-Tt-Request-Tag": "n=1;t=0",
            "X-Vc-Bdturing-Sdk-Version": "2.3.4.i18n",
            "X-Tt-Bypass-Dp": "1",
            "Content-Type": "application/json; charset=utf-8",
            "X-Tt-Dm-Status": "login=0;ct=0;rt=7",
            "X-Tt-Store-Region": self.region,
            "X-Tt-Store-Region-Src": "did",
            "User-Agent": self.ua,
        }

    # -------------------- FULL PIPELINE --------------------

    def run(self, phone, sms_type=33, warm=True):
        log.info("=" * 50)
        log.info(f"Pipeline: {phone} | region={self.region} | type={sms_type}")
        log.info("=" * 50)

        # Step 1: Register
        if not self.register_device():
            return {"ok": False, "ec": -1, "error": "register_failed"}

        time.sleep(random.uniform(*REQUEST_DELAY))

        # Step 2: Warmup
        if warm:
            self.warmup()
            time.sleep(random.uniform(*REQUEST_DELAY))

        # Step 3: send_code (may need multiple attempts with captcha)
        for send_attempt in range(MAX_SEND_RETRIES):
            result = self.send_code(phone, sms_type)

            # Success
            if result["ok"]:
                log.info("=" * 50)
                log.info("SMS SENT!")
                log.info("=" * 50)
                return result

            # Captcha required
            if result.get("captcha"):
                log.info("Captcha required, solving...")
                conf = result.get("conf", {})
                solved = self.solve_captcha(conf)

                if solved:
                    log.info("Captcha solved, retrying send_code...")
                    time.sleep(random.uniform(*POST_CAPTCHA_DELAY))
                    continue  # retry send_code
                else:
                    log.error("Captcha solve failed")
                    return {"ok": False, "ec": result["ec"],
                            "error": "captcha_failed", "msg": result.get("msg", "")}

            # Rate limit or other error — no point retrying
            if result.get("ec") == 7:
                log.warning("Rate limited — need new proxy + device")
                return result

            if result.get("ec") == -1 and result.get("msg") == "empty_response":
                log.warning("Empty response — device flagged, need new device")
                return result

            # Unknown error
            log.warning(f"Unknown error ec={result.get('ec')}, not retrying")
            return result

        log.error("Max send retries exhausted")
        return {"ok": False, "ec": -1, "error": "max_retries"}

    # -------------------- HELPERS --------------------

    def _params(self):
        ts = str(int(time.time()))
        return {
            "passport-sdk-version": "25",
            "iid": self.iid or "0",
            "device_id": self.did or "0",
            "ac": "wifi",
            "channel": CHANNEL,
            "aid": str(AID),
            "app_name": APP_NAME,
            "version_code": VERSION_CODE,
            "version_name": VERSION_NAME,
            "device_platform": "android",
            "os": "android",
            "ab_version": VERSION_NAME,
            "ssmix": "a",
            "device_type": DEVICE_TYPE,
            "device_brand": DEVICE_BRAND,
            "language": self.prof["lang"],
            "os_api": OS_API,
            "os_version": OS_VERSION,
            "openudid": self.openudid,
            "manifest_version_code": MANIFEST_VERSION,
            "resolution": RESOLUTION,
            "dpi": DPI,
            "update_version_code": MANIFEST_VERSION,
            "_rticket": str(int(time.time() * 1000)),
            "is_pad": "0",
            "current_region": self.region.upper(),
            "app_type": "normal",
            "sys_region": self.prof["carrier"],
            "mcc_mnc": self.prof["mcc"],
            "timezone_name": self.prof["tz"],
            "residence": self.region.upper(),
            "app_language": self.prof["lang"],
            "carrier_region": self.prof["carrier"],
            "ac2": "wifi",
            "uoo": "0",
            "op_region": self.region.upper(),
            "timezone_offset": self.prof["tz_off"],
            "build_number": BUILD_NUMBER,
            "host_abi": HOST_ABI,
            "locale": self.prof["locale"],
            "region": self.region.upper(),
            "ts": ts,
            "cdid": self.cdid,
            "app_version": VERSION_NAME,
        }

    def _signed_get(self, ep, params):
        query = urlencode(params)
        sig = tt_sign(query)
        headers = {"User-Agent": self.ua, "Accept-Encoding": "gzip"}
        headers.update(sig)
        try:
            r = self.session.get(f"https://{API_HOST}{ep}", params=params,
                                 headers=headers, timeout=10)
            self._cookies()
            log.info(f"warmup {ep}: {r.status_code}")
        except Exception as e:
            log.debug(f"warmup {ep}: {e}")

    def _cookies(self):
        for c in self.session.cookies:
            if c.name == "msToken":
                self.ms_token = c.value
            elif c.name == "verify_fp":
                self.verify_fp = c.value


# ============================================================
# BATCH RUNNER
# ============================================================

def run_batch(numbers, sms_type=33, proxy_user=PROXY_USER,
              proxy_pass=PROXY_PASS, warm=True):
    results = []
    session_count = 0
    proxy_dict = None

    for i, (phone, country) in enumerate(numbers):
        # Rotate proxy when needed
        if session_count >= MAX_PER_SESSION or proxy_dict is None:
            proxy_dict, sid = build_proxy(country, proxy_user, proxy_pass)
            session_count = 0
            log.info(f"New proxy session: {sid}")

            if not test_proxy(proxy_dict):
                log.error("Proxy dead, skipping number")
                results.append({"phone": phone, "ok": False, "error": "proxy_dead"})
                proxy_dict = None  # force re-rotate next iteration
                continue

        # Fresh client for each number (new device)
        client = TikTokClient(country, proxy_dict)
        result = client.run(phone, sms_type, warm=warm)
        results.append({"phone": phone, **result})
        session_count += 1

        # Force rotation on rate limit, empty response, or captcha fail
        if result.get("ec") in (7, -1):
            session_count = MAX_PER_SESSION
            proxy_dict = None

        if i < len(numbers) - 1:
            time.sleep(random.uniform(3, 8))

    # Summary
    log.info("")
    log.info("=" * 50)
    log.info("BATCH RESULTS")
    log.info("=" * 50)
    ok = sum(1 for r in results if r.get("ok"))
    log.info(f"Success: {ok}/{len(results)}")
    for r in results:
        status = "OK" if r.get("ok") else f"FAIL(ec={r.get('ec', '?')})"
        log.info(f"  {r['phone']}: {status} {r.get('msg', r.get('error', ''))}")
    log.info("=" * 50)

    return results


# ============================================================
# CLI
# ============================================================

def main():
    parser = argparse.ArgumentParser(
        description="TikTok SMS v7.0 — Direct Pipeline",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s +5588951570521
  %(prog)s +5588951570521 --region br --type 33
  %(prog)s +5588951570521 --no-proxy
  %(prog)s +5588951570521 --proxy user:pass@host:port
  %(prog)s +5588951570521 --batch +18304034231 +18194146343
  %(prog)s --test-proxy --region br
  %(prog)s +5588951570521 --no-warm -v
        """,
    )
    parser.add_argument("phone", nargs="?", default=None, help="Phone (+55...)")
    parser.add_argument("--region", default=None, help="br/us/ca/it/de/ae")
    parser.add_argument("--type", type=int, default=33,
                        help="2=recovery 9=register 33=login (default: 33)")
    parser.add_argument("--no-warm", action="store_true", help="Skip warmup")
    parser.add_argument("--no-proxy", action="store_true", help="Use local IP")
    parser.add_argument("--proxy-user", default=PROXY_USER)
    parser.add_argument("--proxy-pass", default=PROXY_PASS)
    parser.add_argument("--proxy", default=None, help="Custom proxy user:pass@host:port")
    parser.add_argument("--batch", nargs="+", help="Additional phones for batch")
    parser.add_argument("--test-proxy", action="store_true", help="Test proxy and exit")
    parser.add_argument("-v", "--verbose", action="store_true", help="Debug logging")

    args = parser.parse_args()

    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    # ---- Test proxy mode ----
    if args.test_proxy:
        region = args.region or "br"
        if args.proxy:
            pd = parse_custom_proxy(args.proxy)
        else:
            pd, _ = build_proxy(region, args.proxy_user, args.proxy_pass)
        test_proxy(pd)
        return

    # ---- Need phone ----
    if not args.phone and not args.batch:
        parser.print_help()
        return

    # ---- Batch mode ----
    if args.batch:
        phones = []
        if args.phone:
            phones.append((args.phone, args.region or detect_country(args.phone)))
        for ph in args.batch:
            phones.append((ph, detect_country(ph)))
        run_batch(phones, args.type, args.proxy_user, args.proxy_pass,
                  warm=not args.no_warm)
        return

    # ---- Single mode ----
    phone = args.phone
    region = args.region or detect_country(phone)

    # Build proxy
    if args.no_proxy:
        proxy_dict = None
        log.info("Running without proxy (local IP)")
    elif args.proxy:
        proxy_dict = parse_custom_proxy(args.proxy)
        log.info(f"Custom proxy: {args.proxy}")
        if not test_proxy(proxy_dict):
            log.error("Proxy dead")
            sys.exit(1)
    else:
        proxy_dict, sid = build_proxy(region, args.proxy_user, args.proxy_pass)
        log.info(f"IPRoyal session: {sid}")
        if not test_proxy(proxy_dict):
            log.error("Proxy dead. Use --no-proxy or --proxy or fix credentials.")
            sys.exit(1)

    # Run pipeline
    client = TikTokClient(region, proxy_dict)
    result = client.run(phone, args.type, warm=not args.no_warm)

    # Output
    print()
    print(json.dumps(result, indent=2, ensure_ascii=False))

    sys.exit(0 if result.get("ok") else 1)


if __name__ == "__main__":
    main()
