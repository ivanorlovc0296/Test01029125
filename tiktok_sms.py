"""
TikTok SMS v10.0 — Direct Pipeline (complete)

Pipeline:
  1. Device register
  2. Warmup
  3. send_code (Argus/Gorgon/Ladon)
  4. Captcha: parse detail from verify_center_decision_conf
  5. captcha/get with detail -> 3D challenge
  6. Solve 3D via JustScrape API
  7. captcha/verify with signed request
  8. Retry send_code

pip install requests pycryptodome opencv-python numpy
"""

import time as time_module
import string
import random
import secrets
import base64
import requests
import json
import hashlib
import uuid
import ctypes
import logging
import argparse
import sys
import traceback
from enum import IntEnum, unique
from random import randint
from time import time
from struct import unpack
from base64 import b64encode
from hashlib import md5
from urllib.parse import urlencode, parse_qs, quote
from os import urandom

import cv2
import numpy as np
from Crypto.Cipher.AES import new as aes_new, MODE_CBC, block_size
from Crypto.Util.Padding import pad

import urllib3
urllib3.disable_warnings()

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
MAX_SEND_RETRIES = 3
MAX_PER_SESSION = 3

WARMUP_DELAY = (2.0, 4.0)
REQUEST_DELAY = (1.5, 3.0)
POST_CAPTCHA_DELAY = (2.0, 4.0)


# ============================================================
# REGIONS
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
    "971": "ae", "44": "gb", "33": "fr", "34": "es",
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
    def __init__(self) -> None:
        self.IV = [
            1937774191, 1226093241, 388252375, 3666478592,
            2842636476, 372324522, 3817729613, 2969243214
        ]
        self.TJ = [
            2043430169, 2043430169, 2043430169, 2043430169,
            2043430169, 2043430169, 2043430169, 2043430169,
            2043430169, 2043430169, 2043430169, 2043430169,
            2043430169, 2043430169, 2043430169, 2043430169,
            2055708042, 2055708042, 2055708042, 2055708042,
            2055708042, 2055708042, 2055708042, 2055708042,
            2055708042, 2055708042, 2055708042, 2055708042,
            2055708042, 2055708042, 2055708042, 2055708042,
            2055708042, 2055708042, 2055708042, 2055708042,
            2055708042, 2055708042, 2055708042, 2055708042,
            2055708042, 2055708042, 2055708042, 2055708042,
            2055708042, 2055708042, 2055708042, 2055708042,
            2055708042, 2055708042, 2055708042, 2055708042,
            2055708042, 2055708042, 2055708042, 2055708042,
            2055708042, 2055708042, 2055708042, 2055708042,
            2055708042, 2055708042, 2055708042, 2055708042,
        ]

    def __rotate_left(self, a: int, k: int) -> int:
        k = k % 32
        return ((a << k) & 0xFFFFFFFF) | ((a & 0xFFFFFFFF) >> (32 - k))

    def __FFJ(self, X: int, Y: int, Z: int, j: int) -> int:
        if 0 <= j and j < 16:
            ret = X ^ Y ^ Z
        elif 16 <= j and j < 64:
            ret = (X & Y) | (X & Z) | (Y & Z)
        return ret

    def __GGJ(self, X: int, Y: int, Z: int, j: int) -> int:
        if 0 <= j and j < 16:
            ret = X ^ Y ^ Z
        elif 16 <= j and j < 64:
            ret = (X & Y) | ((~X) & Z)
        return ret

    def __P_0(self, X: int) -> int:
        return X ^ (self.__rotate_left(X, 9)) ^ (self.__rotate_left(X, 17))

    def __P_1(self, X: int) -> int:
        return X ^ (self.__rotate_left(X, 15)) ^ (self.__rotate_left(X, 23))

    def __CF(self, V_i: list, B_i: bytearray) -> list:
        W = []
        for i in range(16):
            weight = 0x1000000
            data = 0
            for k in range(i * 4, (i + 1) * 4):
                data = data + B_i[k] * weight
                weight = int(weight / 0x100)
            W.append(data)
        for j in range(16, 68):
            W.append(0)
            W[j] = (
                self.__P_1(W[j - 16] ^ W[j - 9] ^ (self.__rotate_left(W[j - 3], 15)))
                ^ (self.__rotate_left(W[j - 13], 7))
                ^ W[j - 6]
            )
        W_1 = []
        for j in range(0, 64):
            W_1.append(0)
            W_1[j] = W[j] ^ W[j + 4]
        A, B, C, D, E, F, G, H = V_i
        for j in range(0, 64):
            SS1 = self.__rotate_left(
                ((self.__rotate_left(A, 12)) + E + (self.__rotate_left(self.TJ[j], j)))
                & 0xFFFFFFFF, 7)
            SS2 = SS1 ^ (self.__rotate_left(A, 12))
            TT1 = (self.__FFJ(A, B, C, j) + D + SS2 + W_1[j]) & 0xFFFFFFFF
            TT2 = (self.__GGJ(E, F, G, j) + H + SS1 + W[j]) & 0xFFFFFFFF
            D = C
            C = self.__rotate_left(B, 9)
            B = A
            A = TT1
            H = G
            G = self.__rotate_left(F, 19)
            F = E
            E = self.__P_0(TT2)
        return [
            A & 0xFFFFFFFF ^ V_i[0], B & 0xFFFFFFFF ^ V_i[1],
            C & 0xFFFFFFFF ^ V_i[2], D & 0xFFFFFFFF ^ V_i[3],
            E & 0xFFFFFFFF ^ V_i[4], F & 0xFFFFFFFF ^ V_i[5],
            G & 0xFFFFFFFF ^ V_i[6], H & 0xFFFFFFFF ^ V_i[7],
        ]

    def sm3_hash(self, msg: bytes) -> bytes:
        msg = bytearray(msg)
        len1 = len(msg)
        reserve1 = len1 % 64
        msg.append(0x80)
        reserve1 = reserve1 + 1
        range_end = 56
        if reserve1 > range_end:
            range_end += 64
        for i in range(reserve1, range_end):
            msg.append(0x00)
        bit_length = (len1) * 8
        bit_length_str = [bit_length % 0x100]
        for i in range(7):
            bit_length = int(bit_length / 0x100)
            bit_length_str.append(bit_length % 0x100)
        for i in range(8):
            msg.append(bit_length_str[7 - i])
        group_count = round(len(msg) / 64)
        B = []
        for i in range(0, group_count):
            B.append(msg[i * 64 : (i + 1) * 64])
        V = []
        V.append(self.IV)
        for i in range(0, group_count):
            V.append(self.__CF(V[i], B[i]))
        y = V[i + 1]
        res = b""
        for i in y:
            res += int(i).to_bytes(4, "big")
        return res


# ============================================================
# SIMON CIPHER
# ============================================================

from ctypes import c_ulonglong


def get_bit(val, pos):
    return 1 if val & (1 << pos) else 0


def rotate_left(v, n):
    r = (v << n) | (v >> (64 - n))
    return r & 0xffffffffffffffff


def rotate_right(v, n):
    r = (v << (64 - n)) | (v >> n)
    return r & 0xffffffffffffffff


def key_expansion(key):
    tmp = 0
    for i in range(4, 72):
        tmp = rotate_right(key[i - 1], 3)
        tmp = tmp ^ key[i - 3]
        tmp = tmp ^ rotate_right(tmp, 1)
        key[i] = c_ulonglong(~key[i - 4]).value ^ tmp ^ get_bit(0x3DC94C3A046D678B, (i - 4) % 62) ^ 3
    return key


def simon_dec(ct, k, c=0):
    tmp = 0
    f = 0
    key = [0] * 72
    key[0] = k[0]
    key[1] = k[1]
    key[2] = k[2]
    key[3] = k[3]
    key = key_expansion(key)
    x_i = ct[0]
    x_i1 = ct[1]
    for i in range(72 - 1, -1, -1):
        tmp = x_i
        f = rotate_left(x_i, 1) if c == 1 else rotate_left(x_i, 1) & rotate_left(x_i, 8)
        x_i = x_i1 ^ f ^ rotate_left(x_i, 2) ^ key[i]
        x_i1 = tmp
    pt = [x_i, x_i1]
    return pt


def simon_enc(pt, k, c=0):
    tmp = 0
    f = 0
    key = [0] * 72
    key[0] = k[0]
    key[1] = k[1]
    key[2] = k[2]
    key[3] = k[3]
    key = key_expansion(key)
    x_i = pt[0]
    x_i1 = pt[1]
    for i in range(72):
        tmp = x_i1
        f = rotate_left(x_i1, 1) if c == 1 else rotate_left(x_i1, 1) & rotate_left(x_i1, 8)
        x_i1 = x_i ^ f ^ rotate_left(x_i1, 2) ^ key[i]
        x_i = tmp
    ct = [x_i, x_i1]
    return ct


# ============================================================
# PROTOBUF
# ============================================================

class ProtoError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return repr(self.msg)


@unique
class ProtoFieldType(IntEnum):
    VARINT = 0
    INT64 = 1
    STRING = 2
    GROUPSTART = 3
    GROUPEND = 4
    INT32 = 5
    ERROR1 = 6
    ERROR2 = 7


class ProtoField:
    def __init__(self, idx, type, val):
        self.idx = idx
        self.type = type
        self.val = val

    def isAsciiStr(self):
        if (type(self.val) != bytes):
            return False
        for b in self.val:
            if b < 0x20 or b > 0x7e:
                return False
        return True


class ProtoReader:
    def __init__(self, data):
        self.data = data
        self.pos = 0

    def isRemain(self, length):
        return self.pos + length <= len(self.data)

    def read0(self):
        assert (self.isRemain(1))
        ret = self.data[self.pos]
        self.pos += 1
        return ret & 0xFF

    def read(self, length):
        assert (self.isRemain(length))
        ret = self.data[self.pos:self.pos + length]
        self.pos += length
        return ret

    def readInt32(self):
        return int.from_bytes(self.read(4), byteorder='little', signed=False)

    def readInt64(self):
        return int.from_bytes(self.read(8), byteorder='little', signed=False)

    def readVarint(self):
        vint = 0
        n = 0
        while True:
            byte = self.read0()
            vint |= ((byte & 0x7F) << (7 * n))
            if byte < 0x80:
                break
            n += 1
        return vint

    def readString(self):
        length = self.readVarint()
        return self.read(length)


class ProtoWriter:
    def __init__(self):
        self.data = bytearray()

    def write0(self, byte):
        self.data.append(byte & 0xFF)

    def write(self, bytes_data):
        self.data.extend(bytes_data)

    def writeInt32(self, int32):
        self.write(int32.to_bytes(4, byteorder='little', signed=False))

    def writeInt64(self, int64):
        self.write(int64.to_bytes(8, byteorder='little', signed=False))

    def writeVarint(self, vint):
        vint = vint & 0xFFFFFFFF
        while (vint > 0x80):
            self.write0((vint & 0x7F) | 0x80)
            vint >>= 7
        self.write0(vint & 0x7F)

    def writeString(self, bytes_data):
        self.writeVarint(len(bytes_data))
        self.write(bytes_data)

    def toBytes(self):
        return bytes(self.data)


class ProtoBuf:
    def __init__(self, data=None):
        self.fields = list()
        if data is not None:
            if type(data) == bytes and len(data) > 0:
                self.__parseBuf(data)
            elif type(data) == dict and len(data) > 0:
                self.__parseDict(data)

    def __parseBuf(self, bytes_data):
        reader = ProtoReader(bytes_data)
        while reader.isRemain(1):
            key = reader.readVarint()
            field_type = ProtoFieldType(key & 0x7)
            field_idx = key >> 3
            if field_idx == 0:
                break
            if field_type == ProtoFieldType.INT32:
                self.put(ProtoField(field_idx, field_type, reader.readInt32()))
            elif field_type == ProtoFieldType.INT64:
                self.put(ProtoField(field_idx, field_type, reader.readInt64()))
            elif field_type == ProtoFieldType.VARINT:
                self.put(ProtoField(field_idx, field_type, reader.readVarint()))
            elif field_type == ProtoFieldType.STRING:
                self.put(ProtoField(field_idx, field_type, reader.readString()))
            else:
                raise ProtoError('unexpected field type: %s' % field_type.name)

    def toBuf(self):
        writer = ProtoWriter()
        for field in self.fields:
            key = (field.idx << 3) | (field.type & 7)
            writer.writeVarint(key)
            if field.type == ProtoFieldType.INT32:
                writer.writeInt32(field.val)
            elif field.type == ProtoFieldType.INT64:
                writer.writeInt64(field.val)
            elif field.type == ProtoFieldType.VARINT:
                writer.writeVarint(field.val)
            elif field.type == ProtoFieldType.STRING:
                writer.writeString(field.val)
        return writer.toBytes()

    def get(self, idx):
        for field in self.fields:
            if field.idx == idx:
                return field
        return None

    def put(self, field):
        self.fields.append(field)

    def __parseDict(self, data):
        for k, v in data.items():
            if isinstance(v, int):
                self.put(ProtoField(k, ProtoFieldType.VARINT, v))
            elif isinstance(v, str):
                self.put(ProtoField(k, ProtoFieldType.STRING, v.encode('utf-8')))
            elif isinstance(v, bytes):
                self.put(ProtoField(k, ProtoFieldType.STRING, v))
            elif isinstance(v, dict):
                self.put(ProtoField(k, ProtoFieldType.STRING, ProtoBuf(v).toBuf()))


# ============================================================
# PKCS7 + padding
# ============================================================

def pkcs7_padding_pad_buffer(buffer, data_length, buffer_size, modulus):
    pad_byte = modulus - (data_length % modulus)
    if data_length + pad_byte > buffer_size:
        return -pad_byte
    for i in range(pad_byte):
        buffer[data_length + i] = pad_byte
    return pad_byte


def padding_size(size):
    mod = size % 16
    if mod > 0:
        return size + (16 - mod)
    return size


# ============================================================
# ARGUS
# ============================================================

class Argus:
    def encrypt_enc_pb(data, l):
        data = list(data)
        xor_array = data[:8]
        for i in range(8, l):
            data[i] ^= xor_array[i % 8]
        return bytes(data[::-1])

    @staticmethod
    def get_bodyhash(stub=None):
        return (SM3().sm3_hash(bytes(16))[0:6] if stub is None or len(stub) == 0
                else SM3().sm3_hash(bytes.fromhex(stub))[0:6])

    @staticmethod
    def get_queryhash(query=None):
        return (SM3().sm3_hash(bytes(16))[0:6] if query is None or len(query) == 0
                else SM3().sm3_hash(query.encode())[0:6])

    @staticmethod
    def encrypt(xargus_bean):
        protobuf = pad(bytes.fromhex(ProtoBuf(xargus_bean).toBuf().hex()), block_size)
        new_len = len(protobuf)
        sign_key = b'\xac\x1a\xda\xae\x95\xa7\xaf\x94\xa5\x11J\xb3\xb3\xa9}\xd8\x00P\xaa\n91L@R\x8c\xae\xc9RV\xc2\x8c'
        sm3_output = b'\xfcx\xe0\xa9ez\x0ct\x8c\xe5\x15Y\x90<\xcf\x03Q\x0eQ\xd3\xcf\xf22\xd7\x13C\xe8\x8a2\x1cS\x04'
        key = sm3_output[:32]
        key_list = []
        enc_pb = bytearray(new_len)
        for _ in range(2):
            key_list = key_list + list(unpack("<QQ", key[_ * 16 : _ * 16 + 16]))
        for _ in range(int(new_len / 16)):
            pt = list(unpack("<QQ", protobuf[_ * 16 : _ * 16 + 16]))
            ct = simon_enc(pt, key_list)
            enc_pb[_ * 16 : _ * 16 + 8] = ct[0].to_bytes(8, byteorder="little")
            enc_pb[_ * 16 + 8 : _ * 16 + 16] = ct[1].to_bytes(8, byteorder="little")
        b_buffer = Argus.encrypt_enc_pb((b"\xf2\xf7\xfc\xff\xf2\xf7\xfc\xff" + enc_pb), new_len + 8)
        b_buffer = b'\xa6n\xad\x9fw\x01\xd0\x0c\x18' + b_buffer + b'ao'
        cipher = aes_new(md5(sign_key[:16]).digest(), MODE_CBC, md5(sign_key[16:]).digest())
        return b64encode(b"\xf2\x81" + cipher.encrypt(pad(b_buffer, block_size))).decode()

    @staticmethod
    def get_sign(queryhash=None, data=None, timestamp=None,
                 aid=1233, license_id=1611921764, platform=0,
                 sec_device_id="", sdk_version="v04.04.05-ov-android",
                 sdk_version_int=134744640):
        if timestamp is None:
            timestamp = int(time())
        params_dict = parse_qs(queryhash)
        p = params_dict.get('app_version', [VERSION_NAME])[0].split('.')
        return Argus.encrypt({
            1: 0x20200929 << 1, 2: 2, 3: randint(0, 0x7FFFFFFF),
            4: str(aid), 5: params_dict.get('device_id', ['0'])[0],
            6: str(license_id),
            7: params_dict.get('app_version', [VERSION_NAME])[0],
            8: sdk_version, 9: sdk_version_int, 10: bytes(8),
            12: (timestamp << 1),
            13: Argus.get_bodyhash(data), 14: Argus.get_queryhash(queryhash),
            16: sec_device_id, 20: "none", 21: 738, 25: 2
        })


# ============================================================
# GORGON
# ============================================================

class Gorgon:
    def __init__(self, params, unix, data=None, cookies=None):
        self.unix = unix
        self.params = params
        self.data = data
        self.cookies = cookies

    def hash(self, data):
        return str(hashlib.md5(data.encode()).hexdigest())

    def get_base_string(self):
        base_str = self.hash(self.params)
        base_str = base_str + self.hash(self.data) if self.data else base_str + "0" * 32
        base_str = base_str + self.hash(self.cookies) if self.cookies else base_str + "0" * 32
        return base_str

    def get_value(self):
        return self.encrypt(self.get_base_string())

    def encrypt(self, data):
        length = 0x14
        key = [0xDF, 0x77, 0xB9, 0x40, 0xB9, 0x9B, 0x84, 0x83,
               0xD1, 0xB9, 0xCB, 0xD1, 0xF7, 0xC2, 0xB9, 0x85,
               0xC3, 0xD0, 0xFB, 0xC3]
        param_list = []
        for i in range(0, 12, 4):
            temp = data[8 * i : 8 * (i + 1)]
            for j in range(4):
                H = int(temp[j * 2 : (j + 1) * 2], 16)
                param_list.append(H)
        param_list.extend([0x0, 0x6, 0xB, 0x1C])
        H = int(hex(int(self.unix)), 16)
        param_list.append((H & 0xFF000000) >> 24)
        param_list.append((H & 0x00FF0000) >> 16)
        param_list.append((H & 0x0000FF00) >> 8)
        param_list.append((H & 0x000000FF) >> 0)
        eor_result_list = []
        for A, B in zip(param_list, key):
            eor_result_list.append(A ^ B)
        for i in range(length):
            C = self.reverse(eor_result_list[i])
            D = eor_result_list[(i + 1) % length]
            E = C ^ D
            F = self.rbit_algorithm(E)
            H = ((F ^ 0xFFFFFFFF) ^ length) & 0xFF
            eor_result_list[i] = H
        result = ""
        for param in eor_result_list:
            result += self.hex_string(param)
        return {
            "x-ss-req-ticket": str(int(self.unix * 1000)),
            "x-khronos": str(int(self.unix)),
            "x-gorgon": f"0404b0d30000{result}"
        }

    def rbit_algorithm(self, num):
        result = ""
        tmp_string = bin(num)[2:]
        while len(tmp_string) < 8:
            tmp_string = "0" + tmp_string
        for i in range(0, 8):
            result = result + tmp_string[7 - i]
        return int(result, 2)

    def hex_string(self, num):
        tmp_string = hex(num)[2:]
        if len(tmp_string) < 2:
            tmp_string = "0" + tmp_string
        return tmp_string

    def reverse(self, num):
        tmp_string = self.hex_string(num)
        return int(tmp_string[1:] + tmp_string[:1], 16)


# ============================================================
# LADON
# ============================================================

def md5bytes(data):
    m = hashlib.md5()
    m.update(data)
    return m.hexdigest()


def validate(num):
    return num & 0xFFFFFFFFFFFFFFFF


def set_type_data(ptr, index, data, data_type):
    if data_type == "uint64_t":
        ptr[index * 8 : (index + 1) * 8] = data.to_bytes(8, "little")


def __ROR__(value, count):
    nbits = ctypes.sizeof(value) * 8
    count %= nbits
    low = ctypes.c_ulonglong(value.value << (nbits - count)).value
    value = ctypes.c_ulonglong(value.value >> count).value
    value = value | low
    return value


def encrypt_ladon_input(hash_table, input_data):
    data0 = int.from_bytes(input_data[:8], byteorder="little")
    data1 = int.from_bytes(input_data[8:], byteorder="little")
    for i in range(0x22):
        hash_val = int.from_bytes(hash_table[i * 8 : (i + 1) * 8], byteorder="little")
        data1 = validate(hash_val ^ (data0 + ((data1 >> 8) | (data1 << (64 - 8)))))
        data0 = validate(data1 ^ ((data0 >> 0x3D) | (data0 << (64 - 0x3D))))
    output_data = bytearray(26)
    output_data[:8] = data0.to_bytes(8, byteorder="little")
    output_data[8:] = data1.to_bytes(8, byteorder="little")
    return bytes(output_data)


def encrypt_ladon(md5hex, data, size):
    hash_table = bytearray(272 + 16)
    hash_table[:32] = md5hex
    temp = []
    for i in range(4):
        temp.append(int.from_bytes(hash_table[i * 8 : (i + 1) * 8], byteorder="little"))
    buffer_b0 = temp[0]
    buffer_b8 = temp[1]
    temp.pop(0)
    temp.pop(0)
    for i in range(0, 0x22):
        x9 = buffer_b0
        x8 = buffer_b8
        x8 = validate(__ROR__(ctypes.c_ulonglong(x8), 8))
        x8 = validate(x8 + x9)
        x8 = validate(x8 ^ i)
        temp.append(x8)
        x8 = validate(x8 ^ __ROR__(ctypes.c_ulonglong(x9), 61))
        set_type_data(hash_table, i + 1, x8, "uint64_t")
        buffer_b0 = x8
        buffer_b8 = temp[0]
        temp.pop(0)
    new_size = padding_size(size)
    input_buf = bytearray(new_size)
    input_buf[:size] = data
    pkcs7_padding_pad_buffer(input_buf, size, new_size, 16)
    output = bytearray(new_size)
    for i in range(new_size // 16):
        output[i * 16 : (i + 1) * 16] = encrypt_ladon_input(
            hash_table, input_buf[i * 16 : (i + 1) * 16])
    return output


def ladon_encrypt(khronos, lc_id=1611921764, aid=1233, random_bytes=None):
    if random_bytes is None:
        random_bytes = urandom(4)
    data = f"{khronos}-{lc_id}-{aid}"
    keygen = random_bytes + str(aid).encode()
    md5hex = md5bytes(keygen)
    size = len(data)
    new_size = padding_size(size)
    output = bytearray(new_size + 4)
    output[:4] = random_bytes
    output[4:] = encrypt_ladon(md5hex.encode(), data.encode(), size)
    return base64.b64encode(bytes(output)).decode()


class Ladon:
    @staticmethod
    def encrypt(x_khronos, lc_id, aid):
        return ladon_encrypt(x_khronos, lc_id, aid)


# ============================================================
# COMBINED SIGN
# ============================================================

def sign(params, payload=None, sec_device_id='', cookie=None,
         aid=1233, license_id=1611921764,
         sdk_version_str='v05.00.06-ov-android',
         sdk_version=167775296, platform=0, unix=None):
    x_ss_stub = md5(payload.encode('utf-8')).hexdigest() if payload is not None else None
    if not unix:
        unix = time()
    return Gorgon(params, unix, payload, cookie).get_value() | {
        'content-length': str(len(payload)) if payload else '0',
        'x-ss-stub': x_ss_stub.upper() if x_ss_stub else '',
        'x-ladon': Ladon.encrypt(int(unix), license_id, aid),
        'x-argus': Argus.get_sign(params, x_ss_stub, int(unix),
            platform=platform, aid=aid, license_id=license_id,
            sec_device_id=sec_device_id, sdk_version=sdk_version_str,
            sdk_version_int=sdk_version)
    }


# ============================================================
# PUZZLE SOLVER
# ============================================================

class PuzzleSolver:
    def __init__(self, base64puzzle, base64piece):
        self.puzzle = base64puzzle
        self.piece = base64piece
        self.methods = [cv2.TM_CCOEFF_NORMED, cv2.TM_CCORR_NORMED]

    def get_position(self):
        try:
            results = []
            puzzle = self.__background_preprocessing()
            piece = self.__piece_preprocessing()
            for method in self.methods:
                matched = cv2.matchTemplate(puzzle, piece, method)
                min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(matched)
                results.append((max_loc[0], max_val))
            enhanced_puzzle = self.__enhanced_preprocessing(puzzle)
            enhanced_piece = self.__enhanced_preprocessing(piece)
            for method in self.methods:
                matched = cv2.matchTemplate(enhanced_puzzle, enhanced_piece, method)
                min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(matched)
                results.append((max_loc[0], max_val))
            edge_puzzle = self.__edge_detection(puzzle)
            edge_piece = self.__edge_detection(piece)
            matched = cv2.matchTemplate(edge_puzzle, edge_piece, cv2.TM_CCOEFF_NORMED)
            min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(matched)
            results.append((max_loc[0], max_val))
            results.sort(key=lambda x: x[1], reverse=True)
            return results[0][0]
        except:
            puzzle = self.__background_preprocessing()
            piece = self.__piece_preprocessing()
            matched = cv2.matchTemplate(puzzle, piece, cv2.TM_CCOEFF_NORMED)
            min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(matched)
            return max_loc[0]

    def __background_preprocessing(self):
        return self.__sobel_operator(self.__img_to_array(self.piece))

    def __piece_preprocessing(self):
        return self.__sobel_operator(self.__img_to_array(self.puzzle))

    def __enhanced_preprocessing(self, img):
        if len(img.shape) == 3:
            img = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
        return clahe.apply(img)

    def __edge_detection(self, img):
        gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY) if len(img.shape) == 3 else img
        return cv2.Canny(cv2.GaussianBlur(gray, (3, 3), 0), 50, 150)

    def __sobel_operator(self, img):
        gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY) if len(img.shape) == 3 else img
        gray = cv2.GaussianBlur(gray, (3, 3), 0)
        grad_x = cv2.Sobel(gray, cv2.CV_16S, 1, 0, ksize=3)
        grad_y = cv2.Sobel(gray, cv2.CV_16S, 0, 1, ksize=3)
        abs_grad_x = cv2.convertScaleAbs(grad_x)
        abs_grad_y = cv2.convertScaleAbs(grad_y)
        grad = cv2.addWeighted(abs_grad_x, 0.5, abs_grad_y, 0.5, 0)
        return cv2.normalize(grad, None, 0, 255, cv2.NORM_MINMAX)

    def __img_to_array(self, base64_input):
        if isinstance(base64_input, str):
            base64_input = base64_input.encode()
        img_data = base64.b64decode(base64_input)
        img_array = np.frombuffer(img_data, dtype=np.uint8)
        decoded_img = cv2.imdecode(img_array, cv2.IMREAD_UNCHANGED)
        if decoded_img is None:
            raise ValueError("Failed to decode image")
        if len(decoded_img.shape) == 2:
            decoded_img = cv2.cvtColor(decoded_img, cv2.COLOR_GRAY2BGR)
        elif decoded_img.shape[2] == 4:
            decoded_img = cv2.cvtColor(decoded_img, cv2.COLOR_RGBA2BGR)
        return decoded_img


# ============================================================
# CAPTCHA SOLVER
# ============================================================

class CaptchaSolver:
    def __init__(self, session, country, ua):
        self.host = CAPTCHA_TT_HOST
        self.country = country
        self.session = session
        self.ua = ua

    def _build_params(self, device_type, device_brand, iid, did, detail="", server_sdk_env=""):
        if not server_sdk_env:
            server_sdk_env = quote(json.dumps(
                {"idc": "useast2b", "region": "I18N", "server_type": "passport"}), safe="")
        return (
            f'lang=en&app_name={APP_NAME}&h5_sdk_version=2.33.7&h5_sdk_use_type=cdn'
            f'&sdk_version=2.3.4.i18n&iid={iid}&did={did}&device_id={did}'
            f'&ch={CHANNEL}&aid={AID}&os_type=0&mode=slide'
            f'&tmp={int(time())}{random.randint(111, 999)}'
            f'&platform=app&webdriver=undefined'
            f'&verify_host=https%3A%2F%2F{self.host}%2F'
            f'&locale=en&channel={CHANNEL}&app_key'
            f'&vc={VERSION_CODE}&app_version={VERSION_NAME}'
            f'&session_id&region=i18n&use_native_report=1&use_jsb_request=1'
            f'&orientation=2&resolution=720*1280&os_version={OS_VERSION}'
            f'&device_brand={device_brand}&device_model={device_type}'
            f'&os_name=Android&version_code={VERSION_CODE}'
            f'&device_type={device_type}&device_platform=Android'
            f'&type=verify&detail={detail}&server_sdk_env={server_sdk_env}'
            f'&imagex_domain&subtype=slide&challenge_code=99996'
            f'&triggered_region=i18n&cookie_enabled=true'
            f'&screen_width=360&screen_height=640'
            f'&browser_language=en&browser_platform=Linux%20i686'
            f'&browser_name=Mozilla'
            f'&browser_version=5.0%20%28Linux%3B%20Android%20{OS_VERSION}'
            f'%3B%20{device_type}%20Build%2FTP1A%3B%20wv%29'
            f'%20AppleWebKit%2F537.36%20%28KHTML%2C%20like%20Gecko%29'
            f'%20Version%2F4.0%20Chrome%2F86.0.4240.198'
            f'%20Mobile%20Safari%2F537.36%20BytedanceWebview%2Fd8a21c6'
        )

    def _sign_and_headers(self, params):
        sig = sign(
            params, '',
            "AadCFwpTyztA5j9L" + ''.join(
                secrets.choice(string.ascii_letters + string.digits) for _ in range(9)),
            None, AID)
        return {
            'X-Tt-Request-Tag': 'n=1;t=0',
            'X-Vc-Bdturing-Sdk-Version': '2.3.4.i18n',
            'X-Tt-Bypass-Dp': '1',
            'Content-Type': 'application/json; charset=utf-8',
            'X-Tt-Dm-Status': 'login=0;ct=0;rt=7',
            'X-Tt-Store-Region': self.country,
            'X-Tt-Store-Region-Src': 'did',
            'User-Agent': self.ua,
            "x-ss-req-ticket": sig["x-ss-req-ticket"],
            "x-ss-stub": sig.get("x-ss-stub", ""),
            "X-Gorgon": sig["x-gorgon"],
            "X-Khronos": str(sig["x-khronos"]),
            "X-Ladon": sig["x-ladon"],
            "X-Argus": sig["x-argus"],
        }

    def get_captcha(self, iid, did, device_type, device_brand, detail="", server_sdk_env=""):
        params = self._build_params(device_type, device_brand, iid, did, detail, server_sdk_env)
        headers = self._sign_and_headers(params)
        try:
            resp = self.session.get(f'https://{self.host}/captcha/get?{params}',
                                    headers=headers, timeout=15)
            data = resp.json()
            log.info(f"captcha/get: {json.dumps(data, ensure_ascii=False)[:600]}")
            return data
        except Exception as e:
            log.error(f"captcha/get error: {e}")
            return None

    def verify_captcha(self, payload, iid, did, device_type, device_brand,
                       detail="", server_sdk_env=""):
        params = self._build_params(device_type, device_brand, iid, did, detail, server_sdk_env)
        headers = self._sign_and_headers(params)
        try:
            resp = self.session.post(f'https://{self.host}/captcha/verify?{params}',
                                     headers=headers, json=payload, timeout=15)
            log.info(f"captcha/verify: {resp.status_code} {resp.text[:300]}")
            return resp.text
        except Exception as e:
            log.error(f"captcha/verify error: {e}")
            return None

    def start(self, iid, did, device_type, device_brand, detail="", server_sdk_env=""):
        try:
            _captcha = self.get_captcha(iid, did, device_type, device_brand,
                                        detail, server_sdk_env)
            if not _captcha:
                return None

            # === AUTO-PASS: server already verified captcha ===
            if (_captcha.get("code") == 200 and
                    _captcha.get("msg_sub_code") == "success"):
                log.info("Captcha auto-passed by server!")
                return "verified"

            cdata = _captcha.get("data") or {}
            challenges = cdata.get("challenges", [])
            if not challenges:
                log.error("No challenges in captcha response")
                return None

            ch = challenges[0]
            mode = ch.get("mode", "")
            captcha_id = ch.get("id", "")
            verify_id = cdata.get("verify_id", "")
            question = ch.get("question", {})

            log.info(f"Captcha mode={mode} id={captcha_id[:30]}")

            # ---- 3D CAPTCHA ----
            if mode == "3d":
                log.info("3D captcha — solving via JustScrape API")
                url1 = question.get("url1", "")
                if not url1:
                    log.error("No 3D image URL")
                    return None

                img = self.session.get(url1, timeout=10).content
                img_b64 = base64.b64encode(img).decode()
                log.info(f"3D image: {len(img)} bytes")

                try:
                    solve_resp = requests.post(
                        f"{CAPTCHA_API_HOST}/captcha/3d",
                        json={"image_base64": img_b64, "modified_img_width": 348},
                        headers={"x-api-key": CAPTCHA_API_KEY},
                        timeout=30)
                    solution = solve_resp.json()
                    log.info(f"3D solver: {solution}")
                except Exception as e:
                    log.error(f"3D solver error: {e}")
                    return None

                sol = solution.get("data", solution)
                if "x1" not in sol:
                    log.error(f"Bad solver response: {solution}")
                    return None

                reply = [
                    {"relative_time": random.randint(600, 800),
                     "x": sol["x1"], "y": sol["y1"]},
                    {"relative_time": random.randint(1200, 1500),
                     "x": sol["x2"], "y": sol["y2"]},
                ]

                verify_payload = {
                    "modified_img_width": 348,
                    "id": captcha_id,
                    "mode": "3d",
                    "reply": reply,
                    "verify_id": verify_id,
                }

                return self.verify_captcha(verify_payload, iid, did,
                                           device_type, device_brand,
                                           detail, server_sdk_env)

            # ---- SLIDE CAPTCHA ----
            url1 = question.get("url1", "")
            url2 = question.get("url2", "")
            if not url1 or not url2:
                log.error(f"No images for mode={mode}")
                return None

            log.info("Slide captcha — downloading images")
            puzzle_img = self.session.get(url1, timeout=10).content
            piece_img = self.session.get(url2, timeout=10).content
            log.info(f"Images: puzzle={len(puzzle_img)}b piece={len(piece_img)}b")

            solver = PuzzleSolver(base64.b64encode(puzzle_img), base64.b64encode(piece_img))
            max_loc = solver.get_position()
            log.info(f"Puzzle position: {max_loc}")

            tip_y = question.get("tip_y", 140)
            rand_length = random.randint(50, 100)
            movements = []
            for i in range(rand_length):
                progress = (i + 1) / rand_length
                x_pos = round(max_loc * progress)
                y_offset = random.randint(-2, 2) if 0 < i < rand_length - 1 else 0
                movements.append({
                    "relative_time": i * rand_length + random.randint(-5, 5),
                    "x": x_pos, "y": tip_y + y_offset
                })

            verify_payload = {
                "modified_img_width": 552,
                "id": captcha_id,
                "mode": "slide",
                "reply": movements,
                "verify_id": verify_id
            }

            return self.verify_captcha(verify_payload, iid, did,
                                       device_type, device_brand,
                                       detail, server_sdk_env)

        except Exception as e:
            log.error(f"CaptchaSolver.start error: {e}")
            traceback.print_exc()
            return None


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


def parse_custom_proxy(ps):
    if "@" in ps:
        return {"http": f"http://{ps}", "https": f"http://{ps}"}
    parts = ps.split(":")
    if len(parts) == 4:
        h, p, u, pw = parts
        return {"http": f"http://{u}:{pw}@{h}:{p}", "https": f"http://{u}:{pw}@{h}:{p}"}
    return {"http": f"http://{ps}", "https": f"http://{ps}"}


def test_proxy(pd):
    try:
        r = requests.get("http://ip-api.com/json/", proxies=pd, timeout=15, verify=False)
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
        self.ms_token = None
        self.verify_fp = None
        self.openudid = hashlib.md5(uuid.uuid4().bytes).hexdigest()[:16]
        self.cdid = str(uuid.uuid4())
        self.ua = (
            f"com.zhiliaoapp.musically/{MANIFEST_VERSION} "
            f"(Linux; U; Android {OS_VERSION}; "
            f"{self.prof['lang']}_{self.region.upper()}; "
            f"{DEVICE_TYPE}; Build/TP1A; tt-ok/3.12.13.4-tiktok)"
        )

    def register_device(self):
        log.info("Registering device...")
        body = {
            "magic_tag": "ss_app_log",
            "header": {
                "display_name": "TikTok",
                "update_version_code": int(MANIFEST_VERSION),
                "manifest_version_code": int(MANIFEST_VERSION),
                "app_version_minor": "", "aid": AID, "channel": CHANNEL,
                "package": "com.zhiliaoapp.musically",
                "app_version": VERSION_NAME, "version_code": int(VERSION_CODE),
                "sdk_version": "2.3.4.i18n", "os": "Android",
                "os_version": OS_VERSION, "os_api": OS_API,
                "device_model": DEVICE_TYPE, "device_brand": DEVICE_BRAND,
                "device_manufacturer": DEVICE_BRAND, "cpu_abi": HOST_ABI,
                "release_build": "1", "density_dpi": int(DPI),
                "display_density": "mdpi", "resolution": RESOLUTION,
                "language": self.prof["lang"],
                "timezone": int(self.prof["tz_off"]) // 3600,
                "access": "wifi", "not_request_sender": 0,
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
        params = {"aid": str(AID), "app_name": APP_NAME, "version_code": VERSION_CODE,
                  "device_platform": "android", "device_type": DEVICE_TYPE,
                  "os_version": OS_VERSION}
        headers = {"User-Agent": self.ua, "Content-Type": "application/json; charset=utf-8",
                   "Accept-Encoding": "gzip"}
        try:
            resp = self.session.post(
                f"https://{REGISTER_HOST}/service/2/device_register/",
                params=params, json=body, headers=headers, timeout=15)
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

    def warmup(self):
        log.info("Warming device...")
        bp = self._params()
        self._signed_get("/aweme/v1/app_alert_check/", bp)
        time_module.sleep(random.uniform(*WARMUP_DELAY))
        fp = {**bp, "count": "6", "type": "0", "max_cursor": "0", "pull_type": "1"}
        self._signed_get("/aweme/v1/feed/", fp)
        time_module.sleep(random.uniform(*REQUEST_DELAY))

    def send_code(self, phone, sms_type=33):
        area = detect_area(phone)
        log.info(f"send_code: {phone} area={area} type={sms_type}")
        bp = self._params()
        query = urlencode(bp)
        body_d = {"phone_number": phone, "area": area, "country_code": area,
                  "type": str(sms_type), "aid": str(AID),
                  "account_sdk_source": "app", "mix_mode": "1", "multi_login": "1"}
        body = urlencode(body_d)
        sig = sign(query, body, aid=AID)
        headers = {"User-Agent": self.ua, "Accept-Encoding": "gzip",
                   "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
                   "X-Tt-Store-Region": self.region, "X-Tt-Store-Region-Src": "did"}
        headers.update(sig)
        url = f"https://{API_HOST}/passport/mobile/send_code/v1/?{query}"
        try:
            resp = self.session.post(url, data=body, headers=headers, timeout=15)
            self._cookies()
            if resp.status_code == 200 and len(resp.content) == 0:
                log.warning("EMPTY RESPONSE")
                return {"ok": False, "ec": -1, "msg": "empty_response", "captcha": False}
            data = resp.json()
            log.debug(f"send_code raw: {json.dumps(data, ensure_ascii=False)[:500]}")
            ec = data.get("data", {}).get("error_code", data.get("error_code", -1))
            msg = data.get("data", {}).get("description", data.get("message", ""))
            log.info(f"send_code result: ec={ec} msg={msg}")

            if ec == 0:
                return {"ok": True, "ec": 0, "msg": msg, "captcha": False, "raw": data}

            if ec in (1105, 1107):
                conf = {}
                vconf_str = data.get("data", {}).get("verify_center_decision_conf", "")
                if vconf_str:
                    try:
                        vconf = json.loads(vconf_str)
                        conf = {
                            "detail": vconf.get("detail", ""),
                            "region": vconf.get("region", ""),
                            "subtype": vconf.get("subtype", ""),
                            "server_sdk_env": vconf.get("server_sdk_env", ""),
                            "type": vconf.get("type", ""),
                        }
                        log.info(f"Captcha conf parsed: subtype={conf['subtype']} "
                                 f"region={conf['region']} "
                                 f"detail={conf['detail'][:60]}...")
                    except json.JSONDecodeError:
                        log.warning("Failed to parse verify_center_decision_conf")
                if not conf.get("detail"):
                    raw_captcha = data.get("data", {}).get("captcha", "")
                    if isinstance(raw_captcha, dict):
                        conf = raw_captcha
                    elif isinstance(raw_captcha, str) and raw_captcha:
                        try:
                            conf = json.loads(raw_captcha)
                        except:
                            pass
                return {"ok": False, "ec": ec, "msg": msg, "captcha": True, "conf": conf}

            if ec == 7:
                return {"ok": False, "ec": 7, "msg": "rate_limit", "captcha": False}

            return {"ok": False, "ec": ec, "msg": msg, "captcha": False, "raw": data}
        except Exception as e:
            log.error(f"send_code error: {e}")
            return {"ok": False, "ec": -1, "msg": str(e), "captcha": False}

    def solve_captcha(self, conf=None):
        log.info("Solving captcha...")
        detail = conf.get("detail", "") if conf else ""
        server_sdk_env = conf.get("server_sdk_env", "") if conf else ""
        subtype = conf.get("subtype", "") if conf else ""

        log.info(f"Captcha subtype: {subtype}")
        log.info(f"Detail: {detail[:80]}...")

        captcha_solver = CaptchaSolver(
            session=self.session, country=self.region, ua=self.ua)

        for attempt in range(MAX_CAPTCHA_RETRIES):
            log.info(f"Captcha attempt {attempt + 1}/{MAX_CAPTCHA_RETRIES}")

            result = captcha_solver.start(
                iid=self.iid, did=self.did,
                device_type=DEVICE_TYPE, device_brand=DEVICE_BRAND,
                detail=detail, server_sdk_env=server_sdk_env)

            if not result:
                log.warning("Captcha solver returned None")
                time_module.sleep(random.uniform(2, 4))
                continue

            # === AUTO-PASS: captcha was already solved by server ===
            if result == "verified":
                log.info("CAPTCHA AUTO-PASSED — no solving needed!")
                return True

            try:
                rd = json.loads(result) if isinstance(result, str) else result
                verify_code = rd.get("code", 0)
                msg_sub = rd.get("msg_sub_code", "")
                message = rd.get("message", "")
                log.info(f"Verify: code={verify_code} msg_sub={msg_sub} msg={message}")

                if msg_sub == "success":
                    log.info("CAPTCHA VERIFIED!")
                    return True
                if verify_code == 200 and "conclu" in message.lower():
                    log.info("CAPTCHA VERIFIED (message)!")
                    return True

                log.warning(f"Verify failed: {str(result)[:200]}")
            except:
                if "success" in str(result).lower():
                    log.info("CAPTCHA VERIFIED (raw)!")
                    return True
                log.warning(f"Verify raw: {str(result)[:200]}")

            time_module.sleep(random.uniform(2, 4))

        log.error("All captcha attempts failed")
        return False

    def run(self, phone, sms_type=33, warm=True):
        log.info("=" * 50)
        log.info(f"Pipeline: {phone} | region={self.region} | type={sms_type}")
        log.info("=" * 50)

        if not self.register_device():
            return {"ok": False, "ec": -1, "error": "register_failed"}
        time_module.sleep(random.uniform(*REQUEST_DELAY))

        if warm:
            self.warmup()
            time_module.sleep(random.uniform(*REQUEST_DELAY))

        for send_attempt in range(MAX_SEND_RETRIES):
            log.info(f"send_code attempt {send_attempt + 1}/{MAX_SEND_RETRIES}")
            result = self.send_code(phone, sms_type)

            if result["ok"]:
                log.info("=" * 50)
                log.info("SMS SENT!")
                log.info("=" * 50)
                return result

            if result.get("captcha"):
                conf = result.get("conf", {})
                solved = self.solve_captcha(conf)
                if solved:
                    log.info("Captcha solved, retrying send_code...")
                    time_module.sleep(random.uniform(*POST_CAPTCHA_DELAY))
                    continue
                else:
                    return {"ok": False, "ec": result["ec"],
                            "error": "captcha_failed", "msg": result.get("msg", "")}

            if result.get("ec") == 7:
                log.warning("Rate limited")
                return result
            if result.get("msg") == "empty_response":
                log.warning("Empty response")
                return result

            return result

        log.error("Max send retries exhausted")
        return {"ok": False, "ec": -1, "error": "max_retries"}

    def _params(self):
        ts = str(int(time_module.time()))
        return {
            "passport-sdk-version": "25",
            "iid": self.iid or "0", "device_id": self.did or "0",
            "ac": "wifi", "channel": CHANNEL, "aid": str(AID),
            "app_name": APP_NAME, "version_code": VERSION_CODE,
            "version_name": VERSION_NAME, "device_platform": "android",
            "os": "android", "ab_version": VERSION_NAME, "ssmix": "a",
            "device_type": DEVICE_TYPE, "device_brand": DEVICE_BRAND,
            "language": self.prof["lang"], "os_api": OS_API,
            "os_version": OS_VERSION, "openudid": self.openudid,
            "manifest_version_code": MANIFEST_VERSION,
            "resolution": RESOLUTION, "dpi": DPI,
            "update_version_code": MANIFEST_VERSION,
            "_rticket": str(int(time_module.time() * 1000)),
            "is_pad": "0", "current_region": self.region.upper(),
            "app_type": "normal", "sys_region": self.prof["carrier"],
            "mcc_mnc": self.prof["mcc"], "timezone_name": self.prof["tz"],
            "residence": self.region.upper(),
            "app_language": self.prof["lang"],
            "carrier_region": self.prof["carrier"],
            "ac2": "wifi", "uoo": "0", "op_region": self.region.upper(),
            "timezone_offset": self.prof["tz_off"],
            "build_number": BUILD_NUMBER, "host_abi": HOST_ABI,
            "locale": self.prof["locale"], "region": self.region.upper(),
            "ts": ts, "cdid": self.cdid, "app_version": VERSION_NAME,
        }

    def _signed_get(self, ep, params):
        query = urlencode(params)
        sig = sign(query, aid=AID)
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
# BATCH
# ============================================================

def run_batch(numbers, sms_type=33, proxy_user=PROXY_USER,
              proxy_pass=PROXY_PASS, warm=True):
    results = []
    session_count = 0
    proxy_dict = None

    for i, (phone, country) in enumerate(numbers):
        if session_count >= MAX_PER_SESSION or proxy_dict is None:
            proxy_dict, sid = build_proxy(country, proxy_user, proxy_pass)
            session_count = 0
            log.info(f"New proxy session: {sid}")
            if not test_proxy(proxy_dict):
                results.append({"phone": phone, "ok": False, "error": "proxy_dead"})
                proxy_dict = None
                continue

        client = TikTokClient(country, proxy_dict)
        result = client.run(phone, sms_type, warm=warm)
        results.append({"phone": phone, **result})
        session_count += 1

        if result.get("ec") in (7, -1):
            session_count = MAX_PER_SESSION
            proxy_dict = None

        if i < len(numbers) - 1:
            time_module.sleep(random.uniform(3, 8))

    ok = sum(1 for r in results if r.get("ok"))
    log.info("=" * 50)
    log.info(f"BATCH: {ok}/{len(results)} success")
    for r in results:
        s = "OK" if r.get("ok") else f"FAIL(ec={r.get('ec', '?')})"
        log.info(f"  {r['phone']}: {s} {r.get('msg', r.get('error', ''))}")
    log.info("=" * 50)
    return results


# ============================================================
# CLI
# ============================================================

def main():
    parser = argparse.ArgumentParser(description="TikTok SMS v10.0")
    parser.add_argument("phone", nargs="?", default=None, help="Phone (+55...)")
    parser.add_argument("--region", default=None, help="br/us/ca/it/de/ae")
    parser.add_argument("--type", type=int, default=33, help="2/9/33")
    parser.add_argument("--no-warm", action="store_true")
    parser.add_argument("--no-proxy", action="store_true")
    parser.add_argument("--proxy-user", default=PROXY_USER)
    parser.add_argument("--proxy-pass", default=PROXY_PASS)
    parser.add_argument("--proxy", default=None, help="user:pass@host:port")
    parser.add_argument("--batch", nargs="+")
    parser.add_argument("--test-proxy", action="store_true")
    parser.add_argument("-v", "--verbose", action="store_true")
    args = parser.parse_args()

    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    if args.test_proxy:
        region = args.region or "br"
        pd = parse_custom_proxy(args.proxy) if args.proxy else build_proxy(
            region, args.proxy_user, args.proxy_pass)[0]
        test_proxy(pd)
        return

    if not args.phone and not args.batch:
        parser.print_help()
        return

    if args.batch:
        phones = []
        if args.phone:
            phones.append((args.phone, args.region or detect_country(args.phone)))
        for ph in args.batch:
            phones.append((ph, detect_country(ph)))
        run_batch(phones, args.type, args.proxy_user, args.proxy_pass,
                  not args.no_warm)
        return

    phone = args.phone
    region = args.region or detect_country(phone)

    if args.no_proxy:
        proxy_dict = None
        log.info("No proxy")
    elif args.proxy:
        proxy_dict = parse_custom_proxy(args.proxy)
        if not test_proxy(proxy_dict):
            sys.exit(1)
    else:
        proxy_dict, sid = build_proxy(region, args.proxy_user, args.proxy_pass)
        log.info(f"IPRoyal session: {sid}")
        if not test_proxy(proxy_dict):
            sys.exit(1)

    client = TikTokClient(region, proxy_dict)
    result = client.run(phone, args.type, warm=not args.no_warm)

    print()
    print(json.dumps(result, indent=2, ensure_ascii=False))
    sys.exit(0 if result.get("ok") else 1)


if __name__ == "__main__":
    main()