"""
TikTok SMS v9.0 — Direct Pipeline (complete)

All crypto from solver.py included verbatim.
No external signer dependencies.

Pipeline:
  1. Device register
  2. Warmup
  3. send_code (Argus/Gorgon/Ladon)
  4. Captcha handling (auto-pass / slide / 3d)
  5. Retry send_code

Requirements:
  pip install requests pycryptodome opencv-python numpy

Usage:
  python tiktok_sms.py +5588951570521
  python tiktok_sms.py +5588951570521 --region br --type 33 -v
  python tiktok_sms.py +5588951570521 --no-proxy -v
  python tiktok_sms.py +5588951570521 --batch +18304034231
  python tiktok_sms.py --test-proxy --region br
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
# SM3 HASH (from solver.py — complete)
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
        Z = X ^ (self.__rotate_left(X, 15)) ^ (self.__rotate_left(X, 23))
        return Z

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
                & 0xFFFFFFFF,
                7,
            )
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
            A & 0xFFFFFFFF ^ V_i[0],
            B & 0xFFFFFFFF ^ V_i[1],
            C & 0xFFFFFFFF ^ V_i[2],
            D & 0xFFFFFFFF ^ V_i[3],
            E & 0xFFFFFFFF ^ V_i[4],
            F & 0xFFFFFFFF ^ V_i[5],
            G & 0xFFFFFFFF ^ V_i[6],
            H & 0xFFFFFFFF ^ V_i[7],
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
# SIMON CIPHER (from solver.py — complete)
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
# PROTOBUF (from solver.py — complete)
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

    def __str__(self):
        if ((self.type == ProtoFieldType.INT32) or
            (self.type == ProtoFieldType.INT64) or
                (self.type == ProtoFieldType.VARINT)):
            return '%d(%s): %d' % (self.idx, self.type.name, self.val)
        elif self.type == ProtoFieldType.STRING:
            if self.isAsciiStr():
                return '%d(%s): "%s"' % (self.idx, self.type.name, self.val.decode('ascii'))
            else:
                return '%d(%s): h"%s"' % (self.idx, self.type.name, self.val.hex())
        elif ((self.type == ProtoFieldType.GROUPSTART) or (self.type == ProtoFieldType.GROUPEND)):
            return '%d(%s): %s' % (self.idx, self.type.name, self.val)
        else:
            return '%d(%s): %s' % (self.idx, self.type.name, self.val)


class ProtoReader:
    def __init__(self, data):
        self.data = data
        self.pos = 0

    def seek(self, pos):
        self.pos = pos

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
        bs = int32.to_bytes(4, byteorder='little', signed=False)
        self.write(bs)

    def writeInt64(self, int64):
        bs = int64.to_bytes(8, byteorder='little', signed=False)
        self.write(bs)

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
        if (data != None):
            if (type(data) != bytes and type(data) != dict):
                raise ProtoError(
                    'unsupport type(%s) to protobuf' % (type(data)))
            if (type(data) == bytes) and (len(data) > 0):
                self.__parseBuf(data)
            elif (type(data) == dict) and (len(data) > 0):
                self.__parseDict(data)

    def __getitem__(self, idx):
        pf = self.get(int(idx))
        if (pf == None):
            return None
        if (pf.type != ProtoFieldType.STRING):
            return pf.val
        if (type(idx) != int):
            return pf.val
        if (pf.val == None):
            return None
        if (pf.isAsciiStr()):
            return pf.val.decode('utf-8')
        return ProtoBuf(pf.val)

    def __parseBuf(self, bytes_data):
        reader = ProtoReader(bytes_data)
        while reader.isRemain(1):
            key = reader.readVarint()
            field_type = ProtoFieldType(key & 0x7)
            field_idx = key >> 3
            if (field_idx == 0):
                break
            if (field_type == ProtoFieldType.INT32):
                self.put(ProtoField(field_idx, field_type, reader.readInt32()))
            elif (field_type == ProtoFieldType.INT64):
                self.put(ProtoField(field_idx, field_type, reader.readInt64()))
            elif (field_type == ProtoFieldType.VARINT):
                self.put(ProtoField(field_idx, field_type, reader.readVarint()))
            elif (field_type == ProtoFieldType.STRING):
                self.put(ProtoField(field_idx, field_type, reader.readString()))
            else:
                raise ProtoError(
                    'parse protobuf error, unexpected field type: %s' % (field_type.name))

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
            else:
                raise ProtoError(
                    'encode to protobuf error, unexpected field type: %s' % (field.type.name))
        return writer.toBytes()

    def dump(self):
        for field in self.fields:
            print(field)

    def getList(self, idx):
        return [field for field in self.fields if field.idx == idx]

    def get(self, idx):
        for field in self.fields:
            if field.idx == idx:
                return field
        return None

    def getInt(self, idx):
        pf = self.get(idx)
        if (pf == None):
            return 0
        if ((pf.type == ProtoFieldType.INT32) or (pf.type == ProtoFieldType.INT64) or (pf.type == ProtoFieldType.VARINT)):
            return pf.val
        raise ProtoError("getInt(%d) -> %s" % (idx, pf.type))

    def getBytes(self, idx):
        pf = self.get(idx)
        if (pf == None):
            return None
        if (pf.type == ProtoFieldType.STRING):
            return pf.val
        raise ProtoError("getBytes(%d) -> %s" % (idx, pf.type))

    def getUtf8(self, idx):
        bs = self.getBytes(idx)
        if (bs == None):
            return None
        return bs.decode('utf-8')

    def getProtoBuf(self, idx):
        bs = self.getBytes(idx)
        if (bs == None):
            return None
        return ProtoBuf(bs)

    def put(self, field: ProtoField):
        self.fields.append(field)

    def putInt32(self, idx, int32):
        self.put(ProtoField(idx, ProtoFieldType.INT32, int32))

    def putInt64(self, idx, int64):
        self.put(ProtoField(idx, ProtoFieldType.INT64, int64))

    def putVarint(self, idx, vint):
        self.put(ProtoField(idx, ProtoFieldType.VARINT, vint))

    def putBytes(self, idx, data):
        self.put(ProtoField(idx, ProtoFieldType.STRING, data))

    def putUtf8(self, idx, data):
        self.put(ProtoField(idx, ProtoFieldType.STRING, data.encode('utf-8')))

    def putProtoBuf(self, idx, data):
        self.put(ProtoField(idx, ProtoFieldType.STRING, data.toBuf()))

    def __parseDict(self, data):
        for k, v in data.items():
            if (isinstance(v, int)):
                self.putVarint(k, v)
            elif (isinstance(v, str)):
                self.putUtf8(k, v)
            elif (isinstance(v, bytes)):
                self.putBytes(k, v)
            elif (isinstance(v, dict)):
                self.putProtoBuf(k, ProtoBuf(v))
            else:
                raise ProtoError('unsupport type(%s) to protobuf' % (type(v)))

    def toDict(self, out):
        for k, v in out.items():
            if (isinstance(v, int)):
                out[k] = self.getInt(k)
            elif (isinstance(v, str)):
                out[k] = self.getUtf8(k)
            elif (isinstance(v, bytes)):
                out[k] = self.getBytes(k)
            elif (isinstance(v, dict)):
                out[k] = self.getProtoBuf(k).toDict(v)
            else:
                raise ProtoError('unsupport type(%s) to protobuf' % (type(v)))
        return out


# ============================================================
# PKCS7 + ByteBuf (from solver.py — complete)
# ============================================================

def pkcs7_padding_data_length(buffer, buffer_size, modulus):
    if buffer_size % modulus != 0 or buffer_size < modulus:
        return 0
    padding_value = buffer[buffer_size - 1]
    if padding_value < 1 or padding_value > modulus:
        return 0
    if buffer_size < padding_value + 1:
        return 0
    count = 1
    buffer_size -= 1
    for i in range(count, padding_value):
        buffer_size -= 1
        if buffer[buffer_size] != padding_value:
            return 0
    return buffer_size


def pkcs7_padding_pad_buffer(buffer: bytearray, data_length: int, buffer_size: int, modulus: int) -> int:
    pad_byte = modulus - (data_length % modulus)
    if data_length + pad_byte > buffer_size:
        return -pad_byte
    for i in range(pad_byte):
        buffer[data_length + i] = pad_byte
    return pad_byte


def padding_size(size: int) -> int:
    mod = size % 16
    if mod > 0:
        return size + (16 - mod)
    return size


class ByteBuf:
    def __init__(self, data, size=None):
        if data:
            self.mem = data
        if size is not None:
            self.data_size = size
        elif data is not None:
            self.data_size = len(data)
        else:
            raise ValueError("either size or data must be provided")
        self.pos = 0

    def data(self):
        return self.mem

    def size(self):
        return self.data_size

    def remove_padding(self):
        padding_sz = pkcs7_padding_data_length(self.mem, self.data_size, 16)
        if padding_sz == 0:
            return self.data_size
        self.data_size = padding_sz
        dst = (ctypes.c_uint8 * self.data_size)()
        dst = self.mem[:self.data_size]
        self.mem = dst
        return self.mem


# ============================================================
# ARGUS (from solver.py — complete)
# ============================================================

class Argus:
    def encrypt_enc_pb(data, l):
        data = list(data)
        xor_array = data[:8]

        for i in range(8, l):
            data[i] ^= xor_array[i % 8]

        return bytes(data[::-1])

    @staticmethod
    def get_bodyhash(stub: str or None = None) -> bytes:
        return (
            SM3().sm3_hash(bytes(16))[0:6] if stub == None or len(stub) == 0
            else SM3().sm3_hash(bytes.fromhex(stub))[0:6]
        )

    @staticmethod
    def get_queryhash(query: str) -> bytes:
        return (
            SM3().sm3_hash(bytes(16))[0:6] if query == None or len(query) == 0
            else SM3().sm3_hash(query.encode())[0:6]
        )

    @staticmethod
    def encrypt(xargus_bean: dict):
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
    def get_sign(queryhash: None or str = None,
                 data: None or str = None,
                 timestamp: int = int(time()),
                 aid: int = 1233,
                 license_id: int = 1611921764,
                 platform: int = 0,
                 sec_device_id: str = "",
                 sdk_version: str = "v04.04.05-ov-android",
                 sdk_version_int: int = 134744640) -> dict:

        params_dict = parse_qs(queryhash)

        p = params_dict.get('app_version', [VERSION_NAME])[0].split('.')
        app_version_hash = bytes.fromhex(
            '{:x}{:x}{:x}00'.format(
                int(p[2]) * 4, int(p[1]) * 16, int(p[0]) * 4
            ).zfill(8)
        )
        app_version_constant = (int.from_bytes(app_version_hash, byteorder='big') << 1)

        return Argus.encrypt({
            1: 0x20200929 << 1,
            2: 2,
            3: randint(0, 0x7FFFFFFF),
            4: str(aid),
            5: params_dict.get('device_id', ['0'])[0],
            6: str(license_id),
            7: params_dict.get('app_version', [VERSION_NAME])[0],
            8: sdk_version,
            9: sdk_version_int,
            10: bytes(8),
            12: (timestamp << 1),
            13: Argus.get_bodyhash(data),
            14: Argus.get_queryhash(queryhash),
            16: sec_device_id,
            20: "none",
            21: 738,
            25: 2
        })


# ============================================================
# GORGON (from solver.py — complete)
# ============================================================

class Gorgon:
    def __init__(self, params: str, unix: int, data: str = None, cookies: str = None) -> None:
        self.unix = unix
        self.params = params
        self.data = data
        self.cookies = cookies

    def hash(self, data: str) -> str:
        return str(hashlib.md5(data.encode()).hexdigest())

    def get_base_string(self) -> str:
        base_str = self.hash(self.params)
        base_str = (
            base_str + self.hash(self.data) if self.data else base_str + str("0" * 32)
        )
        base_str = (
            base_str + self.hash(self.cookies)
            if self.cookies
            else base_str + str("0" * 32)
        )
        return base_str

    def get_value(self) -> dict:
        return self.encrypt(self.get_base_string())

    def encrypt(self, data: str) -> dict:
        length = 0x14
        key = [
            0xDF, 0x77, 0xB9, 0x40, 0xB9, 0x9B, 0x84, 0x83,
            0xD1, 0xB9, 0xCB, 0xD1, 0xF7, 0xC2, 0xB9, 0x85,
            0xC3, 0xD0, 0xFB, 0xC3,
        ]
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
# LADON (from solver.py — complete)
# ============================================================

def md5bytes(data: bytes) -> str:
    m = hashlib.md5()
    m.update(data)
    return m.hexdigest()


def get_type_data(ptr, index, data_type):
    if data_type == "uint64_t":
        return int.from_bytes(ptr[index * 8 : (index + 1) * 8], "little")
    else:
        raise ValueError("Invalid data type")


def set_type_data(ptr, index, data, data_type):
    if data_type == "uint64_t":
        ptr[index * 8 : (index + 1) * 8] = data.to_bytes(8, "little")
    else:
        raise ValueError("Invalid data type")


def validate(num):
    return num & 0xFFFFFFFFFFFFFFFF


def __ROR__(value: ctypes.c_ulonglong, count: int) -> ctypes.c_ulonglong:
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


def encrypt_ladon(md5hex: bytes, data: bytes, size: int):
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
            hash_table, input_buf[i * 16 : (i + 1) * 16]
        )

    return output


def ladon_encrypt(
    khronos: int,
    lc_id: int = 1611921764,
    aid: int = 1233,
    random_bytes: bytes = None
) -> str:
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
    def encrypt(x_khronos: int, lc_id: str, aid: int) -> str:
        return ladon_encrypt(x_khronos, lc_id, aid)


# ============================================================
# COMBINED SIGN (from solver.py — complete)
# ============================================================

def sign(params: str, payload: str or None = None, sec_device_id: str = '',
         cookie: str or None = None, aid: int = 1233,
         license_id: int = 1611921764,
         sdk_version_str: str = 'v05.00.06-ov-android',
         sdk_version: int = 167775296, platform: int = 0,
         unix: float = None):
    x_ss_stub = md5(payload.encode('utf-8')).hexdigest() if payload != None else None
    if not unix:
        unix = time()

    return Gorgon(params, unix, payload, cookie).get_value() | {
        'content-length': str(len(payload)) if payload else '0',
        'x-ss-stub': x_ss_stub.upper() if x_ss_stub else '',
        'x-ladon': Ladon.encrypt(int(unix), license_id, aid),
        'x-argus': Argus.get_sign(params, x_ss_stub, int(unix),
            platform=platform,
            aid=aid,
            license_id=license_id,
            sec_device_id=sec_device_id,
            sdk_version=sdk_version_str,
            sdk_version_int=sdk_version
        )
    }


# ============================================================
# PUZZLE SOLVER (from solver.py — complete with enhancements)
# ============================================================

class PuzzleSolver:
    def __init__(self, base64puzzle, base64piece):
        self.puzzle = base64puzzle
        self.piece = base64piece
        self.methods = [
            cv2.TM_CCOEFF_NORMED,
            cv2.TM_CCORR_NORMED
        ]

    def get_position(self):
        try:
            results = []

            puzzle = self.__background_preprocessing()
            piece = self.__piece_preprocessing()

            for method in self.methods:
                matched = cv2.matchTemplate(puzzle, piece, method)
                min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(matched)
                if method == cv2.TM_SQDIFF_NORMED:
                    results.append((min_loc[0], 1 - min_val))
                else:
                    results.append((max_loc[0], max_val))

            enhanced_puzzle = self.__enhanced_preprocessing(puzzle)
            enhanced_piece = self.__enhanced_preprocessing(piece)

            for method in self.methods:
                matched = cv2.matchTemplate(enhanced_puzzle, enhanced_piece, method)
                min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(matched)
                if method == cv2.TM_SQDIFF_NORMED:
                    results.append((min_loc[0], 1 - min_val))
                else:
                    results.append((max_loc[0], max_val))

            edge_puzzle = self.__edge_detection(puzzle)
            edge_piece = self.__edge_detection(piece)

            matched = cv2.matchTemplate(edge_puzzle, edge_piece, cv2.TM_CCOEFF_NORMED)
            min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(matched)
            results.append((max_loc[0], max_val))

            results.sort(key=lambda x: x[1], reverse=True)
            return results[0][0]

        except Exception as e:
            puzzle = self.__background_preprocessing()
            piece = self.__piece_preprocessing()
            matched = cv2.matchTemplate(puzzle, piece, cv2.TM_CCOEFF_NORMED)
            min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(matched)
            return max_loc[0]

    def __background_preprocessing(self):
        img = self.__img_to_array(self.piece)
        background = self.__sobel_operator(img)
        return background

    def __piece_preprocessing(self):
        img = self.__img_to_array(self.puzzle)
        template = self.__sobel_operator(img)
        return template

    def __enhanced_preprocessing(self, img):
        if len(img.shape) == 3:
            img = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
        enhanced = clahe.apply(img)
        return enhanced

    def __edge_detection(self, img):
        if len(img.shape) == 3:
            gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        else:
            gray = img
        blurred = cv2.GaussianBlur(gray, (3, 3), 0)
        edges = cv2.Canny(blurred, 50, 150)
        return edges

    def __sobel_operator(self, img):
        if len(img.shape) == 3:
            gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        else:
            gray = img
        gray = cv2.GaussianBlur(gray, (3, 3), 0)
        grad_x = cv2.Sobel(gray, cv2.CV_16S, 1, 0, ksize=3)
        grad_y = cv2.Sobel(gray, cv2.CV_16S, 0, 1, ksize=3)
        abs_grad_x = cv2.convertScaleAbs(grad_x)
        abs_grad_y = cv2.convertScaleAbs(grad_y)
        grad = cv2.addWeighted(abs_grad_x, 0.5, abs_grad_y, 0.5, 0)
        grad = cv2.normalize(grad, None, 0, 255, cv2.NORM_MINMAX)
        return grad

    def __img_to_array(self, base64_input):
        try:
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
        except Exception as e:
            raise ValueError(f"Image processing error: {str(e)}")


# ============================================================
# CAPTCHA SOLVER (from solver.py — adapted for our pipeline)
# ============================================================

class CaptchaSolver:
    """
    Original CaptchaSolver from solver.py, adapted.
    Used for getting and verifying slide captcha with proper signing.
    """
    def __init__(self, session, country, ua, proxy=None):
        self.host = CAPTCHA_TT_HOST
        self.country = country
        self.session = session
        self.ua = ua

    def get_captcha(self, iid, did, device_type, device_brand):
        params = (
            f'lang=en&app_name={APP_NAME}&h5_sdk_version=2.33.7&h5_sdk_use_type=cdn&sdk_version=2.3.4.i18n'
            f'&iid={iid}&did={did}&device_id={did}&ch={CHANNEL}&aid={AID}&os_type=0&mode=slide'
            f'&tmp={int(time())}{random.randint(111, 999)}&platform=app&webdriver=undefined'
            f'&verify_host=https%3A%2F%2F{self.host}%2F&locale=en&channel={CHANNEL}&app_key'
            f'&vc={VERSION_CODE}&app_version={VERSION_NAME}&session_id&region=i18n&use_native_report=1'
            f'&use_jsb_request=1&orientation=2&resolution=720*1280&os_version={OS_VERSION}'
            f'&device_brand={device_brand}&device_model={device_type}&os_name=Android'
            f'&version_code={VERSION_CODE}&device_type={device_type}'
            f'&device_platform=Android&type=verify&detail=&server_sdk_env=&imagex_domain'
            f'&subtype=slide&challenge_code=99996&triggered_region=i18n'
            f'&cookie_enabled=true&screen_width=360&screen_height=640'
            f'&browser_language=en&browser_platform=Linux%20i686'
            f'&browser_name=Mozilla'
            f'&browser_version=5.0%20%28Linux%3B%20Android%20{OS_VERSION}%3B%20{device_type}'
            f'%20Build%2FTP1A%3B%20wv%29%20AppleWebKit%2F537.36%20%28KHTML%2C%20like%20Gecko%29'
            f'%20Version%2F4.0%20Chrome%2F86.0.4240.198%20Mobile%20Safari%2F537.36'
            f'%20BytedanceWebview%2Fd8a21c6'
        )

        sig = sign(
            params, '',
            "AadCFwpTyztA5j9L" + ''.join(
                secrets.choice(string.ascii_letters + string.digits) for _ in range(9)
            ),
            None, AID
        )

        headers = {
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
            "X-Argus": sig["x-argus"]
        }

        try:
            url = f'https://{self.host}/captcha/get?{params}'
            resp = self.session.get(url, headers=headers, timeout=15)
            data = resp.json()
            log.info(f"CaptchaSolver.get_captcha response: {json.dumps(data, ensure_ascii=False)[:600]}")
            return data
        except Exception as e:
            log.error(f"CaptchaSolver.get_captcha error: {e}")
            return None

    def verify_captcha(self, data, iid, did, device_type, device_brand):
        params = (
            f'lang=en&app_name={APP_NAME}&h5_sdk_version=2.33.7&h5_sdk_use_type=cdn&sdk_version=2.3.4.i18n'
            f'&iid={iid}&did={did}&device_id={did}&ch={CHANNEL}&aid={AID}&os_type=0&mode=slide'
            f'&tmp={int(time())}{random.randint(111, 999)}&platform=app&webdriver=undefined'
            f'&verify_host=https%3A%2F%2F{self.host}%2F&locale=en&channel={CHANNEL}&app_key'
            f'&vc={VERSION_CODE}&app_version={VERSION_NAME}&session_id&region=i18n&use_native_report=1'
            f'&use_jsb_request=1&orientation=2&resolution=720*1280&os_version={OS_VERSION}'
            f'&device_brand={device_brand}&device_model={device_type}&os_name=Android'
            f'&version_code={VERSION_CODE}&device_type={device_type}'
            f'&device_platform=Android&type=verify&detail=&server_sdk_env=&imagex_domain'
            f'&subtype=slide&challenge_code=99996&triggered_region=i18n'
            f'&cookie_enabled=true&screen_width=360&screen_height=640'
            f'&browser_language=en&browser_platform=Linux%20i686'
            f'&browser_name=Mozilla'
            f'&browser_version=5.0%20%28Linux%3B%20Android%20{OS_VERSION}%3B%20{device_type}'
            f'%20Build%2FTP1A%3B%20wv%29%20AppleWebKit%2F537.36%20%28KHTML%2C%20like%20Gecko%29'
            f'%20Version%2F4.0%20Chrome%2F86.0.4240.198%20Mobile%20Safari%2F537.36'
            f'%20BytedanceWebview%2Fd8a21c6'
        )

        sig = sign(
            params, '',
            "AadCFwpTyztA5j9L" + ''.join(
                secrets.choice(string.ascii_letters + string.digits) for _ in range(9)
            ),
            None, AID
        )

        headers = {
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
            "X-Argus": sig["x-argus"]
        }

        try:
            resp = self.session.post(
                f'https://{self.host}/captcha/verify?{params}',
                headers=headers,
                json=data,
                timeout=15
            )
            log.info(f"CaptchaSolver.verify_captcha response: {resp.text[:300]}")
            return resp.text
        except Exception as e:
            log.error(f"CaptchaSolver.verify_captcha error: {e}")
            return None

    def start(self, iid, did, device_type, device_brand) -> str:
        """Full slide captcha flow: get -> solve -> verify"""
        try:
            _captcha = self.get_captcha(iid, did, device_type, device_brand)
            if not _captcha:
                return None

            # Check for auto-pass
            code = _captcha.get("code", 0)
            msg_sub = _captcha.get("msg_sub_code", "")
            if code == 200 and msg_sub == "success":
                log.info("Captcha auto-passed in CaptchaSolver.start()")
                return "auto_pass"

            cdata = _captcha.get("data", {})
            challenges = cdata.get("challenges", [])

            if not challenges:
                if code == 200:
                    return "auto_pass"
                log.error("No challenges in captcha response")
                return None

            captcha_data = challenges[0]
            mode = captcha_data.get("mode", "")
            captcha_id = captcha_data.get("id", "")
            verify_id = cdata.get("verify_id", "")
            question = captcha_data.get("question", {})

            # hcaptcha auto-pass
            if mode == "hcaptcha" and (captcha_id == "abc" or code == 200):
                log.info("hcaptcha auto-passed")
                return "auto_pass"

            url1 = question.get("url1", "")
            url2 = question.get("url2", "")

            if not url1 or not url2:
                if code == 200:
                    return "auto_pass"
                log.error(f"No image URLs, mode={mode}")
                return None

            log.info(f"Downloading captcha images (mode={mode})...")
            puzzle_img = self.session.get(url1, timeout=10).content
            piece_img = self.session.get(url2, timeout=10).content

            puzzle_b64 = base64.b64encode(puzzle_img)
            piece_b64 = base64.b64encode(piece_img)

            solver = PuzzleSolver(puzzle_b64, piece_b64)
            max_loc = solver.get_position()
            log.info(f"Puzzle position: {max_loc}")

            rand_length = random.randint(50, 100)
            movements = []
            tip_y = question.get("tip_y", 140)

            for i in range(rand_length):
                progress = (i + 1) / rand_length
                x_pos = round(max_loc * progress)
                y_offset = random.randint(-2, 2) if i > 0 and i < rand_length - 1 else 0
                y_pos = tip_y + y_offset

                movements.append({
                    "relative_time": i * rand_length + random.randint(-5, 5),
                    "x": x_pos,
                    "y": y_pos
                })

            verify_payload = {
                "modified_img_width": 552,
                "id": captcha_id,
                "mode": "slide",
                "reply": movements,
                "verify_id": verify_id
            }

            return self.verify_captcha(verify_payload, iid, did, device_type, device_brand)

        except Exception as e:
            log.error(f"CaptchaSolver.start error: {e}")
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
# TIKTOK CLIENT (main pipeline)
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

    # -------- REGISTER --------

    def register_device(self):
        log.info("Registering device...")
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
            resp = self.session.post(
                f"https://{REGISTER_HOST}/service/2/device_register/",
                params=params, json=body, headers=headers, timeout=15
            )
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

    # -------- WARMUP --------

    def warmup(self):
        log.info("Warming device...")
        bp = self._params()

        self._signed_get("/aweme/v1/app_alert_check/", bp)
        time_module.sleep(random.uniform(*WARMUP_DELAY))

        fp = {**bp, "count": "6", "type": "0", "max_cursor": "0", "pull_type": "1"}
        self._signed_get("/aweme/v1/feed/", fp)
        time_module.sleep(random.uniform(*REQUEST_DELAY))

    # -------- SEND CODE --------

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

        sig = sign(query, body, aid=AID)

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
                conf = data.get("data", {}).get("captcha", data.get("captcha", {}))
                log.info(f"Captcha conf: {json.dumps(conf, ensure_ascii=False)[:300]}")
                return {"ok": False, "ec": ec, "msg": msg, "captcha": True, "conf": conf}

            if ec == 7:
                return {"ok": False, "ec": 7, "msg": "rate_limit", "captcha": False}

            return {"ok": False, "ec": ec, "msg": msg, "captcha": False, "raw": data}

        except Exception as e:
            log.error(f"send_code error: {e}")
            return {"ok": False, "ec": -1, "msg": str(e), "captcha": False}

    # -------- CAPTCHA --------

    def solve_captcha(self, conf=None):
        """
        Use original CaptchaSolver from solver.py for the full flow.
        This ensures identical signing as the working solver.py code.
        """
        log.info("Solving captcha via CaptchaSolver...")

        captcha_solver = CaptchaSolver(
            session=self.session,
            country=self.region,
            ua=self.ua
        )

        for attempt in range(MAX_CAPTCHA_RETRIES):
            log.info(f"Captcha attempt {attempt + 1}/{MAX_CAPTCHA_RETRIES}")

            result = captcha_solver.start(
                iid=self.iid,
                did=self.did,
                device_type=DEVICE_TYPE,
                device_brand=DEVICE_BRAND
            )

            if result == "auto_pass":
                log.info("Captcha auto-passed!")
                return True

            if result and ("success" in str(result).lower() or '"code": 200' in str(result)):
                log.info("Captcha SOLVED!")
                return True

            if result:
                # Check JSON response
                try:
                    rd = json.loads(result) if isinstance(result, str) else result
                    if rd.get("code") == 200 or rd.get("msg_sub_code") == "success":
                        log.info("Captcha verified!")
                        return True
                    log.warning(f"Captcha verify response: {str(result)[:200]}")
                except:
                    log.warning(f"Captcha verify raw: {str(result)[:200]}")
            else:
                log.warning("Captcha solver returned None")

            time_module.sleep(random.uniform(2, 4))

        # Fallback: try JustScrape API for 3D captcha
        if conf:
            log.info("Trying JustScrape e2e verify as fallback...")
            return self._justscrape_fallback(conf)

        log.error("All captcha attempts failed")
        return False

    def _justscrape_fallback(self, conf):
        """Fallback to JustScrape API for captcha types we can't solve locally"""
        detail = conf.get("detail", "")
        server_sdk_env = conf.get("server_sdk_env",
            json.dumps({"idc": "useast2b", "region": "I18N", "server_type": "passport"}))

        try:
            resp = requests.post(
                f"{CAPTCHA_API_HOST}/captcha/verify",
                json={
                    "device_id": self.did or "0",
                    "iid": "0",
                    "detail": detail,
                    "region": self.region,
                    "server_sdk_env": server_sdk_env,
                    "verify_fp": self.verify_fp or "",
                    "ms_token": self.ms_token or "",
                },
                headers={"x-api-key": CAPTCHA_API_KEY},
                timeout=60,
            )
            data = resp.json()
            log.info(f"JustScrape e2e: {data}")
            return data.get("status") in ("success", "info")
        except Exception as e:
            log.error(f"JustScrape fallback error: {e}")
            return False

    # -------- FULL PIPELINE --------

    def run(self, phone, sms_type=33, warm=True):
        log.info("=" * 50)
        log.info(f"Pipeline: {phone} | region={self.region} | type={sms_type}")
        log.info("=" * 50)

        # Step 1: Register
        if not self.register_device():
            return {"ok": False, "ec": -1, "error": "register_failed"}

        time_module.sleep(random.uniform(*REQUEST_DELAY))

        # Step 2: Warmup
        if warm:
            self.warmup()
            time_module.sleep(random.uniform(*REQUEST_DELAY))

        # Step 3: send_code with captcha retry loop
        for send_attempt in range(MAX_SEND_RETRIES):
            log.info(f"send_code attempt {send_attempt + 1}/{MAX_SEND_RETRIES}")

            result = self.send_code(phone, sms_type)

            # Success!
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
                    time_module.sleep(random.uniform(*POST_CAPTCHA_DELAY))
                    continue  # retry send_code
                else:
                    return {
                        "ok": False, "ec": result["ec"],
                        "error": "captcha_failed",
                        "msg": result.get("msg", "")
                    }

            # Rate limit
            if result.get("ec") == 7:
                log.warning("Rate limited — need different proxy/device")
                return result

            # Empty response
            if result.get("msg") == "empty_response":
                log.warning("Empty response — device flagged")
                return result

            # Other error
            log.warning(f"Error ec={result.get('ec')}")
            return result

        log.error("Max send retries exhausted")
        return {"ok": False, "ec": -1, "error": "max_retries"}

    # -------- HELPERS --------

    def _params(self):
        ts = str(int(time_module.time()))
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
            "_rticket": str(int(time_module.time() * 1000)),
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
        sig = sign(query, aid=AID)
        headers = {"User-Agent": self.ua, "Accept-Encoding": "gzip"}
        headers.update(sig)
        try:
            r = self.session.get(
                f"https://{API_HOST}{ep}", params=params,
                headers=headers, timeout=10
            )
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
    parser = argparse.ArgumentParser(
        description="TikTok SMS v9.0 — Direct Pipeline",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s +5588951570521
  %(prog)s +5588951570521 --region br --type 33 -v
  %(prog)s +5588951570521 --no-proxy -v
  %(prog)s +5588951570521 --proxy user:pass@host:port
  %(prog)s +5588951570521 --batch +18304034231 +18194146343
  %(prog)s --test-proxy --region br
        """
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

    # Test proxy
    if args.test_proxy:
        region = args.region or "br"
        if args.proxy:
            pd = parse_custom_proxy(args.proxy)
        else:
            pd, _ = build_proxy(region, args.proxy_user, args.proxy_pass)
        test_proxy(pd)
        return

    # Need phone
    if not args.phone and not args.batch:
        parser.print_help()
        return

    # Batch
    if args.batch:
        phones = []
        if args.phone:
            phones.append((args.phone, args.region or detect_country(args.phone)))
        for ph in args.batch:
            phones.append((ph, detect_country(ph)))
        run_batch(phones, args.type, args.proxy_user, args.proxy_pass,
                  warm=not args.no_warm)
        return

    # Single
    phone = args.phone
    region = args.region or detect_country(phone)

    if args.no_proxy:
        proxy_dict = None
        log.info("Running without proxy (local IP)")
    elif args.proxy:
        proxy_dict = parse_custom_proxy(args.proxy)
        log.info(f"Custom proxy: {args.proxy}")
        if not test_proxy(proxy_dict):
            sys.exit(1)
    else:
        proxy_dict, sid = build_proxy(region, args.proxy_user, args.proxy_pass)
        log.info(f"IPRoyal session: {sid}")
        if not test_proxy(proxy_dict):
            log.error("Proxy dead. Use --no-proxy or fix credentials.")
            sys.exit(1)

    client = TikTokClient(region, proxy_dict)
    result = client.run(phone, args.type, warm=not args.no_warm)

    print()
    print(json.dumps(result, indent=2, ensure_ascii=False))
    sys.exit(0 if result.get("ok") else 1)


if __name__ == "__main__":
    main()
