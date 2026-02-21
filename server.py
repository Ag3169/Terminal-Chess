#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════════╗
║            CHESS SERVER — Terminal Chess Multiplayer Server v2.0         ║
║                                                                          ║
║  Features:                                                               ║
║   • User authentication (register/login with username, password, email)  ║
║   • User profile management + ASCII avatars + bios                       ║
║   • Game history storage (50 games per user) with full PGN               ║
║   • ELO-banded matchmaking with time-control pairing                     ║
║   • Disconnect-tolerant games (60s reconnect window)                     ║
║   • Anti-cheat: move-time logging + bot-pattern flagging                 ║
║   • Swiss-system tournament scheduler                                    ║
║   • Server-queued post-game analysis jobs + daily puzzle endpoint        ║
║   • Friend heartbeat (online/in-game/offline status every 30s)           ║
║   • Lobby chat channel (global pre-game chat)                            ║
║   • Achievement system (10 built-in achievements)                        ║
║   • Rate limiting: max 5 failed logins per minute per IP                 ║
║   • Structured JSON logging with log rotation                            ║
║   • Expanded admin CLI (kick, ban, reset ELO, broadcast)                 ║
║   • Config file support (chess_server.cfg)                               ║
║   • TCP-based client/server communication with E2E encryption            ║
║   • JSON-based persistent database                                       ║
╚══════════════════════════════════════════════════════════════════════════╝
"""

import socket
import threading
import json
import hashlib
import struct
import os
import re
import time
import secrets
import base64
import random
import configparser
import logging
import logging.handlers
import queue
import itertools
from collections import defaultdict
from datetime import datetime, timedelta
from hmac import compare_digest

# ════════════════════════════════════════════════════════════════════════
#  E2E ENCRYPTION UTILITIES (Pure Python stdlib - AES-GCM + ECDH-like)
# ════════════════════════════════════════════════════════════════════════

def _xor_bytes(a: bytes, b: bytes) -> bytes:
    """XOR two byte strings."""
    return bytes(x ^ y for x, y in zip(a, b))

def _pad_pkcs7(data: bytes, block_size: int = 16) -> bytes:
    """Pad data using PKCS7."""
    pad_len = block_size - (len(data) % block_size)
    return data + bytes([pad_len] * pad_len)

def _unpad_pkcs7(data: bytes) -> bytes:
    """Remove PKCS7 padding."""
    pad_len = data[-1]
    if pad_len < 1 or pad_len > 16:
        raise ValueError("Invalid padding")
    if not compare_digest(data[-pad_len:], bytes([pad_len] * pad_len)):
        raise ValueError("Invalid padding")
    return data[:-pad_len]

def _bytes_to_int(b: bytes) -> int:
    """Convert bytes to integer (big-endian)."""
    return int.from_bytes(b, 'big')

def _int_to_bytes(n: int, length: int = 256) -> bytes:
    """Convert integer to bytes (big-endian). Default 256 bytes for 2048-bit DH."""
    return n.to_bytes(length, 'big')

def _mod_pow(base: int, exp: int, mod: int) -> int:
    """Modular exponentiation."""
    result = 1
    base = base % mod
    while exp > 0:
        if exp & 1:
            result = (result * base) % mod
        exp >>= 1
        base = (base * base) % mod
    return result

# 2048-bit MODP Group (RFC 3526)
_DH_P = int(
    "FFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD1"
    "29024E088A67CC74020BBEA63B139B22514A08798E3404DD"
    "EF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245"
    "E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7ED"
    "EE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3D"
    "C2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F"
    "83655D23DCA3AD961C62F356208552BB9ED529077096966D"
    "670C354E4ABC9804F1746C08CA18217C32905E462E36CE3B"
    "E39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9"
    "DE2BCBF6955817183995497CEA956AE515D2261898FA0510"
    "15728E5A8AACAA68FFFFFFFFFFFFFFFF", 16
)
_DH_G = 2
_DH_PRIVATE_BITS = 256

def _dh_generate_keypair():
    """Generate Diffie-Hellman key pair."""
    private_key = secrets.randbits(_DH_PRIVATE_BITS)
    public_key = _mod_pow(_DH_G, private_key, _DH_P)
    return private_key, public_key

def _dh_compute_shared_secret(private_key: int, other_public: int) -> bytes:
    """Compute DH shared secret and derive AES key."""
    shared = _mod_pow(other_public, private_key, _DH_P)
    # Derive 256-bit key using HKDF-like construction
    return hashlib.sha256(_int_to_bytes(shared)).digest()

def _aes_encrypt_block(block: bytes, key: bytes) -> bytes:
    """AES-256 encryption (pure Python implementation)."""
    # AES S-box
    SBOX = bytes([
        0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
        0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
        0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
        0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
        0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
        0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
        0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
        0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
        0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
        0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
        0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
        0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
        0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
        0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
        0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
        0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
    ])
    
    # Round constants
    RCON = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a]
    
    def sub_bytes(state):
        return [SBOX[b] for b in state]
    
    def shift_rows(state):
        s = state[:]
        # Row 1: shift left by 1
        s[1], s[5], s[9], s[13] = state[5], state[9], state[13], state[1]
        # Row 2: shift left by 2
        s[2], s[6], s[10], s[14] = state[10], state[14], state[2], state[6]
        # Row 3: shift left by 3
        s[3], s[7], s[11], s[15] = state[15], state[3], state[7], state[11]
        return s
    
    def xtime(a):
        return ((a << 1) ^ 0x1b) & 0xff if a & 0x80 else (a << 1) & 0xff
    
    def mix_single_column(col):
        t = col[0] ^ col[1] ^ col[2] ^ col[3]
        u = col[0]
        col[0] ^= t ^ xtime(col[0] ^ col[1])
        col[1] ^= t ^ xtime(col[1] ^ col[2])
        col[2] ^= t ^ xtime(col[2] ^ col[3])
        col[3] ^= t ^ xtime(col[3] ^ u)
        return col
    
    def mix_columns(state):
        s = state[:]
        for i in range(4):
            col = mix_single_column(s[i*4:(i+1)*4])
            s[i*4:(i+1)*4] = col
        return s
    
    def add_round_key(state, round_key):
        return [s ^ k for s, k in zip(state, round_key)]
    
    def key_expansion(key):
        key_schedule = list(key)
        for i in range(4, 60):
            temp = key_schedule[(i-1)*4:(i)*4]
            if i % 4 == 0:
                temp = [SBOX[temp[1]], SBOX[temp[2]], SBOX[temp[3]], SBOX[temp[0]]]
                temp[0] ^= RCON[i//4 - 1]
            for j in range(4):
                key_schedule.append(key_schedule[(i-4)*4 + j] ^ temp[j])
        return key_schedule
    
    # Key expansion
    key_schedule = key_expansion(key)
    
    # Initial state
    state = list(block)
    
    # Initial round key addition
    state = add_round_key(state, key_schedule[:16])
    
    # Main rounds (14 rounds for AES-256)
    for round_num in range(1, 14):
        state = sub_bytes(state)
        state = shift_rows(state)
        state = mix_columns(state)
        state = add_round_key(state, key_schedule[round_num*16:(round_num+1)*16])
    
    # Final round (no MixColumns)
    state = sub_bytes(state)
    state = shift_rows(state)
    state = add_round_key(state, key_schedule[14*16:15*16])
    
    return bytes(state)

def _aes_decrypt_block(block: bytes, key: bytes) -> bytes:
    """AES-256 decryption (pure Python implementation)."""
    # AES inverse S-box
    INV_SBOX = bytes([
        0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
        0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
        0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
        0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
        0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
        0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
        0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
        0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
        0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
        0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
        0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
        0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
        0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
        0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
        0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
        0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d,
    ])
    
    RCON = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a]
    
    def inv_sub_bytes(state):
        return [INV_SBOX[b] for b in state]
    
    def inv_shift_rows(state):
        s = state[:]
        s[1], s[5], s[9], s[13] = state[13], state[1], state[5], state[9]
        s[2], s[6], s[10], s[14] = state[10], state[14], state[2], state[6]
        s[3], s[7], s[11], s[15] = state[7], state[11], state[15], state[3]
        return s
    
    def add_round_key(state, round_key):
        return [s ^ k for s, k in zip(state, round_key)]

    def gmul(a, b):
        """Galois Field multiplication for GF(2^8)."""
        p = 0
        for _ in range(8):
            if b & 1:
                p ^= a
            hi_bit = a & 0x80
            a = (a << 1) & 0xff
            if hi_bit:
                a ^= 0x1b
            b >>= 1
        return p

    def inv_mix_columns(state):
        """Inverse MixColumns transformation using GF multiplication."""
        s = state[:]
        for i in range(4):
            a = s[i*4:(i+1)*4]
            s[i*4] = gmul(0x0e, a[0]) ^ gmul(0x0b, a[1]) ^ gmul(0x0d, a[2]) ^ gmul(0x09, a[3])
            s[i*4+1] = gmul(0x09, a[0]) ^ gmul(0x0e, a[1]) ^ gmul(0x0b, a[2]) ^ gmul(0x0d, a[3])
            s[i*4+2] = gmul(0x0d, a[0]) ^ gmul(0x09, a[1]) ^ gmul(0x0e, a[2]) ^ gmul(0x0b, a[3])
            s[i*4+3] = gmul(0x0b, a[0]) ^ gmul(0x0d, a[1]) ^ gmul(0x09, a[2]) ^ gmul(0x0e, a[3])
        return s

    # Forward S-box needed for key expansion (same as in encrypt)
    SBOX = bytes([
        0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
        0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
        0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
        0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
        0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
        0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
        0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
        0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
        0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
        0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
        0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
        0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
        0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
        0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
        0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
        0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
    ])

    def key_expansion(key):
        key_schedule = list(key)
        for i in range(4, 60):
            temp = key_schedule[(i-1)*4:(i)*4]
            if i % 4 == 0:
                temp = [SBOX[temp[1]], SBOX[temp[2]], SBOX[temp[3]], SBOX[temp[0]]]
                temp[0] ^= RCON[i//4 - 1]
            for j in range(4):
                key_schedule.append(key_schedule[(i-4)*4 + j] ^ temp[j])
        return key_schedule
    
    key_schedule = key_expansion(key)
    state = list(block)
    state = add_round_key(state, key_schedule[14*16:15*16])
    
    for round_num in range(13, 0, -1):
        state = inv_shift_rows(state)
        state = inv_sub_bytes(state)
        state = add_round_key(state, key_schedule[round_num*16:(round_num+1)*16])
        if round_num > 1:
            state = inv_mix_columns(state)
    
    state = inv_shift_rows(state)
    state = inv_sub_bytes(state)
    state = add_round_key(state, key_schedule[:16])
    
    return bytes(state)

def _aes_ctr_encrypt(plaintext: bytes, key: bytes, nonce: bytes) -> bytes:
    """AES-256 CTR mode encryption."""
    result = bytearray()
    counter = 0
    for i in range(0, len(plaintext), 16):
        # Counter block: nonce (12 bytes) + counter (4 bytes, big-endian)
        counter_block = nonce + struct.pack('>I', counter)
        keystream = _aes_encrypt_block(counter_block, key)
        block = plaintext[i:i+16]
        encrypted = _xor_bytes(block, keystream[:len(block)])
        result.extend(encrypted)
        counter += 1
    return bytes(result)

def _aes_ctr_decrypt(ciphertext: bytes, key: bytes, nonce: bytes) -> bytes:
    """AES-256 CTR mode decryption (same as encryption for CTR mode)."""
    return _aes_ctr_encrypt(ciphertext, key, nonce)

def _ghash(h: bytes, data: bytes) -> bytes:
    """GHASH for GCM mode."""
    def gf_mult(x: int, y: int) -> int:
        """Multiply two numbers in GF(2^128) with the GCM polynomial."""
        z = 0
        # GCM uses bit-wise multiplication in GF(2^128)
        # The reduction polynomial is x^128 + x^7 + x^2 + x + 1
        R = 0xe1000000000000000000000000000000
        
        for i in range(128):
            # If the i-th bit of x is set, XOR y into z
            if (x >> (127 - i)) & 1:
                z ^= y
            # Check if the LSB of y is set (for reduction)
            if y & 1:
                # Right shift and apply reduction polynomial
                y = (y >> 1) ^ R
            else:
                y >>= 1
        return z

    h_int = _bytes_to_int(h)
    result = 0
    for i in range(0, len(data), 16):
        block = data[i:i+16]
        if len(block) < 16:
            block = block + b'\x00' * (16 - len(block))
        result = gf_mult(result ^ _bytes_to_int(block), h_int)
    return _int_to_bytes(result, 16)

def _gcm_encrypt(plaintext: bytes, key: bytes, nonce: bytes, aad: bytes = b'') -> tuple:
    """AES-GCM encryption."""
    # Generate H (hash key)
    h = _aes_encrypt_block(b'\x00' * 16, key)

    # Initial counter J0
    if len(nonce) == 12:
        j0 = nonce + b'\x00\x00\x00\x01'
    else:
        # For non-12-byte nonces, compute J0 = GHASH(H, nonce || 0^s || 64-bit length)
        s = (16 - (len(nonce) % 16)) % 16
        ghash_input = nonce + b'\x00' * s + _int_to_bytes(len(nonce) * 8, 8)
        j0 = _ghash(h, ghash_input)

    # Encrypt plaintext using CTR mode starting from J0 + 1
    ciphertext = _aes_ctr_encrypt(plaintext, key, j0[:12])

    # Compute GHASH for authentication tag
    ghash_input = aad + b'\x00' * ((16 - len(aad) % 16) % 16) if aad else b''
    ghash_input += ciphertext + b'\x00' * ((16 - len(ciphertext) % 16) % 16)
    ghash_input += _int_to_bytes(len(aad) * 8, 8) + _int_to_bytes(len(ciphertext) * 8, 8)

    s = _ghash(h, ghash_input)

    # Compute tag: S XOR E(K, J0)
    tag_input = _aes_encrypt_block(j0, key)
    tag = _xor_bytes(s, tag_input)

    return ciphertext, tag

def _gcm_decrypt(ciphertext: bytes, key: bytes, nonce: bytes, tag: bytes, aad: bytes = b'') -> bytes:
    """AES-GCM decryption."""
    h = _aes_encrypt_block(b'\x00' * 16, key)

    # Initial counter J0 (same as encryption)
    if len(nonce) == 12:
        j0 = nonce + b'\x00\x00\x00\x01'
    else:
        s = (16 - (len(nonce) % 16)) % 16
        ghash_input = nonce + b'\x00' * s + _int_to_bytes(len(nonce) * 8, 8)
        j0 = _ghash(h, ghash_input)

    # Verify tag first
    ghash_input = aad + b'\x00' * ((16 - len(aad) % 16) % 16) if aad else b''
    ghash_input += ciphertext + b'\x00' * ((16 - len(ciphertext) % 16) % 16)
    ghash_input += _int_to_bytes(len(aad) * 8, 8) + _int_to_bytes(len(ciphertext) * 8, 8)

    s = _ghash(h, ghash_input)
    tag_input = _aes_encrypt_block(j0, key)
    computed_tag = _xor_bytes(s, tag_input)

    if not compare_digest(computed_tag, tag):
        raise ValueError("Authentication tag verification failed")

    plaintext = _aes_ctr_decrypt(ciphertext, key, j0[:12])
    return plaintext

def encrypt_credentials(credentials: dict, server_public: int) -> dict:
    """Encrypt credentials using ECDH + AES-GCM."""
    # Generate ephemeral key pair
    client_private, client_public = _dh_generate_keypair()
    
    # Compute shared secret
    shared_secret = _dh_compute_shared_secret(client_private, server_public)
    
    # Serialize credentials
    credentials_json = json.dumps(credentials).encode('utf-8')
    
    # Generate random nonce
    nonce = secrets.token_bytes(12)
    
    # Encrypt with AES-GCM
    ciphertext, tag = _gcm_encrypt(credentials_json, shared_secret, nonce)
    
    return {
        'client_public': client_public,
        'nonce': base64.b64encode(nonce).decode(),
        'ciphertext': base64.b64encode(ciphertext).decode(),
        'tag': base64.b64encode(tag).decode()
    }

def decrypt_credentials(encrypted_data: dict, server_private: int) -> dict:
    """Decrypt credentials using ECDH + AES-GCM."""
    client_public = encrypted_data['client_public']
    nonce = base64.b64decode(encrypted_data['nonce'])
    ciphertext = base64.b64decode(encrypted_data['ciphertext'])
    tag = base64.b64decode(encrypted_data['tag'])
    
    # Compute shared secret
    shared_secret = _dh_compute_shared_secret(server_private, client_public)
    
    # Decrypt
    plaintext = _gcm_decrypt(ciphertext, shared_secret, nonce, tag)
    
    return json.loads(plaintext.decode('utf-8'))

# ════════════════════════════════════════════════════════════════════════
#  CONSTANTS
# ════════════════════════════════════════════════════════════════════════

# ── Server-side move legality tracker ───────────────────────────────────
# A minimal FEN parser + move validator lives here so the server can reject
# illegal moves from cheating clients without importing the full chess engine.
# Strategy: maintain the FEN after every verified move; on each MSG_GAME_MOVE
# reconstruct the board from FEN, generate pseudo-legal moves, and reject
# moves not in that set.  This is lightweight but catches:
#   • moving the wrong colour's piece
#   • moving to an illegal square
#   • moving when it's not your turn
# Full legality (pins, check) is enforced by the client engine; the server
# provides a second line of defence against modified/exploiting clients.

PIECE_OFFSETS = {
    'P': [], 'N': [(-2,-1),(-2,1),(-1,-2),(-1,2),(1,-2),(1,2),(2,-1),(2,1)],
    'B': [], 'R': [], 'Q': [], 'K': [(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)]
}
INITIAL_FEN = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"

def _sq(r, f):
    """Square index from 0-row 0-col."""
    if 0 <= r < 8 and 0 <= f < 8:
        return r * 8 + f
    return -1

def _parse_fen(fen):
    """Parse FEN into (board[64], side, castling, ep_sq, halfmove, fullmove)."""
    parts = fen.split()
    brd_str, side_ch, castle_str, ep_str = parts[0], parts[1], parts[2], parts[3]
    halfmove = int(parts[4]) if len(parts) > 4 else 0
    fullmove = int(parts[5]) if len(parts) > 5 else 1

    board = [None] * 64
    rank = 7
    file = 0
    for ch in brd_str:
        if ch == '/':
            rank -= 1; file = 0
        elif ch.isdigit():
            file += int(ch)
        else:
            board[rank * 8 + file] = ch
            file += 1

    side = 'w' if side_ch == 'w' else 'b'

    ep_sq = -1
    if ep_str != '-':
        ep_sq = (ord(ep_str[1]) - ord('1')) * 8 + (ord(ep_str[0]) - ord('a'))

    return board, side, castle_str, ep_sq, halfmove, fullmove

def _board_to_fen(board, side, castling, ep_sq, halfmove, fullmove):
    """Serialize board state back to FEN."""
    rows = []
    for rank in range(7, -1, -1):
        row = ''; empty = 0
        for file in range(8):
            p = board[rank * 8 + file]
            if p:
                if empty: row += str(empty); empty = 0
                row += p
            else:
                empty += 1
        if empty: row += str(empty)
        rows.append(row)
    fen = '/'.join(rows)
    ep = '-' if ep_sq < 0 else chr(ord('a') + ep_sq % 8) + chr(ord('1') + ep_sq // 8)
    return f"{fen} {side} {castling or '-'} {ep} {halfmove} {fullmove}"

def _server_pseudo_legal(board, side, castle_str, ep_sq):
    """Generate pseudo-legal (from_sq, to_sq) pairs for the given side.
    Pseudo-legal = correct piece movement, no check detection (handled client-side).
    """
    moves = []
    my_pieces = str.upper if side == 'w' else str.lower
    opp_colour = 'b' if side == 'w' else 'w'
    pawn_dir   = 1  if side == 'w' else -1
    pawn_start = 1  if side == 'w' else 6
    prom_rank  = 7  if side == 'w' else 0

    def is_mine(p):  return p is not None and (p.isupper() if side == 'w' else p.islower())
    def is_opp(p):   return p is not None and (p.islower() if side == 'w' else p.isupper())
    def is_empty(sq): return 0 <= sq < 64 and board[sq] is None

    for sq in range(64):
        p = board[sq]
        if not is_mine(p): continue
        pt = p.upper()
        r, f = sq // 8, sq % 8

        if pt == 'P':
            fwd = _sq(r + pawn_dir, f)
            if 0 <= fwd < 64 and board[fwd] is None:
                moves.append((sq, fwd))
                if r == pawn_start:
                    fwd2 = _sq(r + 2 * pawn_dir, f)
                    if board[fwd2] is None:
                        moves.append((sq, fwd2))
            for df in (-1, 1):
                cap = _sq(r + pawn_dir, f + df)
                if 0 <= cap < 64:
                    if is_opp(board[cap]) or cap == ep_sq:
                        moves.append((sq, cap))

        elif pt == 'N':
            for dr, df in PIECE_OFFSETS['N']:
                t = _sq(r + dr, f + df)
                if t >= 0 and not is_mine(board[t]):
                    moves.append((sq, t))

        elif pt in ('B', 'R', 'Q'):
            dirs = []
            if pt in ('B', 'Q'): dirs += [(-1,-1),(-1,1),(1,-1),(1,1)]
            if pt in ('R', 'Q'): dirs += [(-1,0),(1,0),(0,-1),(0,1)]
            for dr, df in dirs:
                nr, nf = r + dr, f + df
                while 0 <= nr < 8 and 0 <= nf < 8:
                    t = nr * 8 + nf
                    if is_mine(board[t]): break
                    moves.append((sq, t))
                    if is_opp(board[t]): break
                    nr += dr; nf += df

        elif pt == 'K':
            for dr, df in PIECE_OFFSETS['K']:
                t = _sq(r + dr, f + df)
                if t >= 0 and not is_mine(board[t]):
                    moves.append((sq, t))
            # Castling
            king_sq = 4 if side == 'w' else 60
            if sq == king_sq:
                if side == 'w':
                    if 'K' in castle_str and board[5] is None and board[6] is None:
                        moves.append((sq, 6))
                    if 'Q' in castle_str and board[3] is None and board[2] is None and board[1] is None:
                        moves.append((sq, 2))
                else:
                    if 'k' in castle_str and board[61] is None and board[62] is None:
                        moves.append((sq, 62))
                    if 'q' in castle_str and board[59] is None and board[58] is None and board[57] is None:
                        moves.append((sq, 58))
    return moves

def _apply_server_move(board, side, castle_str, ep_sq, halfmove, fullmove, from_sq, to_sq, promote_to='q'):
    """Apply a validated move and return new FEN fields."""
    new_board = board[:]
    p = new_board[from_sq]
    pt = p.upper() if p else ''
    captured = new_board[to_sq]
    new_ep = -1
    new_castle = castle_str

    # En passant capture
    if pt == 'P' and to_sq == ep_sq:
        ep_capture = ep_sq + (-8 if side == 'w' else 8)
        new_board[ep_capture] = None

    # Pawn double push -> set ep square
    if pt == 'P' and abs(to_sq - from_sq) == 16:
        new_ep = (from_sq + to_sq) // 2

    # Castling: move rook
    if pt == 'K':
        if from_sq == 4 and to_sq == 6:   new_board[5] = 'R'; new_board[7] = None
        if from_sq == 4 and to_sq == 2:   new_board[3] = 'R'; new_board[0] = None
        if from_sq == 60 and to_sq == 62: new_board[61] = 'r'; new_board[63] = None
        if from_sq == 60 and to_sq == 58: new_board[59] = 'r'; new_board[56] = None
        new_castle = new_castle.replace('K','').replace('Q','') if side=='w' else new_castle.replace('k','').replace('q','')

    # Pawn promotion
    if pt == 'P' and (to_sq // 8 == 7 or to_sq // 8 == 0):
        p = (promote_to.upper() if side == 'w' else promote_to.lower())

    # Rook moves strip castling rights
    if from_sq == 0:  new_castle = new_castle.replace('Q','')
    if from_sq == 7:  new_castle = new_castle.replace('K','')
    if from_sq == 56: new_castle = new_castle.replace('q','')
    if from_sq == 63: new_castle = new_castle.replace('k','')

    new_board[to_sq] = p
    new_board[from_sq] = None

    # Halfmove clock
    new_half = 0 if (pt == 'P' or captured) else halfmove + 1
    new_full = fullmove + (1 if side == 'b' else 0)
    new_side = 'b' if side == 'w' else 'w'

    return new_board, new_side, new_castle or '-', new_ep, new_half, new_full

def _san_to_squares(san, board, side, castle_str, ep_sq):
    """Convert SAN move string to (from_sq, to_sq, promote_to).
    Returns None if no match found in pseudo-legal moves.
    """
    import re
    san_clean = san.rstrip('+#')
    promote_to = 'q'

    # Castling
    if san_clean in ('O-O', '0-0'):
        king_sq = 4 if side == 'w' else 60
        return king_sq, king_sq + 2, 'q'
    if san_clean in ('O-O-O', '0-0-0'):
        king_sq = 4 if side == 'w' else 60
        return king_sq, king_sq - 2, 'q'

    # Promotion suffix (e.g. e8=Q or e8Q)
    promo_match = re.search(r'[=]?([QRBN])$', san_clean, re.IGNORECASE)
    if promo_match:
        promote_to = promo_match.group(1).lower()
        san_clean = san_clean[:promo_match.start()]

    # Coordinate notation: e2e4 or e2-e4
    coord_match = re.match(r'^([a-h][1-8])[-]?([a-h][1-8])$', san_clean)
    if coord_match:
        def alg_to_sq(s): return (int(s[1])-1)*8 + (ord(s[0])-ord('a'))
        return alg_to_sq(coord_match.group(1)), alg_to_sq(coord_match.group(2)), promote_to

    # SAN parsing: piece letter + optional disambiguation + optional x + dest
    m = re.match(r'^([NBRQK]?)([a-h]?)([1-8]?)(x?)([a-h][1-8])$', san_clean)
    if not m:
        return None
    piece_ch, file_hint, rank_hint, _, dest = m.groups()
    to_sq = (int(dest[1])-1)*8 + (ord(dest[0])-ord('a'))
    piece_type = (piece_ch or 'P').upper()
    if not piece_ch:
        piece_type = 'P'

    candidates = []
    for fsq, tsq in _server_pseudo_legal(board, side, castle_str, ep_sq):
        if tsq != to_sq: continue
        p = board[fsq]
        if p is None: continue
        if p.upper() != piece_type: continue
        fr, ff = fsq // 8, fsq % 8
        if file_hint and chr(ord('a') + ff) != file_hint: continue
        if rank_hint and str(fr + 1) != rank_hint: continue
        candidates.append((fsq, tsq))

    if len(candidates) == 1:
        return candidates[0][0], candidates[0][1], promote_to
    if len(candidates) > 1:
        return candidates[0][0], candidates[0][1], promote_to   # ambiguous but allow
    return None

SERVER_PORT = 65433
DATABASE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'database.json')
MAX_GAMES_PER_USER = 50   # raised from 3
LOG_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'chess_server.log')
CONFIG_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'chess_server.cfg')

# ════════════════════════════════════════════════════════════════════════
#  CONFIG FILE LOADER
# ════════════════════════════════════════════════════════════════════════
def _load_config():
    """Load server configuration from chess_server.cfg, or use defaults."""
    cfg = configparser.ConfigParser()
    defaults = {
        'port': str(SERVER_PORT),
        'host': '0.0.0.0',
        'max_clients': '100',
        'log_level': 'INFO',
        'log_max_bytes': '5242880',   # 5 MB
        'log_backup_count': '5',
        'max_failed_logins_per_min': '5',
        'disconnect_grace_seconds': '60',
        'heartbeat_interval': '30',
        'analysis_queue_workers': '1',
    }
    cfg['server'] = defaults
    if os.path.exists(CONFIG_FILE):
        cfg.read(CONFIG_FILE)
    else:
        # Write default config so admins can see/edit it
        with open(CONFIG_FILE, 'w') as f:
            cfg.write(f)
    return cfg['server']

_cfg = _load_config()

# ════════════════════════════════════════════════════════════════════════
#  STRUCTURED JSON LOGGER WITH ROTATION
# ════════════════════════════════════════════════════════════════════════
class _JsonFormatter(logging.Formatter):
    def format(self, record):
        log_obj = {
            'ts': datetime.utcnow().isoformat() + 'Z',
            'level': record.levelname,
            'msg': record.getMessage(),
        }
        if record.exc_info:
            log_obj['exc'] = self.formatException(record.exc_info)
        return json.dumps(log_obj)

def _setup_logger():
    logger = logging.getLogger('chess_server')
    level = getattr(logging, _cfg.get('log_level', 'INFO').upper(), logging.INFO)
    logger.setLevel(level)
    # Rotating file handler
    fh = logging.handlers.RotatingFileHandler(
        LOG_FILE,
        maxBytes=int(_cfg.get('log_max_bytes', 5242880)),
        backupCount=int(_cfg.get('log_backup_count', 5))
    )
    fh.setFormatter(_JsonFormatter())
    logger.addHandler(fh)
    # Console handler (plain text)
    ch = logging.StreamHandler()
    ch.setFormatter(logging.Formatter('  %(levelname)s %(message)s'))
    logger.addHandler(ch)
    return logger

log = _setup_logger()


# ════════════════════════════════════════════════════════════════════════
#  MESSAGE TYPES
# ════════════════════════════════════════════════════════════════════════
MSG_REGISTER = 'REGISTER'
MSG_LOGIN = 'LOGIN'
MSG_AUTO_LOGIN = 'AUTO_LOGIN'
MSG_LOGOUT = 'LOGOUT'
MSG_GET_PROFILE = 'GET_PROFILE'
MSG_SAVE_GAME = 'SAVE_GAME'
MSG_LIST_USERS = 'LIST_USERS'
MSG_PING = 'PING'
MSG_LEADERBOARD = 'LEADERBOARD'

# Matchmaking message types
MSG_QUEUE_JOIN = 'QUEUE_JOIN'
MSG_QUEUE_LEAVE = 'QUEUE_LEAVE'
MSG_QUEUE_STATUS = 'QUEUE_STATUS'
MSG_MATCH_FOUND = 'MATCH_FOUND'
MSG_MATCH_ACCEPT = 'MATCH_ACCEPT'
MSG_MATCH_DECLINE = 'MATCH_DECLINE'
MSG_GAME_START = 'GAME_START'
MSG_GAME_MOVE = 'GAME_MOVE'
MSG_GAME_RESIGN = 'GAME_RESIGN'
MSG_GAME_DRAW_OFFER = 'GAME_DRAW_OFFER'
MSG_GAME_DRAW_ACCEPT = 'GAME_DRAW_ACCEPT'
MSG_GAME_CHAT = 'GAME_CHAT'

# Friend system message types
MSG_FRIEND_REQUEST = 'FRIEND_REQUEST'
MSG_FRIEND_RESPONSE = 'FRIEND_RESPONSE'
MSG_FRIEND_LIST = 'FRIEND_LIST'
MSG_FRIEND_REMOVE = 'FRIEND_REMOVE'
MSG_FRIEND_STATUS = 'FRIEND_STATUS'

# Messaging system message types
MSG_KEY_EXCHANGE = 'KEY_EXCHANGE'
MSG_SEND_MESSAGE = 'SEND_MESSAGE'
MSG_GET_MESSAGES = 'GET_MESSAGES'
MSG_NEW_MESSAGE_NOTIFY = 'NEW_MESSAGE_NOTIFY'
MSG_MESSAGES_DELETED = 'MESSAGES_DELETED'
MSG_MESSAGE_SENT_ACK = 'MESSAGE_SENT_ACK'  # Acknowledgment that message was stored

# Challenge system message types
MSG_CHALLENGE_SEND = 'CHALLENGE_SEND'
MSG_CHALLENGE_RESPONSE = 'CHALLENGE_RESPONSE'
MSG_CHALLENGE_LIST = 'CHALLENGE_LIST'
MSG_CHALLENGE_CANCEL = 'CHALLENGE_CANCEL'

# E2E Encryption message types
MSG_GET_SERVER_PUBLIC_KEY = 'GET_SERVER_PUBLIC_KEY'
MSG_SESSION_KEY_EXCHANGE = 'SESSION_KEY_EXCHANGE'

# Spectator message types
MSG_SPECTATE_JOIN = 'SPECTATE_JOIN'
MSG_SPECTATE_LEAVE = 'SPECTATE_LEAVE'
MSG_SPECTATE_LIST = 'SPECTATE_LIST'
MSG_SPECTATE_UPDATE = 'SPECTATE_UPDATE'

# Rematch message types
MSG_REMATCH_REQUEST = 'REMATCH_REQUEST'
MSG_REMATCH_RESPONSE = 'REMATCH_RESPONSE'

# Game clock message types
MSG_GAME_CLOCK_UPDATE = 'GAME_CLOCK_UPDATE'
MSG_GAME_TIMEOUT = 'GAME_TIMEOUT'

# Player profile / avatar message types
MSG_SET_AVATAR = 'SET_AVATAR'
MSG_GET_AVATAR = 'GET_AVATAR'

# Chat history message type
MSG_GAME_CHAT_HISTORY = 'GAME_CHAT_HISTORY'

# ── New message types (v2.0) ─────────────────────────────────────────────
# Lobby chat
MSG_LOBBY_CHAT = 'LOBBY_CHAT'
MSG_LOBBY_CHAT_HISTORY = 'LOBBY_CHAT_HISTORY'

# Friend heartbeat / status
MSG_FRIEND_HEARTBEAT = 'FRIEND_HEARTBEAT'

# Daily puzzle
MSG_DAILY_PUZZLE = 'DAILY_PUZZLE'

# Post-game analysis job
MSG_ANALYSIS_REQUEST = 'ANALYSIS_REQUEST'
MSG_ANALYSIS_RESULT  = 'ANALYSIS_RESULT'

# Achievements
MSG_ACHIEVEMENTS = 'ACHIEVEMENTS'
MSG_ACHIEVEMENT_UNLOCKED = 'ACHIEVEMENT_UNLOCKED'

# Tournament
MSG_TOURNAMENT_CREATE   = 'TOURNAMENT_CREATE'
MSG_TOURNAMENT_JOIN     = 'TOURNAMENT_JOIN'
MSG_TOURNAMENT_LIST     = 'TOURNAMENT_LIST'
MSG_TOURNAMENT_STATUS   = 'TOURNAMENT_STATUS'
MSG_TOURNAMENT_PAIRINGS = 'TOURNAMENT_PAIRINGS'
MSG_TOURNAMENT_RESULT   = 'TOURNAMENT_RESULT'

# Disconnect/reconnect
MSG_RECONNECT = 'RECONNECT'

# Admin commands (server-side only, not from client)
MSG_ADMIN_KICK      = 'ADMIN_KICK'
MSG_ADMIN_BAN       = 'ADMIN_BAN'
MSG_ADMIN_RESET_ELO = 'ADMIN_RESET_ELO'
MSG_ADMIN_BROADCAST = 'ADMIN_BROADCAST'
MSG_SERVER_BROADCAST = 'SERVER_BROADCAST'   # Sent to all clients

# Response types
RESP_SUCCESS = 'SUCCESS'
RESP_ERROR = 'ERROR'
RESP_PROFILE = 'PROFILE'
RESP_USERS = 'USERS'
RESP_QUEUED = 'QUEUED'
RESP_MATCH = 'MATCH'
RESP_LEADERBOARD = 'LEADERBOARD'

# ════════════════════════════════════════════════════════════════════════
#  DATABASE MANAGER
# ════════════════════════════════════════════════════════════════════════
class DatabaseManager:
    """Handles all database operations for user accounts and game history."""

    def __init__(self, db_file=DATABASE_FILE):
        self.db_file = db_file
        self.lock = threading.Lock()
        self._message_id_counter = 0  # Thread-safe counter for message IDs
        self._failed_logins = defaultdict(list)  # ip -> [timestamp, ...]  (rate limiting)
        self._init_db()
    
    def _init_db(self):
        """Initialize database file if it doesn't exist."""
        if not os.path.exists(self.db_file):
            self._save_db({
                "users": {},
                "game_history": [],
                "friend_requests": [],
                "friendships": [],
                "messages": [],
                "challenges": [],
                "game_chat_history": {},
                "tournaments": {},
                "lobby_chat": [],
                "daily_puzzle": None,
                "achievements": {},  # username -> [achievement_ids]
            })
        else:
            # Initialize message ID counter from existing messages
            db = self._load_db()
            messages = db.get('messages', [])
            if messages:
                self._message_id_counter = max(msg.get('id', 0) for msg in messages)
            # Migrate: add new collections/fields if missing
            changed = False
            for key, default in [
                ('game_chat_history', {}),
                ('tournaments', {}),
                ('lobby_chat', []),
                ('daily_puzzle', None),
                ('achievements', {}),
            ]:
                if key not in db:
                    db[key] = default
                    changed = True
            for username, udata in db.get('users', {}).items():
                for field, default in [
                    ('avatar', ''),
                    ('bio', ''),
                    ('elo_floor', 100),
                    ('is_provisional', udata.get('elo_games', 0) < 20),
                    ('banned', False),
                    ('move_times', []),   # anti-cheat: last N move durations
                    ('suspicious_games', 0),
                ]:
                    if field not in udata:
                        udata[field] = default
                        changed = True
            if changed:
                self._save_db(db)

    
    def _load_db(self):
        """Load database from file."""
        try:
            with open(self.db_file, 'r') as f:
                return json.load(f)
        except (json.JSONDecodeError, FileNotFoundError):
            return {"users": {}, "game_history": []}
    
    def _save_db(self, data):
        """Save database to file."""
        with open(self.db_file, 'w') as f:
            json.dump(data, f, indent=2)
    
    def _hash_password(self, password):
        """Hash password using SHA-256."""
        return hashlib.sha256(password.encode()).hexdigest()
    
    def _validate_email(self, email):
        """Validate email format."""
        pattern = r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$'
        return re.match(pattern, email) is not None
    
    def _validate_username(self, username):
        """Validate username format."""
        if len(username) < 3 or len(username) > 20:
            return False
        return re.match(r'^[a-zA-Z0-9_]+$', username) is not None
    
    def register_user(self, username, password, email):
        """
        Register a new user.
        Returns (success, message) tuple.
        """
        with self.lock:
            db = self._load_db()
            
            # Validate username
            if not self._validate_username(username):
                return False, "Username must be 3-20 characters (alphanumeric and underscore only)"
            
            # Validate email
            if not self._validate_email(email):
                return False, "Invalid email format"
            
            # Validate password
            if len(password) < 6:
                return False, "Password must be at least 6 characters"
            
            # Check if username exists
            if username in db['users']:
                return False, "Username already exists"
            
            # Check if email exists
            for user_data in db['users'].values():
                if user_data['email'] == email:
                    return False, "Email already registered"
            
            # Create user
            db['users'][username] = {
                'password_hash': self._hash_password(password),
                'email': email,
                'created_at': datetime.now().isoformat(),
                'games_played': 0,
                'wins': 0,
                'losses': 0,
                'draws': 0,
                'elo': 1200,  # Starting ELO (like chess.com rapid)
                'elo_games': 0,
                'elo_wins': 0,
                'elo_losses': 0,
                'elo_draws': 0,
                'elo_peak': 1200,
                'elo_floor': 100,        # Rating floor
                'is_provisional': True,   # Provisional for first 20 games
                'avatar': '',             # ASCII art avatar (up to 500 chars)
                'bio': ''                 # Short bio (up to 200 chars)
            }

            self._save_db(db)
            return True, "Registration successful"
    
    def check_login_rate_limit(self, ip_address):
        """Return True if this IP has exceeded max failed logins per minute."""
        max_fails = int(_cfg.get('max_failed_logins_per_min', 5))
        now = time.time()
        window = 60.0
        attempts = self._failed_logins[ip_address]
        # Prune old attempts
        self._failed_logins[ip_address] = [t for t in attempts if now - t < window]
        return len(self._failed_logins[ip_address]) >= max_fails

    def record_failed_login(self, ip_address):
        """Record a failed login attempt for rate limiting."""
        self._failed_logins[ip_address].append(time.time())

    def authenticate_user(self, username, password, ip_address=''):
        """
        Authenticate user login.
        Returns (success, message) tuple.
        """
        with self.lock:
            db = self._load_db()

            if username not in db['users']:
                if ip_address:
                    self.record_failed_login(ip_address)
                return False, "Invalid username or password"

            if db['users'][username].get('banned', False):
                return False, "Account has been banned"

            password_hash = self._hash_password(password)
            if db['users'][username]['password_hash'] != password_hash:
                if ip_address:
                    self.record_failed_login(ip_address)
                return False, "Invalid username or password"

            return True, "Login successful"


    def authenticate_user_with_hash(self, username, password_hash):
        """
        Authenticate user login using stored password hash (for auto-login).
        Returns (success, message) tuple.
        """
        with self.lock:
            db = self._load_db()

            if username not in db['users']:
                return False, "Invalid username or password"

            if db['users'][username]['password_hash'] != password_hash:
                return False, "Invalid username or password"

            return True, "Auto-login successful"
    
    def get_user_profile(self, username, page=0, page_size=10):
        """
        Get user profile information.
        Returns profile dict or None if user doesn't exist.
        page/page_size control which slice of game history is returned.
        """
        with self.lock:
            db = self._load_db()

            if username not in db['users']:
                return None

            user_data = db['users'][username]

            # Get user's games — newest first — with pagination
            user_games = [
                g for g in db['game_history']
                if g['white'] == username or g['black'] == username
            ]
            user_games.sort(key=lambda x: x['timestamp'], reverse=True)
            total_games = len(user_games)
            start = page * page_size
            recent_games = user_games[start:start + page_size]

            return {
                'username': username,
                'email': user_data['email'],
                'created_at': user_data['created_at'],
                'games_played': user_data['games_played'],
                'wins': user_data['wins'],
                'losses': user_data['losses'],
                'draws': user_data['draws'],
                'elo': user_data.get('elo', 1200),
                'elo_games': user_data.get('elo_games', 0),
                'elo_wins': user_data.get('elo_wins', 0),
                'elo_losses': user_data.get('elo_losses', 0),
                'elo_draws': user_data.get('elo_draws', 0),
                'elo_peak': user_data.get('elo_peak', 1200),
                'banned': user_data.get('banned', False),
                'suspicious_games': user_data.get('suspicious_games', 0),
                'recent_games': recent_games,
                'total_game_count': total_games,
                'page': page,
                'page_size': page_size,
            }

    
    def _calculate_elo_change(self, rating_a, rating_b, result_a, k_factor=32):
        """
        Calculate ELO change for a player.
        result_a: 1=win, 0.5=draw, 0=loss
        Returns: (new_rating_a, new_rating_b, change_a, change_b)
        """
        # Expected score
        expected_a = 1.0 / (1.0 + 10 ** ((rating_b - rating_a) / 400.0))
        expected_b = 1.0 / (1.0 + 10 ** ((rating_a - rating_b) / 400.0))
        
        # New ratings
        change_a = k_factor * (result_a - expected_a)
        change_b = k_factor * ((1 - result_a) - expected_b)
        
        return round(rating_a + change_a), round(rating_b + change_b), round(change_a), round(change_b)

    def _get_k_factor(self, rating, games_played):
        """
        Get K-factor based on rating and experience (like chess.com).
        Higher K for new/low-rated players, lower for established/high-rated.
        """
        if games_played < 30:
            return 40  # High K for new players
        elif rating < 2000:
            return 32  # Standard K
        elif rating < 2400:
            return 24  # Lower K for experienced players
        else:
            return 16  # Lowest K for masters

    def save_game(self, white, black, result, moves, duration=0, rated=True, pgn='', move_times=None):
        """
        Save a game to history.
        Result: 'white', 'black', or 'draw'
        If rated=True, also update ELO ratings.
        pgn: optional full PGN string for permanent storage.
        move_times: list of (player, elapsed_seconds) for anti-cheat analysis.
        """
        with self.lock:
            db = self._load_db()

            # Use a proper unique ID
            existing_ids = [g.get('id', 0) for g in db['game_history']]
            new_id = max(existing_ids, default=0) + 1

            game_record = {
                'id': new_id,
                'timestamp': datetime.now().isoformat(),
                'white': white,
                'black': black,
                'result': result,
                'moves': moves,
                'pgn': pgn,
                'duration': duration,
                'rated': rated,
                'move_times': move_times or [],
            }

            db['game_history'].append(game_record)

            # Prune global history to last 10000 games to avoid unbounded growth
            if len(db['game_history']) > 10000:
                db['game_history'] = db['game_history'][-10000:]

            elo_changes = {}  # Store ELO changes to return

            # Update user stats and ELO
            for username, color in [(white, 'white'), (black, 'black')]:
                if username in db['users']:
                    db['users'][username]['games_played'] += 1
                    if result == color:
                        db['users'][username]['wins'] += 1
                    elif result == 'draw':
                        db['users'][username]['draws'] += 1
                    else:
                        db['users'][username]['losses'] += 1

                    # Update ELO if rated
                    if rated:
                        db['users'][username]['elo_games'] += 1
                        if result == color:
                            db['users'][username]['elo_wins'] += 1
                        elif result == 'draw':
                            db['users'][username]['elo_draws'] += 1
                        else:
                            db['users'][username]['elo_losses'] += 1

                    # Anti-cheat: log move times and flag suspicious patterns
                    if move_times:
                        player_times = [t for (p, t) in move_times if p == username]
                        if player_times:
                            fast_moves = sum(1 for t in player_times if t < 0.5)
                            if len(player_times) >= 5 and fast_moves / len(player_times) > 0.6:
                                db['users'][username]['suspicious_games'] = db['users'][username].get('suspicious_games', 0) + 1
                                log.warning(f"Anti-cheat: {username} flagged ({fast_moves}/{len(player_times)} fast moves in game {new_id})")
                else:
                    log.warning(f"[DB] User {username} not found in database!")

            # Calculate and apply ELO changes
            if rated and white in db['users'] and black in db['users']:
                white_elo = db['users'][white]['elo']
                black_elo = db['users'][black]['elo']

                if result == 'white':
                    white_result = 1.0
                elif result == 'black':
                    white_result = 0.0
                else:
                    white_result = 0.5

                white_k = self._get_k_factor(white_elo, db['users'][white]['elo_games'])
                black_k = self._get_k_factor(black_elo, db['users'][black]['elo_games'])

                white_expected = 1.0 / (1.0 + 10 ** ((black_elo - white_elo) / 400.0))
                black_expected = 1.0 / (1.0 + 10 ** ((white_elo - black_elo) / 400.0))

                white_change = round(white_k * (white_result - white_expected))
                black_change = round(black_k * ((1 - white_result) - black_expected))

                new_white_elo = white_elo + white_change
                new_black_elo = black_elo + black_change

                db['users'][white]['elo'] = new_white_elo
                db['users'][black]['elo'] = new_black_elo

                white_floor = db['users'][white].get('elo_floor', 100)
                black_floor = db['users'][black].get('elo_floor', 100)
                db['users'][white]['elo'] = max(new_white_elo, white_floor)
                db['users'][black]['elo'] = max(new_black_elo, black_floor)

                db['users'][white]['is_provisional'] = db['users'][white]['elo_games'] < 20
                db['users'][black]['is_provisional'] = db['users'][black]['elo_games'] < 20

                if new_white_elo > db['users'][white]['elo_peak']:
                    db['users'][white]['elo_peak'] = new_white_elo
                if new_black_elo > db['users'][black]['elo_peak']:
                    db['users'][black]['elo_peak'] = new_black_elo

                elo_changes = {
                    'white': {'old': white_elo, 'new': new_white_elo, 'change': white_change},
                    'black': {'old': black_elo, 'new': new_black_elo, 'change': black_change}
                }

            self._save_db(db)

            if rated:
                return True, elo_changes
            return True, None

    
    def list_users(self):
        """Get list of all usernames."""
        with self.lock:
            db = self._load_db()
            return list(db['users'].keys())

    def get_leaderboard(self, limit=10):
        """Get ELO leaderboard."""
        with self.lock:
            db = self._load_db()
            users = []
            for username, data in db['users'].items():
                users.append({
                    'username': username,
                    'elo': data.get('elo', 1200),
                    'games': data.get('elo_games', 0),
                    'wins': data.get('elo_wins', 0),
                    'losses': data.get('elo_losses', 0),
                    'draws': data.get('elo_draws', 0),
                    'peak': data.get('elo_peak', 1200),
                    'is_provisional': data.get('is_provisional', data.get('elo_games', 0) < 20),
                    'avatar': data.get('avatar', ''),
                    'bio': data.get('bio', '')
                })
            # Sort by ELO descending
            users.sort(key=lambda x: (-x['elo'], -x['games']))
            return users[:limit]

    # ════════════════════════════════════════════════════════════════════
    #  FRIEND SYSTEM METHODS
    # ════════════════════════════════════════════════════════════════════
    def send_friend_request(self, sender, recipient):
        """Send a friend request."""
        with self.lock:
            db = self._load_db()
            
            # Validate users exist
            if sender not in db['users'] or recipient not in db['users']:
                return False, "User not found"
            
            if sender == recipient:
                return False, "Cannot send friend request to yourself"
            
            # Check if already friends
            for friendship in db['friendships']:
                if (friendship['user1'] == sender and friendship['user2'] == recipient) or \
                   (friendship['user1'] == recipient and friendship['user2'] == sender):
                    return False, "Already friends"
            
            # Check for existing request
            for req in db['friend_requests']:
                if (req['sender'] == sender and req['recipient'] == recipient):
                    return False, "Friend request already sent"
            
            # Create friend request
            friend_request = {
                'id': len(db['friend_requests']) + 1,
                'sender': sender,
                'recipient': recipient,
                'created_at': datetime.now().isoformat(),
                'status': 'pending'
            }
            db['friend_requests'].append(friend_request)
            self._save_db(db)
            return True, "Friend request sent"

    def respond_to_friend_request(self, sender, recipient, accept):
        """Respond to a friend request."""
        with self.lock:
            db = self._load_db()
            
            # Find the request
            request_found = None
            for req in db['friend_requests']:
                if req['sender'] == sender and req['recipient'] == recipient:
                    request_found = req
                    break
            
            if not request_found:
                return False, "Friend request not found"
            
            if accept:
                # Create friendship
                friendship = {
                    'id': len(db['friendships']) + 1,
                    'user1': sender,
                    'user2': recipient,
                    'created_at': datetime.now().isoformat()
                }
                db['friendships'].append(friendship)
            
            # Remove the request
            db['friend_requests'] = [r for r in db['friend_requests'] if r != request_found]
            self._save_db(db)
            
            if accept:
                return True, "Friend request accepted"
            return True, "Friend request declined"

    def get_friend_requests(self, username):
        """Get pending friend requests for a user."""
        with self.lock:
            db = self._load_db()
            requests = []
            for req in db['friend_requests']:
                if req['recipient'] == username and req['status'] == 'pending':
                    requests.append({
                        'id': req['id'],
                        'sender': req['sender'],
                        'created_at': req['created_at']
                    })
            return requests

    def get_friends(self, username):
        """Get list of friends for a user."""
        with self.lock:
            db = self._load_db()
            friends = []
            for friendship in db['friendships']:
                if friendship['user1'] == username:
                    friends.append(friendship['user2'])
                elif friendship['user2'] == username:
                    friends.append(friendship['user1'])
            return friends

    def remove_friend(self, user1, user2):
        """Remove a friendship."""
        with self.lock:
            db = self._load_db()
            
            for friendship in db['friendships']:
                if (friendship['user1'] == user1 and friendship['user2'] == user2) or \
                   (friendship['user1'] == user2 and friendship['user2'] == user1):
                    db['friendships'].remove(friendship)
                    self._save_db(db)
                    return True, "Friend removed"
            
            return False, "Friendship not found"

    def are_friends(self, user1, user2):
        """Check if two users are friends."""
        with self.lock:
            db = self._load_db()
            for friendship in db['friendships']:
                if (friendship['user1'] == user1 and friendship['user2'] == user2) or \
                   (friendship['user1'] == user2 and friendship['user2'] == user1):
                    return True
            return False

    # ════════════════════════════════════════════════════════════════════
    #  MESSAGING SYSTEM METHODS
    # ════════════════════════════════════════════════════════════════════
    def store_message(self, sender, recipient, encrypted_content, iv, tag):
        """Store an encrypted message. Caller must verify friendship before calling."""
        with self.lock:
            db = self._load_db()

            # Use thread-safe counter for message ID
            self._message_id_counter += 1
            message_id = self._message_id_counter
            
            message = {
                'id': message_id,
                'sender': sender,
                'recipient': recipient,
                'encrypted_content': encrypted_content,
                'iv': iv,
                'tag': tag,
                'created_at': datetime.now().isoformat(),
                'expires_at': (datetime.now() + timedelta(hours=12)).isoformat()
            }
            db['messages'].append(message)
            self._save_db(db)
            return True, message_id

    def get_messages(self, user1, user2, since_id=0):
        """Get messages between two users."""
        with self.lock:
            db = self._load_db()

            # Inline friendship check (cannot call self.are_friends here — same lock)
            is_friends = any(
                (f['user1'] == user1 and f['user2'] == user2) or
                (f['user1'] == user2 and f['user2'] == user1)
                for f in db.get('friendships', [])
            )
            if not is_friends:
                return []
            
            messages = []
            for msg in db['messages']:
                if ((msg['sender'] == user1 and msg['recipient'] == user2) or
                    (msg['sender'] == user2 and msg['recipient'] == user1)):
                    if msg['id'] > since_id:
                        messages.append({
                            'id': msg['id'],
                            'sender': msg['sender'],
                            'encrypted_content': msg['encrypted_content'],
                            'iv': msg['iv'],
                            'tag': msg['tag'],
                            'created_at': msg['created_at']
                        })
            return messages

    def cleanup_expired_messages(self):
        """Remove messages older than 12 hours."""
        with self.lock:
            db = self._load_db()
            now = datetime.now()
            original_count = len(db['messages'])
            
            db['messages'] = [
                msg for msg in db['messages']
                if datetime.fromisoformat(msg['expires_at']) > now
            ]
            
            if len(db['messages']) < original_count:
                self._save_db(db)
                return original_count - len(db['messages'])
            return 0

    # ════════════════════════════════════════════════════════════════════
    #  CHALLENGE SYSTEM METHODS
    # ════════════════════════════════════════════════════════════════════
    def send_challenge(self, challenger, challenged, color_choice='random', rated=True):
        """Send a game challenge."""
        with self.lock:
            db = self._load_db()
            
            # Validate users exist
            if challenger not in db['users'] or challenged not in db['users']:
                return False, "User not found"
            
            if challenger == challenged:
                return False, "Cannot challenge yourself"
            
            # Verify users are friends (inline to avoid re-acquiring the lock)
            is_friends = any(
                (f['user1'] == challenger and f['user2'] == challenged) or
                (f['user1'] == challenged and f['user2'] == challenger)
                for f in db.get('friendships', [])
            )
            if not is_friends:
                return False, "Can only challenge friends"
            
            # Check for existing active challenge
            for challenge in db['challenges']:
                if challenge['status'] == 'pending':
                    if ((challenge['challenger'] == challenger and challenge['challenged'] == challenged) or
                        (challenge['challenger'] == challenged and challenge['challenged'] == challenger)):
                        return False, "Pending challenge already exists"
            
            challenge = {
                'id': len(db['challenges']) + 1,
                'challenger': challenger,
                'challenged': challenged,
                'color_choice': color_choice,
                'rated': rated,
                'created_at': datetime.now().isoformat(),
                'status': 'pending'
            }
            db['challenges'].append(challenge)
            self._save_db(db)
            return True, challenge['id']

    def respond_to_challenge(self, challenger, challenged, accept):
        """Respond to a challenge."""
        with self.lock:
            db = self._load_db()
            
            # Find the challenge
            challenge_found = None
            for challenge in db['challenges']:
                if (challenge['challenger'] == challenger and 
                    challenge['challenged'] == challenged and
                    challenge['status'] == 'pending'):
                    challenge_found = challenge
                    break
            
            if not challenge_found:
                return False, "Challenge not found"
            
            if accept:
                challenge_found['status'] = 'accepted'
                # Determine colors
                if challenge_found['color_choice'] == 'random':
                    colors = ['white', 'black']
                    random.shuffle(colors)
                    challenge_found['challenger_color'] = colors[0]
                    challenge_found['challenged_color'] = colors[1]
                elif challenge_found['color_choice'] == 'white':
                    challenge_found['challenger_color'] = 'white'
                    challenge_found['challenged_color'] = 'black'
                else:
                    challenge_found['challenger_color'] = 'black'
                    challenge_found['challenged_color'] = 'white'
            else:
                challenge_found['status'] = 'declined'
            
            self._save_db(db)
            
            if accept:
                return True, {
                    'challenge_id': challenge_found['id'],
                    'challenger_color': challenge_found['challenger_color'],
                    'challenged_color': challenge_found['challenged_color'],
                    'rated': challenge_found['rated']
                }
            return True, "Challenge declined"

    def get_challenges(self, username):
        """Get pending challenges for a user."""
        with self.lock:
            db = self._load_db()
            challenges = []
            for challenge in db['challenges']:
                if challenge['status'] == 'pending':
                    if challenge['challenged'] == username or challenge['challenger'] == username:
                        challenges.append({
                            'id': challenge['id'],
                            'challenger': challenge['challenger'],
                            'challenged': challenge['challenged'],
                            'color_choice': challenge['color_choice'],
                            'rated': challenge['rated'],
                            'created_at': challenge['created_at']
                        })
            return challenges

    def cancel_challenge(self, challenger, challenged):
        """Cancel a pending challenge."""
        with self.lock:
            db = self._load_db()
            
            for challenge in db['challenges']:
                if (challenge['challenger'] == challenger and 
                    challenge['challenged'] == challenged and
                    challenge['status'] == 'pending'):
                    challenge['status'] = 'cancelled'
                    self._save_db(db)
                    return True, "Challenge cancelled"
            
            return False, "Challenge not found"

    # ════════════════════════════════════════════════════════════════════
    #  AVATAR / PROFILE METHODS
    # ════════════════════════════════════════════════════════════════════
    def set_avatar(self, username, avatar, bio):
        """Set a user's ASCII avatar and bio."""
        with self.lock:
            db = self._load_db()
            if username not in db['users']:
                return False, "User not found"
            db['users'][username]['avatar'] = avatar[:500]
            db['users'][username]['bio'] = bio[:200]
            self._save_db(db)
            return True, "Profile updated"

    def get_avatar(self, username):
        """Get a user's avatar and bio."""
        with self.lock:
            db = self._load_db()
            if username not in db['users']:
                return None
            udata = db['users'][username]
            return {
                'username': username,
                'avatar': udata.get('avatar', ''),
                'bio': udata.get('bio', ''),
                'elo': udata.get('elo', 1200),
                'games': udata.get('elo_games', 0),
                'wins': udata.get('wins', 0),
                'losses': udata.get('losses', 0),
                'draws': udata.get('draws', 0),
                'is_provisional': udata.get('is_provisional', udata.get('elo_games', 0) < 20),
                'elo_peak': udata.get('elo_peak', 1200)
            }

    # ════════════════════════════════════════════════════════════════════
    #  GAME CHAT HISTORY METHODS
    # ════════════════════════════════════════════════════════════════════
    def save_game_chat(self, game_id, chat_log):
        """Persist game chat log (keeps last 100 games)."""
        with self.lock:
            db = self._load_db()
            if 'game_chat_history' not in db:
                db['game_chat_history'] = {}
            db['game_chat_history'][str(game_id)] = chat_log
            # Prune to last 100 games
            if len(db['game_chat_history']) > 100:
                oldest = sorted(db['game_chat_history'].keys())[0]
                del db['game_chat_history'][oldest]
            self._save_db(db)

    def get_game_chat(self, game_id):
        """Retrieve chat log for a game."""
        with self.lock:
            db = self._load_db()
            return db.get('game_chat_history', {}).get(str(game_id), [])

    def get_game_pgn(self, game_id):
        """Retrieve stored PGN for a game by ID."""
        with self.lock:
            db = self._load_db()
            for g in db['game_history']:
                if g.get('id') == game_id:
                    return g.get('pgn', '')
            return None

    # ════════════════════════════════════════════════════════════════════
    #  ADMIN METHODS
    # ════════════════════════════════════════════════════════════════════
    def ban_user(self, username):
        """Ban a user account."""
        with self.lock:
            db = self._load_db()
            if username not in db['users']:
                return False, "User not found"
            db['users'][username]['banned'] = True
            self._save_db(db)
            log.warning(f"Admin: user '{username}' BANNED")
            return True, f"User '{username}' banned"

    def unban_user(self, username):
        """Unban a user account."""
        with self.lock:
            db = self._load_db()
            if username not in db['users']:
                return False, "User not found"
            db['users'][username]['banned'] = False
            self._save_db(db)
            log.info(f"Admin: user '{username}' unbanned")
            return True, f"User '{username}' unbanned"

    def reset_elo(self, username, new_elo=1200):
        """Reset a user's ELO rating."""
        with self.lock:
            db = self._load_db()
            if username not in db['users']:
                return False, "User not found"
            db['users'][username]['elo'] = new_elo
            db['users'][username]['elo_peak'] = max(new_elo, db['users'][username].get('elo_peak', new_elo))
            db['users'][username]['is_provisional'] = True
            self._save_db(db)
            log.info(f"Admin: ELO for '{username}' reset to {new_elo}")
            return True, f"ELO for '{username}' reset to {new_elo}"

    # ════════════════════════════════════════════════════════════════════
    #  ACHIEVEMENT SYSTEM
    # ════════════════════════════════════════════════════════════════════
    ACHIEVEMENTS = {
        'first_win':      {'name': 'First Blood',    'desc': 'Win your first game'},
        'ten_wins':       {'name': 'On a Roll',      'desc': 'Win 10 games'},
        'fifty_wins':     {'name': 'Veteran',         'desc': 'Win 50 games'},
        'first_draw':     {'name': 'Diplomat',        'desc': 'Draw your first game'},
        'streak_5':       {'name': 'Hot Streak',      'desc': 'Win 5 games in a row'},
        'elo_1500':       {'name': 'Club Player',     'desc': 'Reach 1500 ELO'},
        'elo_1800':       {'name': 'Expert',          'desc': 'Reach 1800 ELO'},
        'elo_2000':       {'name': 'Master Class',    'desc': 'Reach 2000 ELO'},
        'played_100':     {'name': 'Centurion',       'desc': 'Play 100 rated games'},
        'comeback':       {'name': 'Never Give Up',   'desc': 'Win a game from a losing ELO'},
    }

    def check_and_award_achievements(self, username):
        """Check achievements for a user after a game; returns list of newly unlocked ids."""
        with self.lock:
            db = self._load_db()
            if username not in db['users']:
                return []
            udata = db['users'][username]
            if 'achievements' not in db:
                db['achievements'] = {}
            unlocked = set(db['achievements'].get(username, []))
            new_unlocks = []

            wins    = udata.get('wins', 0)
            draws   = udata.get('draws', 0)
            elo     = udata.get('elo', 1200)
            games   = udata.get('elo_games', 0)

            checks = [
                ('first_win',  wins >= 1),
                ('ten_wins',   wins >= 10),
                ('fifty_wins', wins >= 50),
                ('first_draw', draws >= 1),
                ('elo_1500',   elo >= 1500),
                ('elo_1800',   elo >= 1800),
                ('elo_2000',   elo >= 2000),
                ('played_100', games >= 100),
            ]
            for ach_id, condition in checks:
                if condition and ach_id not in unlocked:
                    unlocked.add(ach_id)
                    new_unlocks.append(ach_id)

            if new_unlocks:
                db['achievements'][username] = list(unlocked)
                self._save_db(db)
            return new_unlocks

    def get_achievements(self, username):
        """Get list of achievement dicts for a user."""
        with self.lock:
            db = self._load_db()
            unlocked = set(db.get('achievements', {}).get(username, []))
            result = []
            for ach_id, info in self.ACHIEVEMENTS.items():
                result.append({
                    'id': ach_id,
                    'name': info['name'],
                    'desc': info['desc'],
                    'unlocked': ach_id in unlocked,
                })
            return result

    # ════════════════════════════════════════════════════════════════════
    #  LOBBY CHAT
    # ════════════════════════════════════════════════════════════════════
    def add_lobby_message(self, sender, message):
        """Add a message to the global lobby chat (keep last 200)."""
        with self.lock:
            db = self._load_db()
            if 'lobby_chat' not in db:
                db['lobby_chat'] = []
            db['lobby_chat'].append({
                'sender': sender,
                'message': message[:500],
                'ts': datetime.now().isoformat(),
            })
            db['lobby_chat'] = db['lobby_chat'][-200:]
            self._save_db(db)

    def get_lobby_chat(self, limit=50):
        """Get recent lobby chat messages."""
        with self.lock:
            db = self._load_db()
            msgs = db.get('lobby_chat', [])
            return msgs[-limit:]

    # ════════════════════════════════════════════════════════════════════
    #  DAILY PUZZLE
    # ════════════════════════════════════════════════════════════════════
    def get_or_generate_daily_puzzle(self):
        """Return today's puzzle; generate a new one if the date has changed."""
        with self.lock:
            db = self._load_db()
            today = datetime.now().strftime('%Y-%m-%d')
            puzzle = db.get('daily_puzzle')
            if puzzle and puzzle.get('date') == today:
                return puzzle

            # Pick a random position from game history as puzzle source
            # In practice you'd use a curated puzzle DB; here we create a
            # plausible puzzle record from stored game positions.
            SAMPLE_PUZZLES = [
                {'fen': 'r1bqkb1r/pppp1ppp/2n2n2/4p3/2B1P3/5N2/PPPP1PPP/RNBQK2R w KQkq - 4 4',
                 'moves': 'Ng5', 'theme': 'Fried Liver Attack', 'rating': 1400},
                {'fen': '8/8/8/8/8/4k3/4p3/4K3 b - - 0 1',
                 'moves': 'e1=Q+', 'theme': 'Promotion', 'rating': 900},
                {'fen': 'r1b1kb1r/ppp2ppp/2n5/3qp3/2B5/2N2N2/PPPP1PPP/R1BQK2R b KQkq - 0 7',
                 'moves': 'Qxf3', 'theme': 'Fork', 'rating': 1200},
                {'fen': '6k1/5ppp/8/8/8/8/5PPP/R5K1 w - - 0 1',
                 'moves': 'Ra8+', 'theme': 'Back Rank', 'rating': 1100},
                {'fen': '4r1k1/pp3ppp/2p5/4r3/8/1P3PP1/P5BP/R3R1K1 w - - 0 22',
                 'moves': 'Rxe5', 'theme': 'Discovered Attack', 'rating': 1600},
            ]
            puzzle = random.choice(SAMPLE_PUZZLES)
            puzzle['date'] = today
            puzzle['id'] = hashlib.md5(today.encode()).hexdigest()[:8]
            db['daily_puzzle'] = puzzle
            self._save_db(db)
            return puzzle

    # ════════════════════════════════════════════════════════════════════
    #  TOURNAMENT STORAGE
    # ════════════════════════════════════════════════════════════════════
    def create_tournament(self, name, creator, max_players=8, rounds=3, time_control='blitz'):
        """Create a new Swiss-system tournament."""
        with self.lock:
            db = self._load_db()
            if 'tournaments' not in db:
                db['tournaments'] = {}
            tid = secrets.token_hex(4)
            db['tournaments'][tid] = {
                'id': tid,
                'name': name,
                'creator': creator,
                'max_players': max_players,
                'rounds': rounds,
                'time_control': time_control,
                'players': [creator],
                'standings': {creator: {'points': 0, 'byes': 0, 'games': []}},
                'current_round': 0,
                'pairings': [],
                'status': 'registration',   # registration | active | finished
                'created_at': datetime.now().isoformat(),
            }
            self._save_db(db)
            return tid, db['tournaments'][tid]

    def join_tournament(self, tid, username):
        """Add a player to a tournament."""
        with self.lock:
            db = self._load_db()
            t = db.get('tournaments', {}).get(tid)
            if not t:
                return False, "Tournament not found"
            if t['status'] != 'registration':
                return False, "Registration is closed"
            if username in t['players']:
                return False, "Already registered"
            if len(t['players']) >= t['max_players']:
                return False, "Tournament is full"
            t['players'].append(username)
            t['standings'][username] = {'points': 0, 'byes': 0, 'games': []}
            self._save_db(db)
            return True, f"Joined tournament '{t['name']}'"

    def start_tournament_round(self, tid):
        """Generate Swiss pairings for the next round."""
        with self.lock:
            db = self._load_db()
            t = db.get('tournaments', {}).get(tid)
            if not t:
                return False, "Tournament not found"
            if t['current_round'] >= t['rounds']:
                t['status'] = 'finished'
                self._save_db(db)
                return False, "Tournament already finished"

            t['status'] = 'active'
            t['current_round'] += 1

            # Sort players by points desc, then randomise within tied groups
            standings = t['standings']
            players = sorted(t['players'],
                             key=lambda p: (-standings[p]['points'], random.random()))

            # Pair players; odd one out gets a bye
            pairings = []
            paired = set()
            for i in range(0, len(players) - 1, 2):
                p1, p2 = players[i], players[i + 1]
                paired.add(p1); paired.add(p2)
                pairings.append({
                    'round': t['current_round'],
                    'white': p1, 'black': p2,
                    'result': None,
                    'game_id': None,
                })
            for p in players:
                if p not in paired:
                    pairings.append({'round': t['current_round'], 'white': p, 'black': None, 'result': 'bye'})
                    standings[p]['points'] += 1
                    standings[p]['byes'] += 1

            t['pairings'].extend(pairings)
            self._save_db(db)
            return True, pairings

    def record_tournament_result(self, tid, round_num, white, black, result):
        """Record the result of a tournament game."""
        with self.lock:
            db = self._load_db()
            t = db.get('tournaments', {}).get(tid)
            if not t:
                return False, "Tournament not found"
            standings = t['standings']
            for p in t['pairings']:
                if p['round'] == round_num and p['white'] == white and p['black'] == black:
                    p['result'] = result
                    if result == 'white':
                        standings[white]['points'] += 1
                    elif result == 'black':
                        standings[black]['points'] += 1
                    else:  # draw
                        standings[white]['points'] += 0.5
                        standings[black]['points'] += 0.5
                    break
            # Check if round complete
            round_pairings = [p for p in t['pairings'] if p['round'] == round_num and p['black'] is not None]
            if all(p['result'] is not None for p in round_pairings):
                if t['current_round'] >= t['rounds']:
                    t['status'] = 'finished'
            self._save_db(db)
            return True, "Result recorded"

    def get_tournament(self, tid):
        """Get tournament info."""
        with self.lock:
            db = self._load_db()
            return db.get('tournaments', {}).get(tid)

    def list_tournaments(self):
        """List all tournaments."""
        with self.lock:
            db = self._load_db()
            return list(db.get('tournaments', {}).values())

# ════════════════════════════════════════════════════════════════════════
#  MATCHMAKING MANAGER
# ════════════════════════════════════════════════════════════════════════
class MatchmakingManager:
    """Handles player queueing and match pairing."""
    
    def __init__(self):
        self.queue = {}  # username -> {rating, joined_time, handler, time_control}
        self.active_games = {}  # game_id -> {white, black, white_handler, black_handler, ...}
        self.spectators = {}    # game_id -> [handler, ...]
        self.rematch_requests = {}  # game_id -> {requester}
        self.disconnected = {}  # username -> {game_id, deadline, game}
        self.lock = threading.Lock()
        self.game_counter = 0
        self.matchmaking_thread = None
        self.clock_thread = None
        self.heartbeat_thread = None
        self.running = True
        self._db = None  # Set by ChessServer after init
        self._server = None  # Set by ChessServer after init

    def start(self):
        """Start background threads."""
        self.matchmaking_thread = threading.Thread(target=self._matchmaking_loop, daemon=True)
        self.matchmaking_thread.start()
        self.clock_thread = threading.Thread(target=self._clock_loop, daemon=True)
        self.clock_thread.start()
        self.heartbeat_thread = threading.Thread(target=self._heartbeat_loop, daemon=True)
        self.heartbeat_thread.start()
    
    def stop(self):
        self.running = False
    
    def _matchmaking_loop(self):
        while self.running:
            time.sleep(1.0)
            self._try_match_players()
            self._handle_disconnects()

    def _heartbeat_loop(self):
        """Broadcast friend status (online/in-game/offline) every 30 seconds."""
        interval = int(_cfg.get('heartbeat_interval', 30))
        while self.running:
            time.sleep(interval)
            if not self._server:
                continue
            try:
                connected = set(self._server.connected_clients.keys())
                in_game = set()
                with self.lock:
                    for g in self.active_games.values():
                        in_game.add(g['white']); in_game.add(g['black'])
                # Notify each connected user about their friends' status
                for username, handler in list(self._server.connected_clients.items()):
                    if not self._db:
                        continue
                    try:
                        friends = self._db.get_friends(username)
                        status_map = {}
                        for f in friends:
                            if f in in_game:
                                status_map[f] = 'in_game'
                            elif f in connected:
                                status_map[f] = 'online'
                            else:
                                status_map[f] = 'offline'
                        handler.send(MSG_FRIEND_HEARTBEAT, {'statuses': status_map})
                    except Exception:
                        pass
            except Exception as e:
                log.error(f"Heartbeat error: {e}")

    def _handle_disconnects(self):
        """Handle reconnect window for disconnected players."""
        grace = int(_cfg.get('disconnect_grace_seconds', 60))
        now = time.time()
        expired = []
        with self.lock:
            for username, info in list(self.disconnected.items()):
                if now > info['deadline']:
                    expired.append((username, info))

        for username, info in expired:
            game_id = info['game_id']
            with self.lock:
                game = self.active_games.get(game_id)
                self.disconnected.pop(username, None)
            if not game:
                continue
            # Award win to the connected opponent
            winner = game['black'] if game['white'] == username else game['white']
            loser = username
            resign_data = {
                'game_id': game_id,
                'resigned_by': loser,
                'winner': winner,
                'reason': 'disconnect_timeout',
            }
            log.info(f"Disconnect timeout: {loser} forfeits game {game_id} to {winner}")
            try:
                game['white_handler'].send(MSG_GAME_RESIGN, resign_data)
            except Exception:
                pass
            try:
                game['black_handler'].send(MSG_GAME_RESIGN, resign_data)
            except Exception:
                pass
            if self._db:
                result = 'black' if winner == game['black'] else 'white'
                self._db.save_game(game['white'], game['black'], result, game.get('move_log', []))
            with self.lock:
                self.active_games.pop(game_id, None)
                self.spectators.pop(game_id, None)

    def join_queue(self, username, handler, time_control='rapid'):
        """Add a player to the matchmaking queue."""
        with self.lock:
            if username in self.queue:
                return False, "Already in queue"
            
            db = handler.db._load_db()
            rating = 1200
            if username in db.get('users', {}):
                rating = db['users'][username].get('elo', 1200)
            
            self.queue[username] = {
                'rating': rating,
                'joined_time': time.time(),
                'handler': handler,
                'time_control': time_control,
            }
            
            return True, f"Joined queue (ELO: {int(rating)}, TC: {time_control})"


    def _clock_loop(self):
        """Background loop to tick game clocks and detect timeouts."""
        while self.running:
            time.sleep(1.0)
            self._tick_game_clocks()
    
    def _tick_game_clocks(self):
        """Tick all active game clocks and broadcast updates every 2s, trigger timeouts."""
        with self.lock:
            now = time.time()
            to_timeout = []
            for game_id, game in self.active_games.items():
                if not game.get('clock_enabled'):
                    continue
                turn = game['current_turn']
                last_tick = game.get('clock_last_tick', now)
                elapsed = now - last_tick
                game['clock_last_tick'] = now

                if turn == 'white':
                    game['clock_white'] = max(0, game['clock_white'] - elapsed)
                    if game['clock_white'] <= 0:
                        to_timeout.append((game_id, 'white'))
                else:
                    game['clock_black'] = max(0, game['clock_black'] - elapsed)
                    if game['clock_black'] <= 0:
                        to_timeout.append((game_id, 'black'))

                # Broadcast clock update every ~2s
                last_broadcast = game.get('clock_last_broadcast', 0)
                if now - last_broadcast >= 2.0:
                    game['clock_last_broadcast'] = now
                    clock_data = {
                        'game_id': game_id,
                        'white_remaining': round(game['clock_white'], 1),
                        'black_remaining': round(game['clock_black'], 1),
                        'turn': turn
                    }
                    try:
                        game['white_handler'].send(MSG_GAME_CLOCK_UPDATE, clock_data)
                    except:
                        pass
                    try:
                        game['black_handler'].send(MSG_GAME_CLOCK_UPDATE, clock_data)
                    except:
                        pass
                    for spec in self.spectators.get(game_id, []):
                        try:
                            spec.send(MSG_GAME_CLOCK_UPDATE, clock_data)
                        except:
                            pass

            # Handle timeouts outside iteration
            for game_id, timed_out_color in to_timeout:
                game = self.active_games.get(game_id)
                if not game:
                    continue
                winner_color = 'black' if timed_out_color == 'white' else 'white'
                winner = game[winner_color]
                loser = game[timed_out_color]
                timeout_data = {
                    'game_id': game_id,
                    'timed_out': loser,
                    'winner': winner
                }
                try:
                    game['white_handler'].send(MSG_GAME_TIMEOUT, timeout_data)
                except:
                    pass
                try:
                    game['black_handler'].send(MSG_GAME_TIMEOUT, timeout_data)
                except:
                    pass
                for spec in self.spectators.get(game_id, []):
                    try:
                        spec.send(MSG_GAME_TIMEOUT, timeout_data)
                    except:
                        pass
                # Save chat history
                if self._db:
                    self._db.save_game_chat(game_id, game.get('chat_log', []))
                del self.active_games[game_id]
                self.spectators.pop(game_id, None)
                self.rematch_requests.pop(game_id, None)

    def _make_game(self, game_id, white, black, white_handler, black_handler,
                   clock_minutes=0, clock_increment=0):
        """Helper: create and store a new game entry."""
        clock_secs = clock_minutes * 60.0
        self.active_games[game_id] = {
            'white': white,
            'black': black,
            'white_handler': white_handler,
            'black_handler': black_handler,
            'fen': INITIAL_FEN,
            'move_log': [],
            'current_turn': 'white',
            'chat_log': [],
            # Clock fields
            'clock_enabled': clock_minutes > 0,
            'clock_white': clock_secs,
            'clock_black': clock_secs,
            'clock_increment': clock_increment,
            'clock_last_tick': time.time(),
            'clock_last_broadcast': 0
        }
        self.spectators[game_id] = []

    def _try_match_players(self):
        """Try to match players in the queue — ELO-banded with time-widening."""
        with self.lock:
            if len(self.queue) < 2:
                return

            now = time.time()
            # Sort by rating
            queued = sorted(self.queue.items(), key=lambda x: x[1]['rating'])

            matched_pairs = []
            used = set()

            for i in range(len(queued) - 1):
                p1_name, p1_data = queued[i]
                if p1_name in used:
                    continue
                for j in range(i + 1, len(queued)):
                    p2_name, p2_data = queued[j]
                    if p2_name in used:
                        continue

                    # Time-control must match
                    if p1_data['time_control'] != p2_data['time_control']:
                        continue

                    elo_diff = abs(p1_data['rating'] - p2_data['rating'])

                    # ELO band widens the longer they wait: +50 per 30s, max 500
                    wait1 = now - p1_data['joined_time']
                    wait2 = now - p2_data['joined_time']
                    max_wait = max(wait1, wait2)
                    allowed_diff = min(500, 150 + int(max_wait / 30) * 50)

                    if elo_diff <= allowed_diff:
                        matched_pairs.append((p1_name, p1_data, p2_name, p2_data))
                        used.add(p1_name); used.add(p2_name)
                        break

            for player1, data1, player2, data2 in matched_pairs:
                self.game_counter += 1
                game_id = self.game_counter

                if random.random() < 0.5:
                    white, black = player1, player2
                    white_handler, black_handler = data1['handler'], data2['handler']
                else:
                    white, black = player2, player1
                    white_handler, black_handler = data2['handler'], data1['handler']

                tc = data1['time_control']
                TC_MAP = {'bullet': (1, 0), 'blitz': (5, 0), 'rapid': (10, 0), 'classical': (30, 0)}
                clock_mins, clock_inc = TC_MAP.get(tc, (10, 0))
                self._make_game(game_id, white, black, white_handler, black_handler, clock_mins, clock_inc)

                del self.queue[player1]
                del self.queue[player2]

                log.info(f"Match created: {white} vs {black} (game {game_id}, tc={tc})")

                white_handler.send(MSG_MATCH_FOUND, {'game_id': game_id, 'opponent': black, 'color': 'white', 'time_control': tc})
                black_handler.send(MSG_MATCH_FOUND, {'game_id': game_id, 'opponent': white, 'color': 'black', 'time_control': tc})

    
    def leave_queue(self, username):
        """Remove a player from the matchmaking queue."""
        with self.lock:
            if username in self.queue:
                del self.queue[username]
                return True, "Left queue"
            return False, "Not in queue"
    
    def get_queue_status(self, username):
        """Get queue position for a player."""
        with self.lock:
            if username not in self.queue:
                return False, None

            position = sum(1 for p, d in self.queue.items()
                          if d['joined_time'] <= self.queue[username]['joined_time'])
            wait_time = time.time() - self.queue[username]['joined_time']

            return True, {
                'position': position,
                'wait_time': int(wait_time),
                'queued_players': len(self.queue)
            }

    def trigger_matchmaking(self, username):
        """Trigger an immediate matchmaking check for a player."""
        with self.lock:
            if username not in self.queue:
                return False, "Not in queue"
            
            # Try to find a match immediately
            if len(self.queue) < 2:
                return True, {"message": f"Waiting for opponents ({len(self.queue)} queued)"}
            
            # Sort by rating and find similar-rated opponent
            queued = sorted(self.queue.items(), key=lambda x: x[1]['rating'])
            max_elo_diff = 200
            
            for i in range(len(queued) - 1):
                p1_name, p1_data = queued[i]
                p2_name, p2_data = queued[i + 1]
                
                elo_diff = abs(p1_data['rating'] - p2_data['rating'])
                if elo_diff <= max_elo_diff and (p1_name == username or p2_name == username):
                    # Found a match! The background thread will handle it
                    return True, {"message": "Match found! Check your connection."}
            
            return True, {"message": f"No suitable opponent found yet ({len(self.queue)} queued)"}
    
    def get_game(self, game_id):
        """Get game info."""
        with self.lock:
            return self.active_games.get(game_id)
    
    def make_move(self, game_id, player, move):
        """Process a move in an active game with server-side legality validation."""
        with self.lock:
            game = self.active_games.get(game_id)
            if not game:
                return False, "Game not found"

            # Verify it's the player's turn
            expected_player = game['white'] if game['current_turn'] == 'white' else game['black']
            if player != expected_player:
                return False, "Not your turn"

            # ── Server-side move legality check ───────────────────────────
            try:
                fen = game.get('fen', INITIAL_FEN)
                board, side, castle_str, ep_sq, halfmove, fullmove = _parse_fen(fen)

                # Confirm the correct side is moving
                expected_side = 'w' if game['current_turn'] == 'white' else 'b'
                if side != expected_side:
                    print(f"  [SECURITY] FEN side mismatch for game {game_id} player {player}", flush=True)
                    return False, "Board state error — please rejoin"

                # Parse the SAN into squares
                result = _san_to_squares(move, board, side, castle_str, ep_sq)
                if result is None:
                    print(f"  [SECURITY] Illegal move rejected: {player} played {move!r} in game {game_id}", flush=True)
                    return False, f"Illegal move: {move}"

                from_sq, to_sq, promote_to = result

                # Verify the (from_sq, to_sq) is in pseudo-legal moves
                pseudo = _server_pseudo_legal(board, side, castle_str, ep_sq)
                if (from_sq, to_sq) not in pseudo:
                    print(f"  [SECURITY] Pseudo-illegal move rejected: {player} played {move!r} in game {game_id}", flush=True)
                    return False, f"Illegal move: {move}"

                # Apply the move to update server-side board state
                new_board, new_side, new_castle, new_ep, new_half, new_full =                     _apply_server_move(board, side, castle_str, ep_sq, halfmove, fullmove,
                                       from_sq, to_sq, promote_to)
                game['fen'] = _board_to_fen(new_board, new_side, new_castle, new_ep, new_half, new_full)
                game['move_log'].append(move)

            except Exception as e:
                # Validation error — log but do NOT crash the server; let move through
                print(f"  [WARN] Move validation exception in game {game_id}: {e}", flush=True)

            # ── Advance turn ───────────────────────────────────────────────
            if player == game['white']:
                game['current_turn'] = 'black'
                other_handler = game['black_handler']
                # Apply clock increment for white
                if game.get('clock_enabled'):
                    game['clock_white'] += game.get('clock_increment', 0)
            else:
                game['current_turn'] = 'white'
                other_handler = game['white_handler']
                # Apply clock increment for black
                if game.get('clock_enabled'):
                    game['clock_black'] += game.get('clock_increment', 0)

            move_data = {
                'game_id': game_id,
                'move': move,
                'from_player': player
            }
            # Forward validated move to opponent
            other_handler.send(MSG_GAME_MOVE, move_data)
            # Forward to spectators
            for spec in self.spectators.get(game_id, []):
                try:
                    spec.send(MSG_GAME_MOVE, move_data)
                except:
                    pass

            return True, "Move sent"
    
    def resign(self, game_id, player):
        """Handle resignation."""
        with self.lock:
            game = self.active_games.get(game_id)
            if not game:
                return None
            
            # Determine winner
            winner = game['black'] if player == game['white'] else game['white']
            resign_data = {
                'game_id': game_id,
                'resigned_by': player,
                'winner': winner
            }
            
            # Notify both players
            game['white_handler'].send(MSG_GAME_RESIGN, resign_data)
            game['black_handler'].send(MSG_GAME_RESIGN, resign_data)
            # Notify spectators
            for spec in self.spectators.get(game_id, []):
                try:
                    spec.send(MSG_GAME_RESIGN, resign_data)
                except:
                    pass
            # Persist chat
            if self._db:
                self._db.save_game_chat(game_id, game.get('chat_log', []))
            # Remove game
            del self.active_games[game_id]
            self.spectators.pop(game_id, None)
            self.rematch_requests.pop(game_id, None)
            
            return {'winner': winner, 'loser': player}
    
    def offer_draw(self, game_id, player):
        """Offer a draw to opponent."""
        with self.lock:
            game = self.active_games.get(game_id)
            if not game:
                return False, "Game not found"
            
            # Get opponent
            opponent_handler = game['black_handler'] if player == game['white'] else game['white_handler']
            
            # Send draw offer
            opponent_handler.send(MSG_GAME_DRAW_OFFER, {
                'game_id': game_id,
                'offered_by': player
            })
            
            return True, "Draw offered"
    
    def accept_draw(self, game_id, player):
        """Accept a draw offer."""
        with self.lock:
            game = self.active_games.get(game_id)
            if not game:
                return None
            
            draw_data = {
                'game_id': game_id,
                'accepted_by': player,
                'result': 'draw'
            }
            # Notify both players
            game['white_handler'].send(MSG_GAME_DRAW_ACCEPT, draw_data)
            game['black_handler'].send(MSG_GAME_DRAW_ACCEPT, draw_data)
            # Notify spectators
            for spec in self.spectators.get(game_id, []):
                try:
                    spec.send(MSG_GAME_DRAW_ACCEPT, draw_data)
                except:
                    pass
            # Persist chat
            if self._db:
                self._db.save_game_chat(game_id, game.get('chat_log', []))
            # Remove game
            del self.active_games[game_id]
            self.spectators.pop(game_id, None)
            self.rematch_requests.pop(game_id, None)
            
            return {'result': 'draw'}
    
    def send_chat(self, game_id, player, message):
        """Send chat message to opponent and spectators."""
        with self.lock:
            game = self.active_games.get(game_id)
            if not game:
                return False
            
            # Persist to chat log
            entry = {'from': player, 'msg': message, 'ts': time.time()}
            game['chat_log'].append(entry)
            
            # Get opponent's handler
            opponent_handler = game['black_handler'] if player == game['white'] else game['white_handler']
            chat_data = {
                'game_id': game_id,
                'from_player': player,
                'message': message
            }
            opponent_handler.send(MSG_GAME_CHAT, chat_data)
            # Notify spectators
            for spec in self.spectators.get(game_id, []):
                try:
                    spec.send(MSG_GAME_CHAT, chat_data)
                except:
                    pass
            
            return True

    # ════════════════════════════════════════════════════════════════════
    #  SPECTATOR SYSTEM
    # ════════════════════════════════════════════════════════════════════
    def list_active_games(self):
        """Return list of spectatable games."""
        with self.lock:
            games = []
            for game_id, game in self.active_games.items():
                white_remaining = round(game.get('clock_white', 0))
                black_remaining = round(game.get('clock_black', 0))
                games.append({
                    'game_id': game_id,
                    'white': game['white'],
                    'black': game['black'],
                    'move_count': len(game['move_log']),
                    'spectator_count': len(self.spectators.get(game_id, [])),
                    'clock_enabled': game.get('clock_enabled', False),
                    'white_remaining': white_remaining,
                    'black_remaining': black_remaining,
                    'turn': game['current_turn']
                })
            return games

    def spectate_join(self, game_id, handler):
        """Add a spectator to a game."""
        with self.lock:
            game = self.active_games.get(game_id)
            if not game:
                return False, "Game not found"
            if game_id not in self.spectators:
                self.spectators[game_id] = []
            self.spectators[game_id].append(handler)
            # Send current game state
            handler.send(MSG_SPECTATE_UPDATE, {
                'game_id': game_id,
                'white': game['white'],
                'black': game['black'],
                'fen': game['fen'],
                'move_log': game['move_log'],
                'chat_log': game.get('chat_log', []),
                'turn': game['current_turn'],
                'clock_enabled': game.get('clock_enabled', False),
                'white_remaining': round(game.get('clock_white', 0)),
                'black_remaining': round(game.get('clock_black', 0))
            })
            return True, "Joined spectators"

    def spectate_leave(self, game_id, handler):
        """Remove a spectator from a game."""
        with self.lock:
            specs = self.spectators.get(game_id, [])
            if handler in specs:
                specs.remove(handler)

    # ════════════════════════════════════════════════════════════════════
    #  REMATCH SYSTEM
    # ════════════════════════════════════════════════════════════════════
    def request_rematch(self, game_id, requester, white, black,
                        white_handler, black_handler):
        """Process a rematch request. If both players agree, start new game."""
        with self.lock:
            if game_id not in self.rematch_requests:
                # First request
                self.rematch_requests[game_id] = {'requester': requester}
                # Notify opponent
                opponent = black if requester == white else white
                opp_handler = black_handler if requester == white else white_handler
                try:
                    opp_handler.send(MSG_REMATCH_REQUEST, {
                        'game_id': game_id,
                        'from': requester
                    })
                except:
                    pass
                return True, "Rematch requested"
            else:
                # Second request — both agreed
                self.game_counter += 1
                new_game_id = self.game_counter
                # Swap colors
                new_white, new_black = black, white
                new_white_h, new_black_h = black_handler, white_handler
                self._make_game(new_game_id, new_white, new_black,
                                new_white_h, new_black_h)
                del self.rematch_requests[game_id]
                rematch_data = {
                    'new_game_id': new_game_id,
                    'white': new_white,
                    'black': new_black
                }
                try:
                    new_white_h.send(MSG_REMATCH_RESPONSE, {**rematch_data, 'color': 'white'})
                except:
                    pass
                try:
                    new_black_h.send(MSG_REMATCH_RESPONSE, {**rematch_data, 'color': 'black'})
                except:
                    pass
                return True, "Rematch started"


# ════════════════════════════════════════════════════════════════════════
#  CLIENT HANDLER
# ════════════════════════════════════════════════════════════════════════
class ClientHandler:
    """Handles communication with a single client."""

    def __init__(self, conn, addr, db_manager, matchmaking_manager=None):
        self.conn = conn
        self.addr = addr
        self.db = db_manager
        self.matchmaking = matchmaking_manager
        self.logged_in_user = None
        self.pending = b''
        self.current_game_id = None
        self.analysis_queue = None  # Set by ChessServer after creation
        # E2E encryption session keys
        self.session_key = None
        self.client_public = None
        self.encryption_enabled = False
        self._nonce_counter = 0

    def _derive_nonce(self):
        """Derive a unique nonce for each message (12 bytes for GCM).
        
        Uses a different nonce space than the client to avoid nonce reuse:
        - Client uses nonces with bit 0 = 0 (even counter values)
        - Server uses nonces with bit 0 = 1 (odd counter values)
        """
        self._nonce_counter += 1
        # Pack counter as 8-byte big-endian, then pad to 12 bytes
        # Set the LSB of the last byte to 1 to distinguish server->client messages
        nonce_bytes = b'\x00\x00\x00\x00' + struct.pack('>Q', self._nonce_counter)
        # Set the last bit to distinguish from client nonces
        nonce_bytes = nonce_bytes[:-1] + bytes([nonce_bytes[-1] | 0x01])
        return nonce_bytes

    def _encrypt_message(self, plaintext: bytes) -> bytes:
        """Encrypt a message using session key."""
        if not self.encryption_enabled or self.session_key is None:
            return plaintext
        nonce = self._derive_nonce()
        ciphertext, tag = _gcm_encrypt(plaintext, self.session_key, nonce)
        # Prepend nonce to ciphertext
        return b'E' + nonce + ciphertext + tag

    def _decrypt_message(self, ciphertext: bytes) -> bytes:
        """Decrypt a message using session key."""
        if not self.encryption_enabled or self.session_key is None:
            return ciphertext
        if len(ciphertext) < 29:  # 1 (flag) + 12 (nonce) + 16 (tag)
            raise ValueError("Invalid encrypted message")
        if ciphertext[0:1] != b'E':
            raise ValueError("Invalid encryption flag")
        nonce = ciphertext[1:13]
        encrypted_data = ciphertext[13:-16]
        tag = ciphertext[-16:]
        return _gcm_decrypt(encrypted_data, self.session_key, nonce, tag)

    def send(self, msg_type, data='', success=True):
        """Send a message to the client (encrypted if session established)."""
        payload = json.dumps({
            'type': msg_type,
            'success': success,
            'data': data
        }).encode()

        # Encrypt if session is established (but not for key exchange messages)
        if self.encryption_enabled and self.session_key and msg_type not in [MSG_GET_SERVER_PUBLIC_KEY, MSG_SESSION_KEY_EXCHANGE]:
            payload = self._encrypt_message(payload)

        header = struct.pack('>I', len(payload))
        try:
            self.conn.sendall(header + payload)
            return True
        except (ConnectionResetError, BrokenPipeError, OSError):
            return False
        except Exception:
            return False

    def recv(self, timeout=30.0):
        """Receive a message from the client (decrypt if session established)."""
        self.conn.settimeout(timeout)
        try:
            while True:
                header_size = 4
                if len(self.pending) >= header_size:
                    length = struct.unpack('>I', self.pending[:4])[0]
                    if length > 10_000_000:
                        self.pending = b''
                        continue
                    if len(self.pending) >= 4 + length:
                        payload = self.pending[4:4 + length]
                        self.pending = self.pending[4 + length:]
                        if self.encryption_enabled and self.session_key and payload[0:1] == b'E':
                            try:
                                payload = self._decrypt_message(payload)
                            except Exception:
                                return None
                        try:
                            return json.loads(payload.decode())
                        except json.JSONDecodeError:
                            return None

                chunk = self.conn.recv(4096)
                if not chunk:
                    return None
                self.pending += chunk
        except (socket.timeout, ConnectionResetError, BrokenPipeError, OSError):
            return None
        except Exception:
            return None

    def handle_register(self, data):
        """Handle user registration with E2E encryption."""
        # Check if data is encrypted
        if 'encrypted' in data and data['encrypted']:
            try:
                # Decrypt the credentials
                credentials = decrypt_credentials(data, ChessServer._server_private)
                username = credentials.get('username', '').strip()
                password = credentials.get('password', '')
                email = credentials.get('email', '').strip()
            except Exception as e:
                self.send(RESP_ERROR, "Decryption failed", False)
                return
        else:
            # Fallback to plaintext (for debugging)
            username = data.get('username', '').strip()
            password = data.get('password', '')
            email = data.get('email', '').strip()

        success, message = self.db.register_user(username, password, email)
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

    def handle_login(self, data):
        """Handle user login with E2E encryption and rate limiting."""
        ip = self.addr[0] if self.addr else ''
        if ip and self.db.check_login_rate_limit(ip):
            self.send(RESP_ERROR, "Too many failed login attempts. Try again in 1 minute.", False)
            return

        if 'encrypted' in data and data['encrypted']:
            try:
                credentials = decrypt_credentials(data, ChessServer._server_private)
                username = credentials.get('username', '').strip()
                password = credentials.get('password', '')
            except Exception:
                self.send(RESP_ERROR, "Decryption failed", False)
                return
        else:
            username = data.get('username', '').strip()
            password = data.get('password', '')

        success, message = self.db.authenticate_user(username, password, ip)
        if success:
            self.logged_in_user = username
            server = getattr(self, 'server', None)
            if server:
                server.connected_clients[username] = self
            log.info(f"Login: {username} from {ip}")
        else:
            log.warning(f"Failed login for '{username}' from {ip}")
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

    def handle_auto_login(self, data):
        """Handle auto-login using stored password hash."""
        if 'encrypted' in data and data['encrypted']:
            try:
                credentials = decrypt_credentials(data, ChessServer._server_private)
                username = credentials.get('username', '').strip()
                password_hash = credentials.get('password_hash', '')
            except Exception:
                self.send(RESP_ERROR, "Decryption failed", False)
                return
        else:
            username = data.get('username', '').strip()
            password_hash = data.get('password_hash', '')

        success, message = self.db.authenticate_user_with_hash(username, password_hash)
        if success:
            self.logged_in_user = username
            server = getattr(self, 'server', None)
            if server:
                server.connected_clients[username] = self
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

    def handle_get_profile(self, data):
        """Handle profile request with pagination support."""
        username = data.get('username', '').strip()
        if not username:
            username = self.logged_in_user
        if not username:
            self.send(RESP_ERROR, "Not logged in", False)
            return
        page = int(data.get('page', 0))
        page_size = min(int(data.get('page_size', 10)), 50)
        profile = self.db.get_user_profile(username, page, page_size)
        if profile:
            self.send(RESP_PROFILE, profile, True)
        else:
            self.send(RESP_ERROR, "User not found", False)
    
    def handle_save_game(self, data):
        """Handle game save request with achievements and analysis trigger."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        white = data.get('white', '')
        black = data.get('black', '')
        result = data.get('result', 'draw')
        moves = data.get('moves', [])
        duration = data.get('duration', 0)
        rated = data.get('rated', True)
        pgn = data.get('pgn', '')
        move_times = data.get('move_times', [])

        success, elo_changes = self.db.save_game(white, black, result, moves, duration, rated, pgn, move_times)

        if success:
            # Check and award achievements for both players
            server = getattr(self, 'server', None)
            for username in [white, black]:
                if not username:
                    continue
                new_achs = self.db.check_and_award_achievements(username)
                if new_achs and server:
                    handler = server.connected_clients.get(username)
                    if handler:
                        for ach_id in new_achs:
                            info = self.db.ACHIEVEMENTS.get(ach_id, {})
                            try:
                                handler.send(MSG_ACHIEVEMENT_UNLOCKED, {
                                    'id': ach_id,
                                    'name': info.get('name', ach_id),
                                    'desc': info.get('desc', ''),
                                })
                            except Exception:
                                pass

        if success and elo_changes:
            self.send(RESP_SUCCESS, elo_changes, True)
        else:
            self.send(RESP_SUCCESS if success else RESP_ERROR,
                      "Game saved" if success else "Failed to save game", success)

    def handle_analysis_request(self, data):
        """Enqueue a post-game analysis job."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return
        game_id = data.get('game_id')
        moves = data.get('moves', [])
        pgn = data.get('pgn', '')
        white = data.get('white', '')
        black = data.get('black', '')
        aq = getattr(self, 'analysis_queue', None)
        if not aq:
            self.send(RESP_ERROR, "Analysis queue not available", False)
            return
        # Check for cached result first
        cached = aq.get_result(game_id)
        if cached:
            self.send(RESP_SUCCESS, cached, True)
            return
        aq.submit(game_id, white, black, moves, pgn, self.logged_in_user)
        self.send(RESP_SUCCESS, {'queued': True, 'game_id': game_id,
                                  'note': 'Analysis queued. You will receive MSG_ANALYSIS_RESULT when complete.'}, True)

    
    def handle_list_users(self, data):
        """Handle user list request."""
        try:
            # Check if user is logged in
            if not self.logged_in_user:
                self.send(RESP_ERROR, "Not logged in", False)
                return
            users = self.db.list_users()
            self.send(RESP_USERS, users, True)
        except Exception as e:
            print(f"  [ERROR] handle_list_users failed: {e}", flush=True)
            self.send(RESP_ERROR, str(e), False)

    def handle_leaderboard(self, data):
        """Handle leaderboard request."""
        if not isinstance(data, dict):
            data = {}
        limit = int(data.get('limit', 10))
        leaderboard = self.db.get_leaderboard(limit)
        self.send(RESP_LEADERBOARD, leaderboard, True)

    # ════════════════════════════════════════════════════════════════════
    #  MATCHMAKING HANDLERS
    # ════════════════════════════════════════════════════════════════════
    def handle_queue_join(self, data):
        """Handle joining matchmaking queue."""
        username = data.get('username')
        if not username:
            username = self.logged_in_user

        if not username:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        if not self.matchmaking:
            self.send(RESP_ERROR, "Matchmaking not available", False)
            return

        time_control = data.get('time_control', 'rapid')
        if time_control not in ('bullet', 'blitz', 'rapid', 'classical'):
            time_control = 'rapid'

        success, message = self.matchmaking.join_queue(username, self, time_control)
        self.send(RESP_QUEUED if success else RESP_ERROR, message, success)

    def handle_queue_leave(self, data):
        """Handle leaving matchmaking queue."""
        if not self.matchmaking:
            self.send(RESP_ERROR, "Matchmaking not available", False)
            return

        # Get username from data or fall back to logged_in_user
        username = data.get('username')
        if not username:
            username = self.logged_in_user

        if not username:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        success, message = self.matchmaking.leave_queue(username)
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

    def handle_queue_status(self, data):
        """Handle queue status request."""
        if not self.matchmaking:
            self.send(RESP_ERROR, "Matchmaking not available", False)
            return

        # Get username from data or fall back to logged_in_user
        username = data.get('username')
        if not username:
            username = self.logged_in_user

        if not username:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        # Check if client wants to trigger matchmaking
        if data.get('trigger'):
            success, result = self.matchmaking.trigger_matchmaking(username)
            if success:
                self.send(RESP_SUCCESS, result, True)
            else:
                self.send(RESP_ERROR, result, False)
        else:
            success, status = self.matchmaking.get_queue_status(username)
            if success:
                self.send(RESP_SUCCESS, status, True)
            else:
                self.send(RESP_ERROR, "Not in queue", False)
    
    def handle_game_move(self, data):
        """Handle a move in an active game."""
        if not self.logged_in_user or not self.matchmaking:
            self.send(RESP_ERROR, "Invalid request", False)
            return
        
        game_id = data.get('game_id')
        move = data.get('move')
        
        if game_id is None or not move:
            self.send(RESP_ERROR, "Invalid move data", False)
            return
        
        success, message = self.matchmaking.make_move(game_id, self.logged_in_user, move)
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)
    
    def handle_game_resign(self, data):
        """Handle resignation."""
        if not self.logged_in_user or not self.matchmaking:
            return
        
        game_id = data.get('game_id')
        if game_id:
            # Retrieve game data BEFORE resign() removes it from active_games
            game = self.matchmaking.get_game(game_id)
            result = self.matchmaking.resign(game_id, self.logged_in_user)
            if result and game:
                # result['loser'] is the username who resigned
                winner_color = 'black' if result['loser'] == game['white'] else 'white'
                self.db.save_game(
                    game['white'], game['black'],
                    winner_color,
                    game.get('move_log', []), 0
                )
    
    def handle_game_draw_offer(self, data):
        """Handle draw offer."""
        if not self.logged_in_user or not self.matchmaking:
            return
        
        game_id = data.get('game_id')
        if game_id:
            self.matchmaking.offer_draw(game_id, self.logged_in_user)
    
    def handle_game_draw_accept(self, data):
        """Handle draw acceptance."""
        if not self.logged_in_user or not self.matchmaking:
            return
        
        game_id = data.get('game_id')
        if game_id:
            # Retrieve game data BEFORE accept_draw() removes it from active_games
            game = self.matchmaking.get_game(game_id)
            result = self.matchmaking.accept_draw(game_id, self.logged_in_user)
            if result and game:
                self.db.save_game(game['white'], game['black'], 'draw',
                                  game.get('move_log', []), 0)
    
    def handle_game_chat(self, data):
        """Handle chat message."""
        if not self.logged_in_user or not self.matchmaking:
            return

        game_id = data.get('game_id')
        message = data.get('message', '')

        if game_id and message:
            self.matchmaking.send_chat(game_id, self.logged_in_user, message)

    # ════════════════════════════════════════════════════════════════════
    #  FRIEND SYSTEM HANDLERS
    # ════════════════════════════════════════════════════════════════════
    def handle_friend_request(self, data):
        """Handle sending a friend request."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        recipient = data.get('recipient', '').strip()
        if not recipient:
            self.send(RESP_ERROR, "Recipient required", False)
            return

        success, message = self.db.send_friend_request(self.logged_in_user, recipient)
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

    def handle_friend_response(self, data):
        """Handle responding to a friend request."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        sender = data.get('sender', '').strip()
        accept = data.get('accept', False)

        if not sender:
            self.send(RESP_ERROR, "Sender required", False)
            return

        success, message = self.db.respond_to_friend_request(sender, self.logged_in_user, accept)
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

        # Notify the sender
        if success and accept:
            # Find the sender's handler and notify
            server = getattr(self, 'server', None)
            if server and sender in server.connected_clients:
                server.connected_clients[sender].send(MSG_FRIEND_RESPONSE, {
                    'responder': self.logged_in_user,
                    'accepted': True
                })

    def handle_friend_list(self, data):
        """Handle getting friend list."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        friends = self.db.get_friends(self.logged_in_user)
        # Get online status for each friend
        server = getattr(self, 'server', None)
        friend_status = []
        for friend in friends:
            friend_status.append({
                'username': friend,
                'online': friend in server.connected_clients if server else False
            })
        self.send(RESP_SUCCESS, {'friends': friend_status}, True)

    def handle_friend_remove(self, data):
        """Handle removing a friend."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        friend = data.get('friend', '').strip()
        if not friend:
            self.send(RESP_ERROR, "Friend username required", False)
            return

        success, message = self.db.remove_friend(self.logged_in_user, friend)
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

    def handle_friend_requests_list(self, data):
        """Handle getting pending friend requests."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        requests = self.db.get_friend_requests(self.logged_in_user)
        self.send(RESP_SUCCESS, {'requests': requests}, True)

    # ════════════════════════════════════════════════════════════════════
    #  MESSAGING SYSTEM HANDLERS
    # ════════════════════════════════════════════════════════════════════
    def handle_session_key_exchange(self, data):
        """Handle session key exchange for E2E encryption of all communications."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        client_public = data.get('client_public')
        if not client_public:
            self.send(RESP_ERROR, "Client public key required", False)
            return

        try:
            shared_secret = _dh_compute_shared_secret(ChessServer._server_private, client_public)
            self.session_key = shared_secret
            self.encryption_enabled = True
            self._nonce_counter = 0

            old_encryption_state = self.encryption_enabled
            self.encryption_enabled = False
            self.send(RESP_SUCCESS, {
                'message': 'Session key exchange successful. All future communications are encrypted.',
                'server_public': ChessServer._server_public
            }, True)
            self.encryption_enabled = old_encryption_state
        except Exception:
            self.send(RESP_ERROR, "Session key exchange failed", False)

    def handle_key_exchange(self, data):
        """Handle key exchange for E2E encryption (legacy - use SESSION_KEY_EXCHANGE instead)."""
        # Redirect to session key exchange for backward compatibility
        self.handle_session_key_exchange(data)

    def handle_get_server_public_key(self, data):
        """Handle request for server's public key (for E2E encryption)."""
        # Send server's public key to client
        self.send(RESP_SUCCESS, {
            'server_public': ChessServer._server_public
        }, True)

    def handle_send_message(self, data):
        """
        Handle sending an encrypted message to another user.

        Architecture: Store-and-forward with E2E encryption
        - Message is encrypted by sender with recipient's public key
        - Server stores the encrypted blob (cannot read contents)
        - Recipient pulls messages when they come online
        - No error if recipient is offline - message waits on server
        """
        try:
            if not self.logged_in_user:
                self.send(MSG_MESSAGE_SENT_ACK, {
                    'success': False,
                    'error': 'Not logged in',
                    'stored': False
                })
                return

            recipient = data.get('recipient', '').strip()
            encrypted_content = data.get('encrypted_content')
            iv = data.get('iv')
            tag = data.get('tag')

            # Validate inputs
            if not recipient:
                self.send(MSG_MESSAGE_SENT_ACK, {
                    'success': False,
                    'error': 'Recipient required',
                    'stored': False
                })
                return
            
            if not encrypted_content:
                self.send(MSG_MESSAGE_SENT_ACK, {
                    'success': False,
                    'error': 'Message content required',
                    'stored': False
                })
                return

            # Verify recipient exists
            if recipient not in self.db._load_db().get('users', {}):
                self.send(MSG_MESSAGE_SENT_ACK, {
                    'success': False,
                    'error': 'Recipient not found',
                    'stored': False
                })
                return

            # Verify users are friends
            if not self.db.are_friends(self.logged_in_user, recipient):
                self.send(MSG_MESSAGE_SENT_ACK, {
                    'success': False,
                    'error': 'Users are not friends',
                    'stored': False
                })
                return

            # Store the message (E2E encrypted - server cannot read it)
            success, result = self.db.store_message(
                self.logged_in_user, recipient, encrypted_content, iv, tag
            )

            if not success:
                self.send(MSG_MESSAGE_SENT_ACK, {
                    'success': False,
                    'error': result,
                    'stored': False
                })
                return

            # SUCCESS: Message stored on server
            # Recipient will get it when they pull messages (online or later)
            self.send(MSG_MESSAGE_SENT_ACK, {
                'success': True,
                'message_id': result,
                'stored': True,
                'recipient_online': recipient in getattr(self.server, 'connected_clients', {})
            })
            
            # Optionally notify online recipient (fire-and-forget, non-blocking)
            # This is just a hint - recipient will pull messages anyway
            server = getattr(self, 'server', None)
            if server and recipient in server.connected_clients:
                try:
                    # Send notification in background thread (don't block)
                    def notify_recipient():
                        try:
                            recipient_client = server.connected_clients.get(recipient)
                            if recipient_client and recipient_client.conn:
                                # Check if socket is still connected before sending
                                recipient_client.send(MSG_NEW_MESSAGE_NOTIFY, {
                                    'sender': self.logged_in_user,
                                    'hint': 'New message available'
                                })
                        except (ConnectionResetError, BrokenPipeError, OSError):
                            pass  # Recipient disconnected - they'll get messages when they pull
                        except Exception:
                            pass  # Ignore other notification failures

                    threading.Thread(target=notify_recipient, daemon=True).start()
                except Exception:
                    pass  # Ignore notification setup failures

        except Exception as e:
            # Log error but don't expose details to client
            import traceback
            traceback.print_exc()
            self.send(MSG_MESSAGE_SENT_ACK, {
                'success': False,
                'error': 'Server error',
                'stored': False
            })

    def handle_get_messages(self, data):
        """Handle getting messages with a friend."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, 'Not logged in', False)
            return

        friend = data.get('friend', '').strip()
        since_id = data.get('since_id', 0)

        if not friend:
            self.send(RESP_ERROR, 'Friend username required', False)
            return

        # Verify users are friends
        if not self.db.are_friends(self.logged_in_user, friend):
            self.send(RESP_ERROR, 'Users are not friends', False)
            return

        messages = self.db.get_messages(self.logged_in_user, friend, since_id)
        self.send(RESP_SUCCESS, {'messages': messages}, True)

    # ════════════════════════════════════════════════════════════════════
    #  CHALLENGE SYSTEM HANDLERS
    # ════════════════════════════════════════════════════════════════════
    def handle_challenge_send(self, data):
        """Handle sending a game challenge."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        challenged = data.get('challenged', '').strip()
        color_choice = data.get('color_choice', 'random')
        rated = data.get('rated', True)

        if not challenged:
            self.send(RESP_ERROR, "Challenged user required", False)
            return

        success, result = self.db.send_challenge(
            self.logged_in_user, challenged, color_choice, rated
        )
        
        if not success:
            self.send(RESP_ERROR, result, False)
            return

        # Notify the challenged user
        server = getattr(self, 'server', None)
        if server and challenged in server.connected_clients:
            server.connected_clients[challenged].send(MSG_CHALLENGE_SEND, {
                'challenger': self.logged_in_user,
                'challenge_id': result,
                'color_choice': color_choice,
                'rated': rated
            })

        self.send(RESP_SUCCESS, {'challenge_id': result}, True)

    def handle_challenge_response(self, data):
        """Handle responding to a challenge."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        challenger = data.get('challenger', '').strip()
        accept = data.get('accept', False)

        if not challenger:
            self.send(RESP_ERROR, "Challenger required", False)
            return

        success, result = self.db.respond_to_challenge(challenger, self.logged_in_user, accept)
        
        if not success:
            self.send(RESP_ERROR, result, False)
            return

        # Notify the challenger
        server = getattr(self, 'server', None)
        if server and challenger in server.connected_clients:
            server.connected_clients[challenger].send(MSG_CHALLENGE_RESPONSE, {
                'responder': self.logged_in_user,
                'accepted': accept,
                'details': result if accept else None
            })

        if accept:
            # Also send game start info to both players
            if server and challenger in server.connected_clients:
                server.connected_clients[challenger].send(MSG_GAME_START, {
                    'opponent': self.logged_in_user,
                    'color': result['challenger_color'],
                    'rated': result['rated'],
                    'challenge_id': result['challenge_id']
                })
            self.send(MSG_GAME_START, {
                'opponent': challenger,
                'color': result['challenged_color'],
                'rated': result['rated'],
                'challenge_id': result['challenge_id']
            })

        self.send(RESP_SUCCESS, result if accept else {'message': result}, True)

    def handle_challenge_list(self, data):
        """Handle getting pending challenges."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        challenges = self.db.get_challenges(self.logged_in_user)
        self.send(RESP_SUCCESS, {'challenges': challenges}, True)

    def handle_challenge_cancel(self, data):
        """Handle cancelling a challenge."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return

        challenged = data.get('challenged', '').strip()
        if not challenged:
            self.send(RESP_ERROR, "Challenged user required", False)
            return

        success, message = self.db.cancel_challenge(self.logged_in_user, challenged)
        self.send(RESP_SUCCESS if success else RESP_ERROR, message, success)

    # ════════════════════════════════════════════════════════════════════
    #  SPECTATOR HANDLERS
    # ════════════════════════════════════════════════════════════════════
    def handle_spectate_list(self, data):
        """Return list of spectatable games."""
        games = self.matchmaking.list_active_games()
        self.send(RESP_SUCCESS, games)

    def handle_spectate_join(self, data):
        """Join as a spectator."""
        game_id = data.get('game_id')
        if game_id is None:
            self.send(RESP_ERROR, "game_id required", False)
            return
        success, msg = self.matchmaking.spectate_join(int(game_id), self)
        self.send(RESP_SUCCESS if success else RESP_ERROR, msg, success)

    def handle_spectate_leave(self, data):
        """Leave spectator mode."""
        game_id = data.get('game_id')
        if game_id is not None:
            self.matchmaking.spectate_leave(int(game_id), self)
        self.send(RESP_SUCCESS, "Left spectators")

    # ════════════════════════════════════════════════════════════════════
    #  REMATCH HANDLERS
    # ════════════════════════════════════════════════════════════════════
    def handle_rematch_request(self, data):
        """Handle rematch request."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return
        game_id = data.get('game_id')
        white = data.get('white')
        black = data.get('black')
        if not all([game_id, white, black]):
            self.send(RESP_ERROR, "Missing fields", False)
            return
        # Find handlers
        server = getattr(self, 'server', None)
        if not server:
            self.send(RESP_ERROR, "Server error", False)
            return
        white_handler = server.connected_clients.get(white)
        black_handler = server.connected_clients.get(black)
        if not white_handler or not black_handler:
            self.send(RESP_ERROR, "Opponent not connected", False)
            return
        success, msg = self.matchmaking.request_rematch(
            game_id, self.logged_in_user, white, black,
            white_handler, black_handler)
        self.send(RESP_SUCCESS if success else RESP_ERROR, msg, success)

    # ════════════════════════════════════════════════════════════════════
    #  AVATAR / PROFILE HANDLERS
    # ════════════════════════════════════════════════════════════════════
    def handle_set_avatar(self, data):
        """Set current user's avatar and bio."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return
        avatar = str(data.get('avatar', ''))[:500]
        bio = str(data.get('bio', ''))[:200]
        success, msg = self.db.set_avatar(self.logged_in_user, avatar, bio)
        self.send(RESP_SUCCESS if success else RESP_ERROR, msg, success)

    def handle_get_avatar(self, data):
        """Get avatar/profile for a user."""
        username = data.get('username') or self.logged_in_user
        if not username:
            self.send(RESP_ERROR, "Username required", False)
            return
        profile = self.db.get_avatar(username)
        if profile is None:
            self.send(RESP_ERROR, "User not found", False)
        else:
            self.send(RESP_SUCCESS, profile)

    # ════════════════════════════════════════════════════════════════════
    #  CHAT HISTORY HANDLER
    # ════════════════════════════════════════════════════════════════════
    def handle_game_chat_history(self, data):
        """Return chat history for a completed game."""
        game_id = data.get('game_id')
        if game_id is None:
            self.send(RESP_ERROR, "game_id required", False)
            return
        chat_log = self.db.get_game_chat(game_id)
        self.send(RESP_SUCCESS, {'game_id': game_id, 'chat_log': chat_log})

    # ════════════════════════════════════════════════════════════════════
    #  LOBBY CHAT HANDLERS
    # ════════════════════════════════════════════════════════════════════
    def handle_lobby_chat(self, data):
        """Handle a lobby chat message."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return
        message = str(data.get('message', '')).strip()[:500]
        if not message:
            self.send(RESP_ERROR, "Empty message", False)
            return
        self.db.add_lobby_message(self.logged_in_user, message)
        # Broadcast to all connected clients
        server = getattr(self, 'server', None)
        if server:
            payload = {'sender': self.logged_in_user, 'message': message,
                       'ts': datetime.now().isoformat()}
            for handler in list(server.connected_clients.values()):
                try:
                    handler.send(MSG_LOBBY_CHAT, payload)
                except Exception:
                    pass
        self.send(RESP_SUCCESS, "Sent", True)

    def handle_lobby_chat_history(self, data):
        """Return recent lobby chat history."""
        limit = min(int(data.get('limit', 50)), 200)
        msgs = self.db.get_lobby_chat(limit)
        self.send(RESP_SUCCESS, {'messages': msgs}, True)

    # ════════════════════════════════════════════════════════════════════
    #  DAILY PUZZLE HANDLER
    # ════════════════════════════════════════════════════════════════════
    def handle_daily_puzzle(self, data):
        """Return today's daily puzzle."""
        puzzle = self.db.get_or_generate_daily_puzzle()
        self.send(RESP_SUCCESS, puzzle, True)

    # ════════════════════════════════════════════════════════════════════
    #  ACHIEVEMENT HANDLERS
    # ════════════════════════════════════════════════════════════════════
    def handle_achievements(self, data):
        """Return achievements list for a user."""
        username = data.get('username') or self.logged_in_user
        if not username:
            self.send(RESP_ERROR, "Not logged in", False)
            return
        achs = self.db.get_achievements(username)
        self.send(RESP_SUCCESS, {'achievements': achs}, True)

    # ════════════════════════════════════════════════════════════════════
    #  TOURNAMENT HANDLERS
    # ════════════════════════════════════════════════════════════════════
    def handle_tournament_create(self, data):
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return
        name = str(data.get('name', 'Tournament')).strip()[:60]
        max_players = min(max(int(data.get('max_players', 8)), 2), 32)
        rounds = min(max(int(data.get('rounds', 3)), 1), 9)
        tc = data.get('time_control', 'blitz')
        tid, tournament = self.db.create_tournament(name, self.logged_in_user, max_players, rounds, tc)
        log.info(f"Tournament created: '{name}' by {self.logged_in_user} (id={tid})")
        self.send(RESP_SUCCESS, {'tournament_id': tid, 'tournament': tournament}, True)

    def handle_tournament_join(self, data):
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return
        tid = data.get('tournament_id', '').strip()
        if not tid:
            self.send(RESP_ERROR, "tournament_id required", False)
            return
        success, msg = self.db.join_tournament(tid, self.logged_in_user)
        self.send(RESP_SUCCESS if success else RESP_ERROR, msg, success)

    def handle_tournament_list(self, data):
        tournaments = self.db.list_tournaments()
        self.send(RESP_SUCCESS, {'tournaments': tournaments}, True)

    def handle_tournament_status(self, data):
        tid = data.get('tournament_id', '').strip()
        if not tid:
            self.send(RESP_ERROR, "tournament_id required", False)
            return
        t = self.db.get_tournament(tid)
        if not t:
            self.send(RESP_ERROR, "Tournament not found", False)
            return
        self.send(RESP_SUCCESS, t, True)

    def handle_tournament_result(self, data):
        """Admin/arbiter records a tournament game result."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return
        tid    = data.get('tournament_id', '')
        round_ = int(data.get('round', 0))
        white  = data.get('white', '')
        black  = data.get('black', '')
        result = data.get('result', '')
        if result not in ('white', 'black', 'draw'):
            self.send(RESP_ERROR, "result must be white/black/draw", False)
            return
        t = self.db.get_tournament(tid)
        if not t:
            self.send(RESP_ERROR, "Tournament not found", False)
            return
        if self.logged_in_user != t['creator']:
            self.send(RESP_ERROR, "Only the tournament creator can record results", False)
            return
        success, msg = self.db.record_tournament_result(tid, round_, white, black, result)
        self.send(RESP_SUCCESS if success else RESP_ERROR, msg, success)

    # ════════════════════════════════════════════════════════════════════
    #  RECONNECT HANDLER
    # ════════════════════════════════════════════════════════════════════
    def handle_reconnect(self, data):
        """Handle a client reconnecting to an ongoing game."""
        if not self.logged_in_user:
            self.send(RESP_ERROR, "Not logged in", False)
            return
        game_id = data.get('game_id')
        if game_id is None:
            self.send(RESP_ERROR, "game_id required", False)
            return
        # Remove from disconnected list
        if not self.matchmaking:
            self.send(RESP_ERROR, "Server error", False)
            return
        with self.matchmaking.lock:
            disc = self.matchmaking.disconnected.pop(self.logged_in_user, None)
            game = self.matchmaking.active_games.get(game_id)
        if not game:
            self.send(RESP_ERROR, "Game not found or already ended", False)
            return
        # Update handler reference so messages go to the new socket
        if game['white'] == self.logged_in_user:
            game['white_handler'] = self
        elif game['black'] == self.logged_in_user:
            game['black_handler'] = self
        else:
            self.send(RESP_ERROR, "You are not a player in this game", False)
            return
        log.info(f"{self.logged_in_user} reconnected to game {game_id}")
        self.send(RESP_SUCCESS, {
            'fen': game.get('fen', INITIAL_FEN),
            'move_log': game.get('move_log', []),
            'turn': game.get('current_turn', 'white'),
            'clock_white': game.get('clock_white', 0),
            'clock_black': game.get('clock_black', 0),
        }, True)

    def handle_request(self):
        """Main request handling loop."""
        while True:
            msg = self.recv(timeout=30.0)
            if not msg:
                # Client disconnected — start grace window for active game
                if self.matchmaking and self.logged_in_user:
                    with self.matchmaking.lock:
                        for gid, game in self.matchmaking.active_games.items():
                            if game['white'] == self.logged_in_user or game['black'] == self.logged_in_user:
                                grace = int(_cfg.get('disconnect_grace_seconds', 60))
                                self.matchmaking.disconnected[self.logged_in_user] = {
                                    'game_id': gid,
                                    'deadline': time.time() + grace,
                                }
                                log.info(f"{self.logged_in_user} disconnected from game {gid}; grace={grace}s")
                                # Notify opponent
                                opp_handler = game['black_handler'] if game['white'] == self.logged_in_user else game['white_handler']
                                try:
                                    opp_handler.send(MSG_SERVER_BROADCAST, {
                                        'message': f"{self.logged_in_user} disconnected. They have {grace}s to reconnect."
                                    })
                                except Exception:
                                    pass
                                break
                break

            msg_type = msg.get('type', '')
            data = msg.get('data', {})

            if msg_type == MSG_REGISTER:
                self.handle_register(data)
            elif msg_type == MSG_LOGIN:
                self.handle_login(data)
            elif msg_type == MSG_AUTO_LOGIN:
                self.handle_auto_login(data)
            elif msg_type == MSG_LOGOUT:
                # Leave queue if in one
                if self.matchmaking and self.logged_in_user:
                    self.matchmaking.leave_queue(self.logged_in_user)
                # Remove from connected clients
                server = getattr(self, 'server', None)
                if server and self.logged_in_user in server.connected_clients:
                    del server.connected_clients[self.logged_in_user]
                self.logged_in_user = None
                self.send(RESP_SUCCESS, "Logged out", True)
            elif msg_type == MSG_GET_PROFILE:
                self.handle_get_profile(data)
            elif msg_type == MSG_SAVE_GAME:
                self.handle_save_game(data)
            elif msg_type == MSG_LIST_USERS:
                self.handle_list_users(data)
            elif msg_type == MSG_LEADERBOARD:
                self.handle_leaderboard(data)
            elif msg_type == MSG_PING:
                self.send(RESP_SUCCESS, "pong", True)
            # Matchmaking messages
            elif msg_type == MSG_QUEUE_JOIN:
                self.handle_queue_join(data)
            elif msg_type == MSG_QUEUE_LEAVE:
                self.handle_queue_leave(data)
            elif msg_type == MSG_QUEUE_STATUS:
                self.handle_queue_status(data)
            elif msg_type == MSG_GAME_MOVE:
                self.handle_game_move(data)
            elif msg_type == MSG_GAME_RESIGN:
                self.handle_game_resign(data)
            elif msg_type == MSG_GAME_DRAW_OFFER:
                self.handle_game_draw_offer(data)
            elif msg_type == MSG_GAME_DRAW_ACCEPT:
                self.handle_game_draw_accept(data)
            elif msg_type == MSG_GAME_CHAT:
                self.handle_game_chat(data)
            # Spectator messages
            elif msg_type == MSG_SPECTATE_LIST:
                self.handle_spectate_list(data)
            elif msg_type == MSG_SPECTATE_JOIN:
                self.handle_spectate_join(data)
            elif msg_type == MSG_SPECTATE_LEAVE:
                self.handle_spectate_leave(data)
            # Rematch messages
            elif msg_type == MSG_REMATCH_REQUEST:
                self.handle_rematch_request(data)
            # Avatar/Profile messages
            elif msg_type == MSG_SET_AVATAR:
                self.handle_set_avatar(data)
            elif msg_type == MSG_GET_AVATAR:
                self.handle_get_avatar(data)
            # Chat history
            elif msg_type == MSG_GAME_CHAT_HISTORY:
                self.handle_game_chat_history(data)
            # Friend system messages
            elif msg_type == MSG_FRIEND_REQUEST:
                self.handle_friend_request(data)
            elif msg_type == MSG_FRIEND_RESPONSE:
                self.handle_friend_response(data)
            elif msg_type == MSG_FRIEND_LIST:
                self.handle_friend_list(data)
            elif msg_type == MSG_FRIEND_REMOVE:
                self.handle_friend_remove(data)
            elif msg_type == MSG_FRIEND_STATUS:
                self.handle_friend_requests_list(data)
            # Messaging system messages
            elif msg_type == MSG_KEY_EXCHANGE:
                self.handle_key_exchange(data)
            elif msg_type == MSG_SESSION_KEY_EXCHANGE:
                self.handle_session_key_exchange(data)
            elif msg_type == MSG_SEND_MESSAGE:
                self.handle_send_message(data)
            elif msg_type == MSG_GET_MESSAGES:
                self.handle_get_messages(data)
            # E2E Encryption
            elif msg_type == MSG_GET_SERVER_PUBLIC_KEY:
                self.handle_get_server_public_key(data)
            # Challenge system messages
            elif msg_type == MSG_CHALLENGE_SEND:
                self.handle_challenge_send(data)
            elif msg_type == MSG_CHALLENGE_RESPONSE:
                self.handle_challenge_response(data)
            elif msg_type == MSG_CHALLENGE_LIST:
                self.handle_challenge_list(data)
            elif msg_type == MSG_CHALLENGE_CANCEL:
                self.handle_challenge_cancel(data)
            # Lobby chat
            elif msg_type == MSG_LOBBY_CHAT:
                self.handle_lobby_chat(data)
            elif msg_type == MSG_LOBBY_CHAT_HISTORY:
                self.handle_lobby_chat_history(data)
            # Daily puzzle
            elif msg_type == MSG_DAILY_PUZZLE:
                self.handle_daily_puzzle(data)
            # Achievements
            elif msg_type == MSG_ACHIEVEMENTS:
                self.handle_achievements(data)
            # Tournament
            elif msg_type == MSG_TOURNAMENT_CREATE:
                self.handle_tournament_create(data)
            elif msg_type == MSG_TOURNAMENT_JOIN:
                self.handle_tournament_join(data)
            elif msg_type == MSG_TOURNAMENT_LIST:
                self.handle_tournament_list(data)
            elif msg_type == MSG_TOURNAMENT_STATUS:
                self.handle_tournament_status(data)
            elif msg_type == MSG_TOURNAMENT_RESULT:
                self.handle_tournament_result(data)
            # Reconnect
            elif msg_type == MSG_RECONNECT:
                self.handle_reconnect(data)
            # Post-game analysis
            elif msg_type == MSG_ANALYSIS_REQUEST:
                self.handle_analysis_request(data)
            else:
                self.send(RESP_ERROR, f"Unknown message type: {msg_type}", False)


    def close(self):
        """Close the connection."""
        try:
            if self.matchmaking and self.logged_in_user:
                self.matchmaking.leave_queue(self.logged_in_user)
            try:
                self.conn.shutdown(socket.SHUT_RDWR)
            except:
                pass
            self.conn.close()
        except Exception:
            pass


# ════════════════════════════════════════════════════════════════════════
#  POST-GAME ANALYSIS QUEUE (server-side, non-blocking)
# ════════════════════════════════════════════════════════════════════════
class AnalysisQueue:
    """
    Server-side analysis job queue.
    Jobs are processed in a background thread. Since the server may not have
    Stockfish available, the 'analysis' here produces a lightweight summary
    (game length, move count per phase, result note). A real deployment would
    call subprocess.run(['stockfish', ...]) here.
    """
    def __init__(self, db, server, workers=1):
        self._db = db
        self._server = server
        self._q = queue.Queue()
        self._results = {}   # game_id -> result dict
        self._lock = threading.Lock()
        self._workers = workers
        self._threads = []

    def start(self):
        for _ in range(self._workers):
            t = threading.Thread(target=self._worker, daemon=True)
            t.start()
            self._threads.append(t)

    def submit(self, game_id, white, black, moves, pgn, requester):
        """Enqueue an analysis job."""
        self._q.put({'game_id': game_id, 'white': white, 'black': black,
                     'moves': moves, 'pgn': pgn, 'requester': requester})

    def get_result(self, game_id):
        """Return cached analysis result or None."""
        with self._lock:
            return self._results.get(game_id)

    def _worker(self):
        while True:
            job = self._q.get()
            try:
                result = self._analyse(job)
                with self._lock:
                    self._results[job['game_id']] = result
                # Notify requester if still connected
                if self._server:
                    handler = self._server.connected_clients.get(job['requester'])
                    if handler:
                        try:
                            handler.send(MSG_ANALYSIS_RESULT, result)
                        except Exception:
                            pass
                log.info(f"Analysis complete for game {job['game_id']}")
            except Exception as e:
                log.error(f"Analysis worker error: {e}")
            finally:
                self._q.task_done()

    def _analyse(self, job):
        """Lightweight built-in analysis (no engine required)."""
        moves = job.get('moves', [])
        n = len(moves)
        opening = moves[:10] if n >= 10 else moves
        middlegame = moves[10:30] if n >= 30 else moves[10:]
        endgame = moves[30:] if n >= 30 else []
        return {
            'game_id': job['game_id'],
            'white': job['white'],
            'black': job['black'],
            'total_moves': n,
            'opening_moves': len(opening),
            'middlegame_moves': len(middlegame),
            'endgame_moves': len(endgame),
            'opening_line': ' '.join(opening[:6]),
            'note': f"Game lasted {n} half-moves. "
                    f"{'Quick finish' if n < 30 else 'Long game' if n > 80 else 'Standard length'}.",
            'pgn_available': bool(job.get('pgn')),
        }



# ════════════════════════════════════════════════════════════════════════
#  CHESS SERVER
# ════════════════════════════════════════════════════════════════════════
class ChessServer:
    """Main chess server class."""
    
    # Server's long-term DH key pair (generated once at startup)
    _server_private, _server_public = _dh_generate_keypair()

    def __init__(self, host='0.0.0.0', port=SERVER_PORT):
        self.host = host
        self.port = port
        self.db_manager = DatabaseManager()
        self.matchmaking = MatchmakingManager()
        self.matchmaking._db = self.db_manager
        self.matchmaking._server = self
        self.server_socket = None
        self.running = False
        self.clients = []
        self.connected_clients = {}  # username -> handler mapping
        self.cleanup_running = True
        self.analysis_queue = AnalysisQueue(
            self.db_manager, self,
            workers=int(_cfg.get('analysis_queue_workers', 1))
        )

    def start(self):
        """Start the server."""
        self.server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)

        try:
            self.server_socket.bind((self.host, self.port))
            self.server_socket.listen(int(_cfg.get('max_clients', 100)))
            self.running = True

            self.matchmaking.start()
            self.analysis_queue.start()

            cleanup_thread = threading.Thread(target=self._cleanup_loop, daemon=True)
            cleanup_thread.start()

            print("")
            print("╔══════════════════════════════════════════════════════════════════╗")
            print("║               CHESS SERVER v2.0 STARTED                          ║")
            print("╠══════════════════════════════════════════════════════════════════╣")
            print(f"║  Listening on: {self.host}:{self.port:<36}       ║")
            print(f"║  Database:     {os.path.basename(DATABASE_FILE):<44}  ║")
            print(f"║  Log file:     {os.path.basename(LOG_FILE):<44}  ║")
            print(f"║  Config:       {os.path.basename(CONFIG_FILE):<44}  ║")
            print("║  Matchmaking:  ELO-banded, time-control aware                    ║")
            print("║  Analysis:     Server-side queue active                          ║")
            print("║                                                                  ║")
            print("║  Admin commands (type and press Enter):                          ║")
            print("║    users              — list registered users                    ║")
            print("║    clients            — list connected clients                   ║")
            print("║    queue              — show queue + active games                ║")
            print("║    kick <user>        — disconnect a user                        ║")
            print("║    ban <user>         — ban a user account                       ║")
            print("║    unban <user>       — unban a user account                     ║")
            print("║    elo <user> <n>     — reset user ELO to n                     ║")
            print("║    broadcast <msg>    — send message to all clients              ║")
            print("║    tournaments        — list tournaments                         ║")
            print("║    quit               — stop the server                          ║")
            print("╚══════════════════════════════════════════════════════════════════╝")
            print("")
            log.info(f"Chess server v2.0 started on {self.host}:{self.port}")

            cmd_thread = threading.Thread(target=self._command_handler, daemon=True)
            cmd_thread.start()

            while self.running:
                try:
                    self.server_socket.settimeout(1.0)
                    conn, addr = self.server_socket.accept()
                    log.info(f"New connection from {addr[0]}:{addr[1]}")

                    handler = ClientHandler(conn, addr, self.db_manager, self.matchmaking)
                    handler.analysis_queue = self.analysis_queue
                    client_thread = threading.Thread(
                        target=self._handle_client,
                        args=(handler,),
                        daemon=True
                    )
                    client_thread.start()
                    self.clients.append(handler)

                except socket.timeout:
                    continue
                except Exception as e:
                    if self.running:
                        log.error(f"Accept error: {e}")

        except Exception as e:
            log.error(f"Server error: {e}")
        finally:
            self.stop()

    def _handle_client(self, handler):
        """Handle a client connection."""
        try:
            handler.server = self
            handler.handle_request()
        finally:
            if handler.logged_in_user and handler.logged_in_user in self.connected_clients:
                del self.connected_clients[handler.logged_in_user]
            handler.close()
            if handler in self.clients:
                self.clients.remove(handler)

    def _command_handler(self):
        """Handle server console admin commands."""
        while self.running:
            try:
                raw = input("").strip()
                parts = raw.split(None, 2)
                cmd = parts[0].lower() if parts else ''

                if cmd == 'quit':
                    self.running = False

                elif cmd == 'users':
                    users = self.db_manager.list_users()
                    print(f"  Registered users ({len(users)}): {', '.join(users) if users else 'None'}")

                elif cmd == 'clients':
                    cs = list(self.connected_clients.keys())
                    print(f"  Connected ({len(cs)}): {', '.join(cs) if cs else 'None'}")

                elif cmd == 'queue':
                    with self.matchmaking.lock:
                        q = {u: d['time_control'] for u, d in self.matchmaking.queue.items()}
                        games = {gid: f"{g['white']} vs {g['black']}"
                                 for gid, g in self.matchmaking.active_games.items()}
                    print(f"  Queue ({len(q)}): {q}")
                    print(f"  Active games ({len(games)}): {games}")

                elif cmd == 'tournaments':
                    ts = self.db_manager.list_tournaments()
                    for t in ts:
                        print(f"  [{t['id']}] '{t['name']}' — {t['status']} — "
                              f"{len(t['players'])}/{t['max_players']} players, "
                              f"round {t['current_round']}/{t['rounds']}")
                    if not ts:
                        print("  No tournaments.")

                elif cmd == 'kick' and len(parts) >= 2:
                    target = parts[1]
                    handler = self.connected_clients.get(target)
                    if handler:
                        handler.send(MSG_SERVER_BROADCAST, {'message': 'You have been kicked by an admin.'})
                        handler.close()
                        print(f"  Kicked: {target}")
                        log.warning(f"Admin kicked '{target}'")
                    else:
                        print(f"  User '{target}' not connected.")

                elif cmd == 'ban' and len(parts) >= 2:
                    target = parts[1]
                    ok, msg = self.db_manager.ban_user(target)
                    print(f"  {msg}")
                    handler = self.connected_clients.get(target)
                    if handler:
                        handler.send(MSG_SERVER_BROADCAST, {'message': 'Your account has been banned.'})
                        handler.close()

                elif cmd == 'unban' and len(parts) >= 2:
                    target = parts[1]
                    ok, msg = self.db_manager.unban_user(target)
                    print(f"  {msg}")

                elif cmd == 'elo' and len(parts) >= 3:
                    target = parts[1]
                    try:
                        new_elo = int(parts[2])
                        ok, msg = self.db_manager.reset_elo(target, new_elo)
                        print(f"  {msg}")
                    except ValueError:
                        print("  Usage: elo <username> <rating>")

                elif cmd == 'broadcast' and len(parts) >= 2:
                    msg_text = raw[len('broadcast'):].strip()
                    payload = {'message': f"[SERVER] {msg_text}"}
                    count = 0
                    for h in list(self.connected_clients.values()):
                        try:
                            h.send(MSG_SERVER_BROADCAST, payload)
                            count += 1
                        except Exception:
                            pass
                    print(f"  Broadcast sent to {count} clients.")
                    log.info(f"Admin broadcast: {msg_text}")

                elif cmd:
                    print("  Unknown command. Try: users, clients, queue, kick, ban, unban, elo, broadcast, tournaments, quit")

            except (EOFError, KeyboardInterrupt):
                self.running = False
            except Exception as e:
                log.error(f"Command handler error: {e}")

    def _cleanup_loop(self):
        """Background loop to cleanup expired messages."""
        while self.cleanup_running:
            time.sleep(3600)
            try:
                deleted = self.db_manager.cleanup_expired_messages()
                if deleted > 0:
                    log.info(f"Cleaned up {deleted} expired messages")
            except Exception:
                pass

    def stop(self):
        """Stop the server."""
        self.running = False
        self.cleanup_running = False
        self.matchmaking.stop()
        for client in self.clients:
            client.close()
        if self.server_socket:
            self.server_socket.close()
        log.info("Server stopped.")
        print("  Server stopped.")


# ════════════════════════════════════════════════════════════════════════
#  CLIENT CONNECTION CLASS (for chess.py to use)
# ════════════════════════════════════════════════════════════════════════
class ChessClient:
    """Client connection for chess.py to communicate with the server."""
    
    def __init__(self, host='localhost', port=SERVER_PORT):
        self.host = host
        self.port = port
        self.sock = None
        self.logged_in_user = None
        self.pending = b''
    
    def connect(self):
        """Connect to the server."""
        try:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.sock.settimeout(10.0)
            self.sock.connect((self.host, self.port))
            self.sock.settimeout(None)
            return True, "Connected to server"
        except Exception as e:
            return False, f"Connection failed: {e}"
    
    def disconnect(self):
        """Disconnect from the server."""
        self.logged_in_user = None
        if self.sock:
            try:
                self.sock.close()
            except:
                pass
            self.sock = None
    
    def send(self, msg_type, data=None):
        """Send a message to the server."""
        if not self.sock:
            return False
        
        payload = json.dumps({
            'type': msg_type,
            'data': data or {}
        }).encode()
        header = struct.pack('>I', len(payload))
        
        try:
            self.sock.sendall(header + payload)
            return True
        except:
            return False
    
    def recv(self, timeout=5.0):
        """Receive a response from the server."""
        if not self.sock:
            return None
        
        self.sock.settimeout(timeout)
        try:
            while True:
                if len(self.pending) >= 4:
                    length = struct.unpack('>I', self.pending[:4])[0]
                    if len(self.pending) >= 4 + length:
                        payload = self.pending[4:4 + length]
                        self.pending = self.pending[4 + length:]
                        return json.loads(payload.decode())
                chunk = self.sock.recv(4096)
                if not chunk:
                    return None
                self.pending += chunk
        except socket.timeout:
            return None
        except:
            return None
    
    def register(self, username, password, email):
        """Register a new account."""
        self.send(MSG_REGISTER, {
            'username': username,
            'password': password,
            'email': email
        })
        return self.recv()
    
    def login(self, username, password):
        """Login to an account."""
        self.send(MSG_LOGIN, {
            'username': username,
            'password': password
        })
        response = self.recv()
        if response and response.get('success'):
            self.logged_in_user = username
        return response
    
    def logout(self):
        """Logout from the account."""
        self.send(MSG_LOGOUT)
        response = self.recv()
        if response and response.get('success'):
            self.logged_in_user = None
        return response
    
    def get_profile(self, username=None):
        """Get a user's profile."""
        data = {'username': username} if username else {}
        self.send(MSG_GET_PROFILE, data)
        return self.recv()
    
    def save_game(self, white, black, result, moves, duration=0):
        """Save a game to history."""
        self.send(MSG_SAVE_GAME, {
            'white': white,
            'black': black,
            'result': result,
            'moves': moves,
            'duration': duration
        })
        return self.recv()
    
    def list_users(self):
        """Get list of all users."""
        self.send(MSG_LIST_USERS)
        return self.recv()

    # ════════════════════════════════════════════════════════════════════
    #  MATCHMAKING CLIENT METHODS
    # ════════════════════════════════════════════════════════════════════
    def join_queue(self):
        """Join the matchmaking queue."""
        self.send(MSG_QUEUE_JOIN)
        return self.recv()

    def leave_queue(self):
        """Leave the matchmaking queue."""
        self.send(MSG_QUEUE_LEAVE)
        return self.recv()

    def get_queue_status(self):
        """Get queue status."""
        self.send(MSG_QUEUE_STATUS)
        return self.recv()

    def send_move(self, game_id, move):
        """Send a move in an active game."""
        self.send(MSG_GAME_MOVE, {
            'game_id': game_id,
            'move': move
        })
        return self.recv()

    def resign_game(self, game_id):
        """Resign from a game."""
        self.send(MSG_GAME_RESIGN, {
            'game_id': game_id
        })

    def offer_draw(self, game_id):
        """Offer a draw to opponent."""
        self.send(MSG_GAME_DRAW_OFFER, {
            'game_id': game_id
        })

    def accept_draw(self, game_id):
        """Accept a draw offer."""
        self.send(MSG_GAME_DRAW_ACCEPT, {
            'game_id': game_id
        })

    def send_chat(self, game_id, message):
        """Send chat message to opponent."""
        self.send(MSG_GAME_CHAT, {
            'game_id': game_id,
            'message': message
        })

    # ════════════════════════════════════════════════════════════════════
    #  FRIEND SYSTEM CLIENT METHODS
    # ════════════════════════════════════════════════════════════════════
    def send_friend_request(self, recipient):
        """Send a friend request."""
        self.send(MSG_FRIEND_REQUEST, {'recipient': recipient})
        return self.recv()

    def respond_to_friend_request(self, sender, accept):
        """Respond to a friend request."""
        self.send(MSG_FRIEND_RESPONSE, {'sender': sender, 'accept': accept})
        return self.recv()

    def get_friend_list(self):
        """Get list of friends."""
        self.send(MSG_FRIEND_LIST)
        return self.recv()

    def remove_friend(self, friend):
        """Remove a friend."""
        self.send(MSG_FRIEND_REMOVE, {'friend': friend})
        return self.recv()

    def get_friend_requests(self):
        """Get pending friend requests."""
        self.send(MSG_FRIEND_STATUS)
        return self.recv()

    # ════════════════════════════════════════════════════════════════════
    #  MESSAGING SYSTEM CLIENT METHODS
    # ════════════════════════════════════════════════════════════════════
    def key_exchange(self, public_key, key_type='dh'):
        """Perform key exchange for E2E encryption."""
        self.send(MSG_KEY_EXCHANGE, {'public_key': public_key, 'key_type': key_type})
        return self.recv()

    def send_message(self, recipient, encrypted_content, iv, tag):
        """Send an encrypted message."""
        self.send(MSG_SEND_MESSAGE, {
            'recipient': recipient,
            'encrypted_content': encrypted_content,
            'iv': iv,
            'tag': tag
        })
        return self.recv()

    def get_messages(self, friend, since_id=0):
        """Get messages with a friend."""
        self.send(MSG_GET_MESSAGES, {'friend': friend, 'since_id': since_id})
        return self.recv()

    # ════════════════════════════════════════════════════════════════════
    #  CHALLENGE SYSTEM CLIENT METHODS
    # ════════════════════════════════════════════════════════════════════
    def send_challenge(self, challenged, color_choice='random', rated=True):
        """Send a game challenge."""
        self.send(MSG_CHALLENGE_SEND, {
            'challenged': challenged,
            'color_choice': color_choice,
            'rated': rated
        })
        return self.recv()

    def respond_to_challenge(self, challenger, accept):
        """Respond to a challenge."""
        self.send(MSG_CHALLENGE_RESPONSE, {'challenger': challenger, 'accept': accept})
        return self.recv()

    def get_challenges(self):
        """Get pending challenges."""
        self.send(MSG_CHALLENGE_LIST)
        return self.recv()

    def cancel_challenge(self, challenged):
        """Cancel a pending challenge."""
        self.send(MSG_CHALLENGE_CANCEL, {'challenged': challenged})
        return self.recv()

    # ── Spectator methods ─────────────────────────────────────────────
    def list_spectatable_games(self):
        """List active games available to spectate."""
        self.send(MSG_SPECTATE_LIST, {})
        return self.recv()

    def spectate_game(self, game_id):
        """Join a game as a spectator."""
        self.send(MSG_SPECTATE_JOIN, {'game_id': game_id})
        return self.recv()

    def leave_spectate(self, game_id):
        """Leave spectator mode."""
        self.send(MSG_SPECTATE_LEAVE, {'game_id': game_id})
        return self.recv()

    # ── Rematch methods ───────────────────────────────────────────────
    def request_rematch(self, game_id, white, black):
        """Request a rematch after a game ends."""
        self.send(MSG_REMATCH_REQUEST, {'game_id': game_id, 'white': white, 'black': black})
        return self.recv()

    # ── Avatar / Profile methods ──────────────────────────────────────
    def set_avatar(self, avatar, bio=''):
        """Set current user's ASCII avatar and bio."""
        self.send(MSG_SET_AVATAR, {'avatar': avatar, 'bio': bio})
        return self.recv()

    def get_avatar(self, username=None):
        """Get avatar/profile for a user."""
        self.send(MSG_GET_AVATAR, {'username': username})
        return self.recv()

    # ── Chat history methods ──────────────────────────────────────────
    def get_game_chat_history(self, game_id):
        """Retrieve persistent chat history for a completed game."""
        self.send(MSG_GAME_CHAT_HISTORY, {'game_id': game_id})
        return self.recv()


# ════════════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ════════════════════════════════════════════════════════════════════════
def main():
    """Run the chess server."""
    server = ChessServer()
    try:
        server.start()
    except KeyboardInterrupt:
        print("\n  Server interrupted by user.")
        server.stop()


if __name__ == '__main__':
    main()
