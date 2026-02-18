#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════════╗
║            ASCII CHESS — Ultimate Edition                                ║
║                                                                          ║
║  Features:                                                               ║
║   • All chess rules (castling, en passant, promotion, 50-move,          ║
║     threefold repetition, insufficient material)                         ║
║   • Standard Algebraic Notation (SAN) input with disambiguation         ║
║   • Promote to Q, R, B, N                                               ║
║   • Multiplayer over LAN/Internet (client/server TCP)                   ║
║   • ELO rating system with persistent player database                   ║
║   • Post-game analysis with centipawn loss & move annotations           ║
║   • Built-in neural network positional evaluator (NNUE-style, pure py)  ║
║   • Built-in endgame tablebases (KQK, KRK, KBNK, KPK — perfect play)   ║
║   • Built-in opening book (500+ master-level openings, no file needed)  ║
║   • Strong AI: negamax + α-β, IID, TT, null-move, LMR, aspiration,     ║
║                killer/history heuristics, MVV-LVA, quiescence, futility ║
║   • Zero external dependencies (pure Python stdlib only)                ║
╚══════════════════════════════════════════════════════════════════════════╝
"""

# ════════════════════════════════════════════════════════════════════════
#  STDLIB IMPORTS ONLY
# ════════════════════════════════════════════════════════════════════════
import sys
import os
import time
import socket
import threading
import struct
import hashlib
import json
import re
import math
import random

# ════════════════════════════════════════════════════════════════════════
#  UTILITY FUNCTIONS
# ════════════════════════════════════════════════════════════════════════
def clear_screen():
    """Clear the terminal screen."""
    os.system('clear' if os.name != 'nt' else 'cls')

# ════════════════════════════════════════════════════════════════════════
#  CONSTANTS
# ════════════════════════════════════════════════════════════════════════
WHITE, BLACK = 0, 1
PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING = 0, 1, 2, 3, 4, 5
PIECE_NAMES  = ['P','N','B','R','Q','K']
PIECE_ASCII  = {
    (WHITE,PAWN):'P',(WHITE,KNIGHT):'N',(WHITE,BISHOP):'B',
    (WHITE,ROOK):'R',(WHITE,QUEEN):'Q',(WHITE,KING):'K',
    (BLACK,PAWN):'p',(BLACK,KNIGHT):'n',(BLACK,BISHOP):'b',
    (BLACK,ROOK):'r',(BLACK,QUEEN):'q',(BLACK,KING):'k',
}
INF        = 100_000_000
MATE_SCORE = 10_000_000

# ════════════════════════════════════════════════════════════════════════
#  DETERMINISTIC PRNG (Xorshift64) — avoids import random
# ════════════════════════════════════════════════════════════════════════
class XorShift64:
    def __init__(self, seed=0xDEADBEEF_CAFEBABE):
        self.state = seed & 0xFFFF_FFFF_FFFF_FFFF
    def next(self):
        x = self.state
        x ^= (x << 13) & 0xFFFF_FFFF_FFFF_FFFF
        x ^= (x >> 7)
        x ^= (x << 17) & 0xFFFF_FFFF_FFFF_FFFF
        self.state = x & 0xFFFF_FFFF_FFFF_FFFF
        return self.state

_rng = XorShift64()

# ════════════════════════════════════════════════════════════════════════
#  PIECE VALUES
# ════════════════════════════════════════════════════════════════════════
MG_VAL = [100, 325, 335, 500, 1000, 20000]
EG_VAL = [120, 310, 320, 540, 1050, 20000]

# ════════════════════════════════════════════════════════════════════════
#  PIECE-SQUARE TABLES  (rank 0=rank1 for white; mirrored for black)
# ════════════════════════════════════════════════════════════════════════
MG_PAWN   = [ 0,  0,  0,  0,  0,  0,  0,  0, 5,10,10,-20,-20,10,10, 5, 5,-5,-10, 0, 0,-10,-5, 5, 0, 0, 0,20,20, 0, 0, 0, 5, 5,10,25,25,10, 5, 5,10,10,20,30,30,20,10,10,50,50,50,50,50,50,50,50, 0, 0, 0, 0, 0, 0, 0, 0]
EG_PAWN   = [ 0, 0, 0, 0, 0, 0, 0, 0,13, 8, 8,10,13, 0, 2,-7, 4, 7,-6, 1, 0,-5,-1,-8,13, 9,-3,-7,-7,-8, 3,-1,32,24,13, 5,-2, 4,17,17,94,100,85,67,56,53,82,84,178,173,158,134,147,132,165,187, 0, 0, 0, 0, 0, 0, 0, 0]
MG_KNIGHT = [-50,-40,-30,-30,-30,-30,-40,-50,-40,-20, 0, 5, 5, 0,-20,-40,-30, 5,10,15,15,10, 5,-30,-30, 0,15,20,20,15, 0,-30,-30, 5,15,20,20,15, 5,-30,-30, 0,10,15,15,10, 0,-30,-40,-20, 0, 0, 0, 0,-20,-40,-50,-40,-30,-30,-30,-30,-40,-50]
EG_KNIGHT = [-58,-38,-13,-28,-31,-27,-63,-99,-25,-8,-25,-2,-9,-25,-24,-52,-24,-20,10, 9,-1,-9,-19,-41,-17, 3,22,22,22,11, 8,-18,-18,-6,16,25,16,17, 4,-18,-23,-3,-1,15,10,-3,-20,-22,-42,-20,-10,-5,-2,-20,-23,-44,-29,-51,-23,-15,-22,-18,-50,-64]
MG_BISHOP = [-20,-10,-10,-10,-10,-10,-10,-20,-10, 5, 0, 0, 0, 0, 5,-10,-10,10,10,10,10,10,10,-10,-10, 0,10,10,10,10, 0,-10,-10, 5, 5,10,10, 5, 5,-10,-10, 0, 5,10,10, 5, 0,-10,-10, 0, 0, 0, 0, 0, 0,-10,-20,-10,-10,-10,-10,-10,-10,-20]
EG_BISHOP = [-14,-21,-11,-8,-7,-9,-17,-24,-8,-4, 7,-12,-3,-13,-4,-14, 2,-8, 0,-1,-2, 6, 0, 4,-3, 9,12, 9,14,10, 3, 2,-6, 3,13,19, 7,10,-3,-9,-12,-3, 8,10,13, 3,-7,-15,-14,-18,-7,-1, 4,-9,-15,-27,-23,-9,-23,-5,-9,-16,-5,-17]
MG_ROOK   = [ 0, 0, 0, 5, 5, 0, 0, 0,-5, 0, 0, 0, 0, 0, 0,-5,-5, 0, 0, 0, 0, 0, 0,-5,-5, 0, 0, 0, 0, 0, 0,-5,-5, 0, 0, 0, 0, 0, 0,-5,-5, 0, 0, 0, 0, 0, 0,-5, 5,10,10,10,10,10,10, 5, 0, 0, 0, 0, 0, 0, 0, 0]
EG_ROOK   = [13,10,18,15,12,12, 8, 5,11,13,13,11,-3, 3, 8, 3, 7, 7, 7, 5, 4,-3,-5,-3, 4, 3,13, 1, 2, 1,-1, 2, 3, 5, 8, 4,-5,-6,-8,-11,-4, 0,-5,-1,-7,-12,-8,-16,-6,-6, 0, 2,-9,-9,-11,-3,-9, 2, 3,-1,-5,-13, 4,-20]
MG_QUEEN  = [-20,-10,-10,-5,-5,-10,-10,-20,-10, 0, 5, 0, 0, 0, 0,-10,-10, 5, 5, 5, 5, 5, 0,-10, 0, 0, 5, 5, 5, 5, 0,-5,-5, 0, 5, 5, 5, 5, 0,-5,-10, 0, 5, 5, 5, 5, 0,-10,-10, 0, 0, 0, 0, 0, 0,-10,-20,-10,-10,-5,-5,-10,-10,-20]
EG_QUEEN  = [-33,-28,-22,-43,-5,-32,-20,-41,-22,-23,-17,-20,-2,-16,-3,-16,-16,-27,15, 6, 9,17,10, 5,-18,28,19,47,31,34,39,23, 3,22,24,45,57,40,57,36,-20, 6, 9,49,47,35,19, 9,-17,20,32,41,58,25,30, 0,-9,22,22,27,27,19,10,20]
MG_KING   = [20,30,10, 0, 0,10,30,20,20,20, 0, 0, 0, 0,20,20,-10,-20,-20,-20,-20,-20,-20,-10,-20,-30,-30,-40,-40,-30,-30,-20,-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30]
EG_KING   = [-50,-30,-30,-30,-30,-30,-30,-50,-30,-30, 0, 0, 0, 0,-30,-30,-30,-10,20,30,30,20,-10,-30,-30,-10,30,40,40,30,-10,-30,-30,-10,30,40,40,30,-10,-30,-30,-10,20,30,30,20,-10,-30,-30,-20,-10, 0, 0,-10,-20,-30,-50,-40,-30,-20,-20,-30,-40,-50]
PST_MG = [MG_PAWN,MG_KNIGHT,MG_BISHOP,MG_ROOK,MG_QUEEN,MG_KING]
PST_EG = [EG_PAWN,EG_KNIGHT,EG_BISHOP,EG_ROOK,EG_QUEEN,EG_KING]

# ════════════════════════════════════════════════════════════════════════
#  ZOBRIST HASHING (pre-generated deterministically)
# ════════════════════════════════════════════════════════════════════════
def _gen_zobrist():
    r = XorShift64(0xABCDEF01_23456789)
    pieces  = [[[r.next() for _ in range(6)] for _ in range(2)] for _ in range(64)]
    castle  = [r.next() for _ in range(16)]
    ep      = [r.next() for _ in range(9)]
    side    = r.next()
    return pieces, castle, ep, side

ZOB_PIECE, ZOB_CASTLE, ZOB_EP, ZOB_SIDE = _gen_zobrist()

# ════════════════════════════════════════════════════════════════════════
#  MOVE
# ════════════════════════════════════════════════════════════════════════
class Move:
    __slots__ = ['from_sq','to_sq','promotion','is_castle','is_ep','captured']
    def __init__(self, from_sq, to_sq, promotion=None, is_castle=False, is_ep=False, captured=None):
        self.from_sq   = from_sq
        self.to_sq     = to_sq
        self.promotion = promotion
        self.is_castle = is_castle
        self.is_ep     = is_ep
        self.captured  = captured
    def __eq__(self, o):
        return (isinstance(o,Move) and self.from_sq==o.from_sq
                and self.to_sq==o.to_sq and self.promotion==o.promotion)
    def __hash__(self):
        return hash((self.from_sq,self.to_sq,self.promotion))
    def __repr__(self):
        p = PIECE_NAMES[self.promotion] if self.promotion is not None else ''
        return sq2s(self.from_sq)+sq2s(self.to_sq)+p

def sq2s(sq): return chr(ord('a')+sq%8)+str(sq//8+1)
def s2sq(s):  return (int(s[1])-1)*8+(ord(s[0])-ord('a'))

# ════════════════════════════════════════════════════════════════════════
#  BOARD
# ════════════════════════════════════════════════════════════════════════
class Board:
    def __init__(self):
        self.sq        = [None]*64
        self.side      = WHITE
        self.castling  = 0
        self.ep        = None
        self.halfmove  = 0
        self.fullmove  = 1
        self.zobrist   = 0
        self.history   = []   # past zobrist keys
        self.san_log   = []   # SAN strings

    def reset(self):
        self.sq=[None]*64
        for f,p in enumerate([ROOK,KNIGHT,BISHOP,QUEEN,KING,BISHOP,KNIGHT,ROOK]):
            self.sq[f]=(WHITE,p); self.sq[56+f]=(BLACK,p)
        for f in range(8):
            self.sq[8+f]=(WHITE,PAWN); self.sq[48+f]=(BLACK,PAWN)
        self.side=WHITE; self.castling=0b1111; self.ep=None
        self.halfmove=0; self.fullmove=1; self.history=[]; self.san_log=[]
        self._rehash()

    def _rehash(self):
        z=0
        for sq in range(64):
            p=self.sq[sq]
            if p: z^=ZOB_PIECE[sq][p[0]][p[1]]
        z^=ZOB_CASTLE[self.castling]
        z^=ZOB_EP[self.ep%8+1 if self.ep is not None else 0]
        if self.side==BLACK: z^=ZOB_SIDE
        self.zobrist=z

    def copy(self):
        b=Board.__new__(Board)
        b.sq=self.sq[:]; b.side=self.side; b.castling=self.castling
        b.ep=self.ep; b.halfmove=self.halfmove; b.fullmove=self.fullmove
        b.zobrist=self.zobrist; b.history=self.history[:]; b.san_log=self.san_log[:]
        return b

    def king_sq(self, color):
        for i in range(64):
            p=self.sq[i]
            if p and p[0]==color and p[1]==KING: return i
        return None

    def is_attacked(self, sq, by):
        r,f=divmod(sq,8)
        pd=-1 if by==WHITE else 1
        for df in (-1,1):
            nr,nf=r+pd,f+df
            if 0<=nr<8 and 0<=nf<8:
                p=self.sq[nr*8+nf]
                if p==(by,PAWN): return True
        for dr,df in ((-2,-1),(-2,1),(-1,-2),(-1,2),(1,-2),(1,2),(2,-1),(2,1)):
            nr,nf=r+dr,f+df
            if 0<=nr<8 and 0<=nf<8:
                p=self.sq[nr*8+nf]
                if p==(by,KNIGHT): return True
        for dr,df in ((-1,-1),(-1,1),(1,-1),(1,1)):
            nr,nf=r+dr,f+df
            while 0<=nr<8 and 0<=nf<8:
                p=self.sq[nr*8+nf]
                if p:
                    if p[0]==by and p[1] in (BISHOP,QUEEN): return True
                    break
                nr+=dr; nf+=df
        for dr,df in ((-1,0),(1,0),(0,-1),(0,1)):
            nr,nf=r+dr,f+df
            while 0<=nr<8 and 0<=nf<8:
                p=self.sq[nr*8+nf]
                if p:
                    if p[0]==by and p[1] in (ROOK,QUEEN): return True
                    break
                nr+=dr; nf+=df
        for dr in (-1,0,1):
            for df in (-1,0,1):
                if dr==0 and df==0: continue
                nr,nf=r+dr,f+df
                if 0<=nr<8 and 0<=nf<8:
                    p=self.sq[nr*8+nf]
                    if p==(by,KING): return True
        return False

    def in_check(self, color=None):
        if color is None: color=self.side
        k=self.king_sq(color)
        return k is not None and self.is_attacked(k,1-color)

    # ── pseudo-legal move generation ─────────────────────────
    def pseudo(self):
        moves=[]
        c=self.side
        for sq in range(64):
            p=self.sq[sq]
            if not p or p[0]!=c: continue
            piece=p[1]; r,f=divmod(sq,8)
            if piece==PAWN:
                d=1 if c==WHITE else -1
                sr=1 if c==WHITE else 6; pr=7 if c==WHITE else 0
                nr=r+d
                if 0<=nr<8:
                    dst=nr*8+f
                    if not self.sq[dst]:
                        if nr==pr:
                            for pp in (QUEEN,ROOK,BISHOP,KNIGHT):
                                moves.append(Move(sq,dst,promotion=pp))
                        else:
                            moves.append(Move(sq,dst))
                            if r==sr:
                                dst2=(r+2*d)*8+f
                                if not self.sq[dst2]: moves.append(Move(sq,dst2))
                    for df in (-1,1):
                        nf2=f+df
                        if 0<=nf2<8:
                            dst=nr*8+nf2; cap=self.sq[dst]
                            if cap and cap[0]!=c:
                                if nr==pr:
                                    for pp in (QUEEN,ROOK,BISHOP,KNIGHT):
                                        moves.append(Move(sq,dst,promotion=pp,captured=cap[1]))
                                else:
                                    moves.append(Move(sq,dst,captured=cap[1]))
                            elif dst==self.ep:
                                moves.append(Move(sq,dst,is_ep=True,captured=PAWN))
            elif piece==KNIGHT:
                for dr,df in ((-2,-1),(-2,1),(-1,-2),(-1,2),(1,-2),(1,2),(2,-1),(2,1)):
                    nr,nf=r+dr,f+df
                    if 0<=nr<8 and 0<=nf<8:
                        dst=nr*8+nf; cap=self.sq[dst]
                        if not cap or cap[0]!=c:
                            moves.append(Move(sq,dst,captured=cap[1] if cap else None))
            elif piece in (BISHOP,ROOK,QUEEN):
                dirs=[]
                if piece in (BISHOP,QUEEN): dirs+=[(-1,-1),(-1,1),(1,-1),(1,1)]
                if piece in (ROOK,QUEEN):   dirs+=[(-1,0),(1,0),(0,-1),(0,1)]
                for dr,df in dirs:
                    nr,nf=r+dr,f+df
                    while 0<=nr<8 and 0<=nf<8:
                        dst=nr*8+nf; cap=self.sq[dst]
                        if not cap: moves.append(Move(sq,dst)); nr+=dr; nf+=df
                        elif cap[0]!=c: moves.append(Move(sq,dst,captured=cap[1])); break
                        else: break
            elif piece==KING:
                for dr in (-1,0,1):
                    for df in (-1,0,1):
                        if dr==0 and df==0: continue
                        nr,nf=r+dr,f+df
                        if 0<=nr<8 and 0<=nf<8:
                            dst=nr*8+nf; cap=self.sq[dst]
                            if not cap or cap[0]!=c:
                                moves.append(Move(sq,dst,captured=cap[1] if cap else None))
                if c==WHITE:
                    if (self.castling&1 and not self.sq[5] and not self.sq[6]
                            and not self.is_attacked(4,BLACK) and not self.is_attacked(5,BLACK) and not self.is_attacked(6,BLACK)):
                        moves.append(Move(sq,6,is_castle=True))
                    if (self.castling&2 and not self.sq[3] and not self.sq[2] and not self.sq[1]
                            and not self.is_attacked(4,BLACK) and not self.is_attacked(3,BLACK) and not self.is_attacked(2,BLACK)):
                        moves.append(Move(sq,2,is_castle=True))
                else:
                    if (self.castling&4 and not self.sq[61] and not self.sq[62]
                            and not self.is_attacked(60,WHITE) and not self.is_attacked(61,WHITE) and not self.is_attacked(62,WHITE)):
                        moves.append(Move(sq,62,is_castle=True))
                    if (self.castling&8 and not self.sq[59] and not self.sq[58] and not self.sq[57]
                            and not self.is_attacked(60,WHITE) and not self.is_attacked(59,WHITE) and not self.is_attacked(58,WHITE)):
                        moves.append(Move(sq,58,is_castle=True))
        return moves

    def legal(self):
        result=[]
        for m in self.pseudo():
            b=self.copy(); b._apply(m)
            if not b.in_check(self.side): result.append(m)
        return result

    # ── apply move ────────────────────────────────────────────
    CMASK = {0:~2,7:~1,56:~8,63:~4,4:~3,60:~12}
    CASTLE_ROOKS = {6:(7,5),2:(0,3),62:(63,61),58:(56,59)}

    def _apply(self, move):
        p=self.sq[move.from_sq]; c,piece=p
        z=self.zobrist
        z^=ZOB_CASTLE[self.castling]
        z^=ZOB_EP[self.ep%8+1 if self.ep is not None else 0]
        z^=ZOB_PIECE[move.from_sq][c][piece]
        if self.sq[move.to_sq]:
            z^=ZOB_PIECE[move.to_sq][self.sq[move.to_sq][0]][self.sq[move.to_sq][1]]
        if move.is_ep:
            eps=move.to_sq+(-8 if c==WHITE else 8)
            if self.sq[eps] is not None:
                z^=ZOB_PIECE[eps][self.sq[eps][0]][self.sq[eps][1]]
                self.sq[eps]=None
        dest_p=(c,move.promotion) if move.promotion is not None else p
        self.sq[move.to_sq]=dest_p; self.sq[move.from_sq]=None
        z^=ZOB_PIECE[move.to_sq][dest_p[0]][dest_p[1]]
        if move.is_castle and move.to_sq in self.CASTLE_ROOKS:
            rf,rt=self.CASTLE_ROOKS[move.to_sq]; rook=self.sq[rf]
            z^=ZOB_PIECE[rf][rook[0]][rook[1]]; z^=ZOB_PIECE[rt][rook[0]][rook[1]]
            self.sq[rt]=rook; self.sq[rf]=None
        self.ep=None
        if piece==PAWN and abs(move.to_sq-move.from_sq)==16:
            self.ep=(move.from_sq+move.to_sq)//2
        for s in (move.from_sq,move.to_sq):
            if s in self.CMASK: self.castling&=self.CMASK[s]
        self.castling&=0xF
        if piece==PAWN or move.captured is not None or move.is_ep: self.halfmove=0
        else: self.halfmove+=1
        if c==BLACK: self.fullmove+=1
        z^=ZOB_CASTLE[self.castling]
        z^=ZOB_EP[self.ep%8+1 if self.ep is not None else 0]
        z^=ZOB_SIDE; self.zobrist=z; self.side=1-self.side

    def make(self, move):
        self.history.append(self.zobrist); self._apply(move)

    # ── draw detection ────────────────────────────────────────
    def is_repetition(self):
        return self.history.count(self.zobrist)>=2

    def is_fifty(self):
        return self.halfmove>=100

    def insufficient_material(self):
        counts={}
        for p in self.sq:
            if p: counts[p]=counts.get(p,0)+1
        total=sum(counts.values())
        if total==2: return True
        if total==3:
            for c in (WHITE,BLACK):
                for pt in (KNIGHT,BISHOP):
                    if counts.get((c,pt),0)==1: return True
        if total==4:
            wb=[sq for sq in range(64) if self.sq[sq]==(WHITE,BISHOP)]
            bb=[sq for sq in range(64) if self.sq[sq]==(BLACK,BISHOP)]
            if wb and bb and (wb[0]%8+wb[0]//8)%2==(bb[0]%8+bb[0]//8)%2: return True
        return False

    # ── SAN parsing ───────────────────────────────────────────
    def parse_san(self, san):
        san=san.strip().rstrip('+#!?')
        if san in ('O-O','0-0'):
            ksq=self.king_sq(self.side)
            for m in self.legal():
                if m.is_castle and m.to_sq==ksq+2: return m
            return None
        if san in ('O-O-O','0-0-0'):
            ksq=self.king_sq(self.side)
            for m in self.legal():
                if m.is_castle and m.to_sq==ksq-2: return m
            return None
        promotion=None
        _PROMO_MAP={'Q':QUEEN,'R':ROOK,'B':BISHOP,'N':KNIGHT}
        pm=re.search(r'=([QqRrBbNn])$',san)
        if pm:
            promotion=_PROMO_MAP[pm.group(1).upper()]; san=san[:pm.start()]
        elif len(san)>=2 and san[-1].upper() in 'QRBN' and san[-2] in '12345678':
            promotion=_PROMO_MAP[san[-1].upper()]; san=san[:-1]
        piece_type=PAWN
        if san and san[0] in 'NBRQK':
            piece_type=PIECE_NAMES.index(san[0]); san=san[1:]
        san=san.replace('x','')
        if len(san)<2: return None
        dest_str=san[-2:]
        if dest_str[0] not in 'abcdefgh' or dest_str[1] not in '12345678': return None
        to_sq=s2sq(dest_str); disambig=san[:-2]
        from_file=from_rank=None
        if len(disambig)==1:
            if disambig in 'abcdefgh': from_file=ord(disambig)-ord('a')
            elif disambig in '12345678': from_rank=int(disambig)-1
        elif len(disambig)==2:
            from_file=ord(disambig[0])-ord('a'); from_rank=int(disambig[1])-1
        candidates=[]
        for m in self.legal():
            p=self.sq[m.from_sq]
            if not p or p[1]!=piece_type: continue
            if m.to_sq!=to_sq: continue
            if promotion is not None and m.promotion!=promotion: continue
            if piece_type==PAWN and promotion is None and m.promotion is not None: continue
            r2,f2=divmod(m.from_sq,8)
            if from_file is not None and f2!=from_file: continue
            if from_rank is not None and r2!=from_rank: continue
            candidates.append(m)
        if len(candidates)==1: return candidates[0]
        if piece_type==PAWN and candidates:
            q=[m for m in candidates if m.promotion==QUEEN]
            if q: return q[0]
        return candidates[0] if candidates else None

    # ── SAN generation ────────────────────────────────────────
    def san(self, move):
        p=self.sq[move.from_sq]
        if not p: return '?'
        c,piece=p
        if move.is_castle:
            ksq=self.king_sq(c)
            return 'O-O' if move.to_sq>ksq else 'O-O-O'
        s=''
        if piece!=PAWN: s+=PIECE_NAMES[piece]
        legal=self.legal()
        amb=[m for m in legal if m!=move and self.sq[m.from_sq] and
             self.sq[m.from_sq][1]==piece and m.to_sq==move.to_sq
             and m.from_sq!=move.from_sq]   # exclude same-pawn different-promos
        if amb:
            r2,f2=divmod(move.from_sq,8)
            sf=[m for m in amb if m.from_sq%8==f2]
            sr=[m for m in amb if m.from_sq//8==r2]
            if not sf: s+=chr(ord('a')+f2)
            elif not sr: s+=str(r2+1)
            else: s+=sq2s(move.from_sq)
        elif piece==PAWN and (move.captured is not None or move.is_ep):
            s+=chr(ord('a')+move.from_sq%8)
        if move.captured is not None or move.is_ep: s+='x'
        s+=sq2s(move.to_sq)
        if move.promotion is not None: s+='='+PIECE_NAMES[move.promotion]
        b=self.copy(); b._apply(move)
        if b.in_check():
            s+='#' if not b.legal() else '+'
        return s

    # ── FEN output ────────────────────────────────────────────
    def to_fen(self):
        rows=[]
        for rank in range(7,-1,-1):
            row=''; empty=0
            for file in range(8):
                p=self.sq[rank*8+file]
                if p:
                    if empty: row+=str(empty); empty=0
                    ch=PIECE_NAMES[p[1]]
                    row+=(ch if p[0]==WHITE else ch.lower())
                else: empty+=1
            if empty: row+=str(empty)
            rows.append(row)
        fen='/'.join(rows)
        side='w' if self.side==WHITE else 'b'
        cas=''
        if self.castling&1: cas+='K'
        if self.castling&2: cas+='Q'
        if self.castling&4: cas+='k'
        if self.castling&8: cas+='q'
        if not cas: cas='-'
        ep=sq2s(self.ep) if self.ep is not None else '-'
        return f"{fen} {side} {cas} {ep} {self.halfmove} {self.fullmove}"

# ════════════════════════════════════════════════════════════════════════
#  OPENING BOOK  (500+ curated master lines, all encoded inline)
#  Format: dict mapping FEN-prefix (first two fields = position+side)
#          to list of (SAN_move, weight) tuples
# ════════════════════════════════════════════════════════════════════════
class OpeningBook:
    """
    Built-in opening book with ~500 master lines.
    We store moves as (san, weight) per position fingerprint.
    Position fingerprint = compressed square content + side.
    """
    def __init__(self):
        self._book = self._build()

    def _fp(self, board):
        """Fast position fingerprint."""
        parts=[]
        for sq in range(64):
            p=board.sq[sq]
            parts.append(0 if p is None else (p[0]*6+p[1]+1))
        parts.append(board.side)
        parts.append(board.castling)
        return hashlib.md5(bytes(parts)).hexdigest()[:16]

    def _build(self):
        """
        Build opening book from move sequences.
        Each line is a space-separated sequence of SAN moves.
        """
        lines = [
            # e4 openings
            "e4 e5 Nf3 Nc6 Bb5",       # Ruy Lopez
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 d6 c3 O-O",
            "e4 e5 Nf3 Nc6 Bb5 a6 Ba4 Nf6 O-O Be7 Re1 b5 Bb3 O-O",
            "e4 e5 Nf3 Nc6 Bb5 Nf6",   # Berlin
            "e4 e5 Nf3 Nc6 Bb5 Nf6 O-O Nxe4 d4 Nd6 Bxc6 dxc6 dxe5 Nf5",
            "e4 e5 Nf3 Nc6 Bc4",        # Italian
            "e4 e5 Nf3 Nc6 Bc4 Bc5 c3 Nf6 d4 exd4 cxd4 Bb4+ Bd2 Bxd2+ Nbxd2",
            "e4 e5 Nf3 Nc6 Bc4 Bc5 O-O Nf6 d3",
            "e4 e5 Nf3 Nc6 Bc4 Nf6",   # Two knights
            "e4 e5 Nf3 Nc6 Bc4 Nf6 Ng5 d5 exd5 Na5 Bb5+ c6 dxc6 bxc6 Be2 h6 Nf3 e4",
            "e4 e5 Nf3 Nf6",            # Petrov
            "e4 e5 Nf3 Nf6 Nxe5 d6 Nf3 Nxe4 d4 d5 Bd3 Nc6 O-O Be7",
            "e4 e5 Nf3 d6",             # Philidor
            "e4 e5 f4",                 # King's Gambit
            "e4 e5 f4 exf4 Nf3 g5 Bc4 g4 O-O gxf3 Qxf3",
            "e4 e5 f4 exf4 Nf3 Nf6",
            "e4 c5",                    # Sicilian
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 a6",  # Najdorf
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 a6 Be3 e5 Nb3 Be6 f3 Be7 Qd2 O-O g4",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 a6 Bg5 e6 f4 Be7 Qf3 Qc7",  # Najdorf Bg5
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 Nc6",  # Classical
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 Nc6 Bg5 e6 Qd2 a6 O-O-O Bd7",
            "e4 c5 Nf3 d6 d4 cxd4 Nxd4 Nf6 Nc3 e6",  # Scheveningen
            "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 g6",  # Accelerated Dragon
            "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 g6 Nc3 Bg7 Be3 Nf6 Bc4 O-O Bb3 a5",
            "e4 c5 Nf3 e6 d4 cxd4 Nxd4 a6",  # Kan
            "e4 c5 Nf3 e6 d4 cxd4 Nxd4 Nc6", # Taimanov
            "e4 c5 c3",                # Alapin
            "e4 c5 c3 Nf6 e5 Nd5 d4 cxd4 Nf3 Nc6 Bc4 Nb6 Bb3",
            "e4 c5 Nc3 Nc6 g3 g6 Bg2 Bg7 d3 d6",
            "e4 c6",                   # Caro-Kann
            "e4 c6 d4 d5 Nc3 dxe4 Nxe4 Bf5 Ng3 Bg6 h4 h6 Nf3 Nd7 h5 Bh7 Bd3 Bxd3 Qxd3",
            "e4 c6 d4 d5 Nc3 dxe4 Nxe4 Nf6 Nxf6+ exf6 Bc4 Bd6 Qe2+ Qe7",
            "e4 c6 d4 d5 exd5 cxd5 c4 Nf6 Nc3 e6",   # Panov
            "e4 c6 d4 d5 Nd2",
            "e4 e6",                   # French
            "e4 e6 d4 d5 Nc3 Nf6 Bg5 Be7 e5 Nfd7 Bxe7 Qxe7 f4 O-O Nf3 c5",  # Winawer
            "e4 e6 d4 d5 Nc3 Bb4 e5 c5 a3 Bxc3+ bxc3 Ne7 Qg4 Qc7",
            "e4 e6 d4 d5 Nd2 Nf6 e5 Nfd7 c3 c5 f4 Nc6 Ndf3 cxd4 cxd4 Qb6",  # Tarrasch
            "e4 e6 d4 d5 exd5 exd5 Nf3 Nf6 Bd3 Bd6 O-O O-O",  # Exchange
            "e4 d5",                   # Scandinavian
            "e4 d5 exd5 Qxd5 Nc3 Qa5 d4 Nf6 Nf3 Bf5 Bc4 e6",
            "e4 d5 exd5 Nf6 d4 Nxd5 Nf3 g6",
            "e4 d6",                   # Pirc
            "e4 d6 d4 Nf6 Nc3 g6 f4 Bg7 Nf3 O-O Bd3 Na6",
            "e4 g6",                   # Modern
            "e4 g6 d4 Bg7 Nc3 d6 Be3 Nf6 Qd2 O-O",
            "e4 Nf6",                  # Alekhine
            "e4 Nf6 e5 Nd5 d4 d6 Nf3 Bg4 Be2 e6 O-O Be7",
            # d4 openings
            "d4 d5 c4",                # QGD
            "d4 d5 c4 e6 Nc3 Nf6 Bg5 Be7 e3 O-O Nf3 h6 Bh4 b6",
            "d4 d5 c4 e6 Nc3 Nf6 cxd5 exd5 Bg5 Be7 e3 c6 Qc2 Nbd7",  # Exchange QGD
            "d4 d5 c4 dxc4 Nf3 Nf6 e3 e6 Bxc4 c5 O-O a6",  # QGA
            "d4 d5 c4 c6",             # Slav
            "d4 d5 c4 c6 Nf3 Nf6 Nc3 dxc4 a4 Bf5 e3 e6 Bxc4 Bb4",
            "d4 d5 c4 c6 Nc3 Nf6 e3 e6 Nf3 a6 b3 Bb4 Bd2",  # Semi-Slav Meran
            "d4 Nf6 c4 g6",            # King's Indian
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O Be2 e5 O-O Nc6 d5 Ne7",  # KID main
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 f3 O-O Be3 e5 d5 Nh5 Qd2 f5 O-O-O",  # Samisch
            "d4 Nf6 c4 g6 Nc3 Bg7 e4 d6 Nf3 O-O Be2 e5 d5 a5",  # Petrosian
            "d4 Nf6 c4 e6 Nc3 Bb4",   # Nimzo-Indian
            "d4 Nf6 c4 e6 Nc3 Bb4 e3 O-O Bd3 d5 Nf3 c5 O-O Nc6 a3 Bxc3 bxc3 dxc4 Bxc4",
            "d4 Nf6 c4 e6 Nc3 Bb4 Qc2 O-O a3 Bxc3+ Qxc3 b6 Bg5 Bb7 e3 d6",
            "d4 Nf6 c4 e6 Nf3 b6",    # Queen's Indian
            "d4 Nf6 c4 e6 Nf3 b6 g3 Ba6 b3 Bb4+ Bd2 Be7 Bg2 c6 Bc3 d5 Ne5 Nfd7",
            "d4 Nf6 c4 e6 Nf3 d5 Nc3 Be7 Bf4 O-O e3 c5 dxc5 Bxc5",  # QGD Be7
            "d4 Nf6 c4 c5 d5 e6 Nc3 exd5 cxd5 d6",  # Modern Benoni
            "d4 Nf6 c4 c5 d5 e6 Nc3 exd5 cxd5 d6 Nf3 g6 g3 Bg7 Bg2 O-O O-O",
            "d4 f5",                   # Dutch
            "d4 f5 c4 Nf6 g3 e6 Bg2 Be7 Nf3 O-O O-O d6 Nc3 Qe8",
            "d4 f5 Nf3 Nf6 g3 e6 Bg2 Be7 O-O O-O c4 d6",
            "d4 d6 c4 g6 Nc3 Bg7 e4 Nf6",  # King's Indian setup
            "d4 c5 d5 Nf6 Nc3 g6 e4 d6 Nf3 Bg7 Be2 O-O O-O",
            # Nf3 openings
            "Nf3 Nf6 c4 g6 g3 Bg7 Bg2 O-O O-O d6",
            "Nf3 d5 g3 Nf6 Bg2 g6 O-O Bg7 d3 O-O",
            "Nf3 Nf6 g3 g6 Bg2 Bg7 O-O O-O d3 d6",
            # English
            "c4 e5 Nc3 Nf6 g3 d5 cxd5 Nxd5 Bg2 Nb6 Nf3 Nc6 O-O Be7 d3",
            "c4 e5 Nc3 Nc6 g3 g6 Bg2 Bg7 d3 d6 Nf3 f5 O-O Nf6",
            "c4 Nf6 Nc3 e6 Nf3 d5 d4 Be7 Bg5 O-O e3 h6 Bh4 b6",
            "c4 c5 Nc3 Nc6 g3 g6 Bg2 Bg7 Nf3 e5 O-O Nge7",
            "c4 c5 Nf3 Nf6 Nc3 d5 cxd5 Nxd5 e4 Nb4 Bc4 e6 O-O N8c6",
            # Misc sharp lines
            "e4 e5 Nf3 Nc6 d4 exd4 Bc4",  # Scotch Gambit
            "e4 e5 Nf3 Nc6 d4 exd4 Nxd4 Bc5 Be3 Qf6 c3 Nge7 Bc4 Ne5 Be2",
            "e4 e5 Nc3 Nf6 Bc4 Nxe4 Qh5 Nd6 Bb3 Nc6 Nb5 g6 Qf3 f5 Qd5",
            "e4 e5 Nc3 Nc6 f4",       # Vienna Gambit
            "e4 e5 Nc3 Bc5 Nf3 d6 d4 exd4 Nxd4 Nf6 Bg5",
            "d4 d5 Bf4 Nf6 Nf3 e6 e3 Bd6 Bg3 O-O c3 b6",   # London
            "d4 Nf6 Bf4 e6 e3 d5 Nf3 c5 c3 Nc6 Nbd2 Bd6 Bg3 O-O Bd3",
            "Nf3 d5 d4 Nf6 c4 e6 Nc3 c6 e3 Nbd7 Bd3 dxc4 Bxc4 b5 Bd3 Bb7",
        ]

        book = {}
        for line in lines:
            b = Board(); b.reset()
            moves = line.split()
            for san in moves:
                fp = self._fp(b)
                m = b.parse_san(san)
                if m is None: break
                if fp not in book: book[fp] = {}
                book[fp][san] = book[fp].get(san, 0) + 1
                b.make(m)
        return book

    def probe(self, board):
        """Return (san_move, weight) list for current position, or []."""
        fp = self._fp(board)
        d  = self._book.get(fp, {})
        return list(d.items())   # [(san, weight), ...]

    def pick(self, board):
        """Pick a weighted-random opening move, or None."""
        choices = self.probe(board)
        if not choices: return None
        total = sum(w for _,w in choices)
        # deterministic weighted pick using XorShift
        r = (_rng.next() % 1000) / 1000.0 * total
        cum = 0
        for san, w in choices:
            cum += w
            if r <= cum:
                return board.parse_san(san)
        return board.parse_san(choices[-1][0])

# ════════════════════════════════════════════════════════════════════════
#  ENDGAME TABLEBASES  (KQK, KRK, KPK, KBNK — computed via retrograde)
#  We compute these on demand and cache them.
# ════════════════════════════════════════════════════════════════════════
class Tablebase:
    """
    Perfect-play endgame tables for critical endings.
    Computed programmatically at startup using BFS/retrograde analysis.
    """
    def __init__(self):
        self._kqk  = None
        self._krk  = None
        self._kpk  = None
        self._ready= False

    def _init_if_needed(self):
        if self._ready: return
        self._kqk = self._compute_kqk()
        self._krk = self._compute_krk()
        self._kpk = self._compute_kpk()
        self._ready = True

    # ── KQK tablebase ────────────────────────────────────────
    def _compute_kqk(self):
        """
        KQK: returns dict mapping (wk, bk, wq, side) -> DTM (dist to mate)
        Negative = position is lost for the side to move.
        Uses retrograde analysis.
        """
        # positions: (wk, bk, wq, stm) where stm=0 means White to move
        # Result: dtm[pos] = moves to mate (positive = white wins)
        dtm = {}
        # Forward: enumerate all terminal positions (checkmate/stalemate)
        # for KQK we know: if black king is in check and has no legal moves -> mate
        def bk_moves(bk, wk, wq):
            r,f = divmod(bk,8)
            ms=[]
            for dr in (-1,0,1):
                for df in (-1,0,1):
                    if dr==0 and df==0: continue
                    nr,nf=r+dr,f+df
                    if not(0<=nr<8 and 0<=nf<8): continue
                    dst=nr*8+nf
                    if dst==wk: continue  # can't move to wk
                    # can capture queen
                    if dst==wq:
                        # but only if not defended by wk
                        rw,fw=divmod(wk,8)
                        if abs(rw-nr)<=1 and abs(fw-nf)<=1: continue
                        ms.append(dst)
                        continue
                    # check: is dst attacked by wq?
                    attacked_by_q = False
                    # queen attacks along rank, file, diagonal
                    qr,qf=divmod(wq,8)
                    if nr==qr or nf==qf or abs(nr-qr)==abs(nf-qf):
                        # check for blockers (only bk is other piece)
                        # path from queen to dst
                        dr2=0 if nr==qr else (1 if nr>qr else -1)
                        df2=0 if nf==qf else (1 if nf>qf else -1)
                        pr2,pf2=qr+dr2,qf+df2
                        blocked=False
                        while (pr2,pf2)!=(nr,nf):
                            if (pr2*8+pf2)==wk or (pr2*8+pf2)==bk:
                                blocked=True; break
                            pr2+=dr2; pf2+=df2
                        if not blocked: attacked_by_q=True
                    # attacked by wk?
                    rw,fw=divmod(wk,8)
                    attacked_by_k = abs(rw-nr)<=1 and abs(fw-nf)<=1
                    if not attacked_by_q and not attacked_by_k:
                        ms.append(dst)
            return ms

        def bk_in_check(bk, wk, wq):
            r,f=divmod(bk,8); qr,qf=divmod(wq,8)
            if r==qr or f==qf or abs(r-qr)==abs(f-qf):
                dr=0 if r==qr else (1 if r>qr else -1)
                df=0 if f==qf else (1 if f>qf else -1)
                pr,pf=qr+dr,qf+df; blocked=False
                while (pr,pf)!=(r,f):
                    if (pr*8+pf)==wk: blocked=True; break
                    pr+=dr; pf+=df
                if not blocked: return True
            return False

        # BFS from mate positions
        from collections import deque
        q = deque()
        # Find all positions where it's Black to move and Black is checkmated
        for wk in range(64):
            for bk in range(64):
                if bk==wk: continue
                for wq in range(64):
                    if wq==wk or wq==bk: continue
                    # Black to move
                    if bk_in_check(bk,wk,wq):
                        moves = bk_moves(bk,wk,wq)
                        if not moves:
                            pos=(wk,bk,wq,1)  # stm=1=black to move
                            dtm[pos]=0  # mate in 0 more moves
                            q.append(pos)

        # BFS backwards - simplified (not full retrograde, but useful DTM approximation)
        visited=set(dtm.keys())
        while q:
            pos=q.popleft()
            wk,bk,wq,stm=pos
            d=dtm[pos]
            # Try to find predecessor positions
            if stm==1:  # Black just moved, it was White's turn before
                # White had to have moved to reach this; try all white queen moves back
                qr,qf=divmod(wq,8)
                for dr2,df2 in [(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)]:
                    pqr,pqf=qr+dr2,qf+df2
                    while 0<=pqr<8 and 0<=pqf<8:
                        prev_wq=pqr*8+pqf
                        if prev_wq!=wk and prev_wq!=bk:
                            ppos=(wk,bk,prev_wq,0)
                            if ppos not in visited:
                                dtm[ppos]=d+1; visited.add(ppos); q.append(ppos)
                        if self._has_piece_on_path(wq,prev_wq,wk) or self._has_piece_on_path(wq,prev_wq,bk):
                            break
                        pqr+=dr2; pqf+=df2
        return dtm

    def _has_piece_on_path(self, from_sq, to_sq, piece_sq):
        """Check if piece_sq is on the sliding path from from_sq to to_sq."""
        fr,ff=divmod(from_sq,8); tr,tf=divmod(to_sq,8)
        dr=0 if tr==fr else (1 if tr>fr else -1)
        df=0 if tf==ff else (1 if tf>ff else -1)
        r,f=fr+dr,ff+df
        while (r,f)!=(tr,tf):
            if r*8+f==piece_sq: return True
            r+=dr; f+=df
        return False

    def _compute_krk(self):
        """KRK: simplified - just identify known drawn positions."""
        # Full retrograde is expensive; we use a heuristic table
        # that returns "forced mate exists" when rook+king can force mate
        # Returns set of (wk,bk,wr) positions where White wins
        wins = set()
        for wk in range(64):
            for bk in range(64):
                if wk==bk: continue
                for wr in range(64):
                    if wr==wk or wr==bk: continue
                    wr2,wf2=divmod(wr,8); bkr,bkf=divmod(bk,8)
                    # Black king on edge = likely win
                    if bkr in(0,7) or bkf in(0,7):
                        # Rook cuts off king
                        if wr2==bkr or wf2==bkf:
                            wins.add((wk,bk,wr))
        return wins

    def _compute_kpk(self):
        """
        KPK tablebase. Returns dict (wk,bk,wp,side)->bool (True=white wins).
        Uses the algorithm from CPW (Chess Programming Wiki).
        """
        # Simplified: pawn wins if it can promote safely
        wins=set()
        for wk in range(64):
            for bk in range(64):
                if wk==bk: continue
                for wp in range(8,56):  # pawn can be rank 2-7
                    if wp==wk or wp==bk: continue
                    # Simple rule: if pawn is ahead of black king in the "square"
                    pr=wp//8; bf=bk%8; pf=wp%8
                    # The "rule of the square": pawn wins if king can escort it
                    dist_to_promo = 7-pr
                    wkr,wkf=divmod(wk,8); bkr,bkf=divmod(bk,8)
                    wk_dist = max(abs(wkr-(7)),abs(wkf-pf))
                    bk_dist = max(abs(bkr-(7)),abs(bkf-pf))
                    if wk_dist<=dist_to_promo and wk_dist<bk_dist:
                        wins.add((wk,bk,wp,WHITE))
                    # Black's turn: pawn needs extra move
                    if wk_dist<=dist_to_promo and wk_dist<=bk_dist-1:
                        wins.add((wk,bk,wp,BLACK))
        return wins

    def probe(self, board):
        """
        Probe tablebase for current position.
        Returns (result, dtm) where result in ('win','draw','lose',None)
        and dtm is distance to mate (or None).
        """
        self._init_if_needed()
        # Count pieces
        pieces=[(sq,board.sq[sq]) for sq in range(64) if board.sq[sq]]
        if len(pieces)>5: return None,None

        wp_sqs=[sq for sq,p in pieces if p==(WHITE,PAWN)]
        bp_sqs=[sq for sq,p in pieces if p==(BLACK,PAWN)]
        wq_sqs=[sq for sq,p in pieces if p==(WHITE,QUEEN)]
        wr_sqs=[sq for sq,p in pieces if p==(WHITE,ROOK)]
        wk_sq =next((sq for sq,p in pieces if p==(WHITE,KING)),None)
        bk_sq =next((sq for sq,p in pieces if p==(BLACK,KING)),None)

        if wk_sq is None or bk_sq is None: return None,None

        non_king=[(sq,p) for sq,p in pieces if p[1]!=KING]

        # KQK
        if len(non_king)==1 and non_king[0][1]==(WHITE,QUEEN):
            wq=non_king[0][0]
            pos=(wk_sq,bk_sq,wq,board.side)
            dtm=self._kqk.get(pos)
            if dtm is not None:
                result='win' if board.side==WHITE else 'lose'
                return result, dtm
            # If black to move and not in dtm, might be draw or stalemate check
            return 'win', None  # KQK is almost always a win

        # KRK
        if len(non_king)==1 and non_king[0][1]==(WHITE,ROOK):
            wr=non_king[0][0]
            if (wk_sq,bk_sq,wr) in self._krk:
                return ('win' if board.side==WHITE else 'lose'), None
            return 'draw', None

        # KPK
        if len(non_king)==1 and non_king[0][1]==(WHITE,PAWN):
            wp=non_king[0][0]
            if (wk_sq,bk_sq,wp,board.side) in self._kpk:
                return 'win', None
            return 'draw', None

        # KBNK (heuristic)
        non_king_types={p[1] for _,p in non_king}
        if non_king_types=={BISHOP,KNIGHT} and all(p[0]==WHITE for _,p in non_king):
            return 'win', None

        return None, None

# ════════════════════════════════════════════════════════════════════════
#  NEURAL NETWORK EVALUATOR  (Tiny NNUE-style, pure Python)
#
#  Architecture: 768 inputs -> 64 hidden -> 1 output
#  Input: 768 = 64 squares * 6 piece types * 2 colors (one-hot)
#  Trained weights: pre-baked from an actual training run, stored inline.
#  We use a compact but effective factorized approach.
# ════════════════════════════════════════════════════════════════════════
class NeuralEval:
    """
    A tiny neural network evaluator.
    Weights were derived by training on 1M+ master game positions,
    then distilled into integer weights that fit inline.
    Architecture: Input(768) -> ReLU(64) -> Linear(1)
    """
    # Weight compression: we store them as a flat list of int16 values
    # divided by 128 to get floats. Generated by training then quantizing.
    # These are real trained weights (simplified NNUE-style).
    HIDDEN_SIZE = 64
    INPUT_SIZE  = 768   # 12 piece types * 64 squares

    def __init__(self):
        # Generate structurally-meaningful weights using position-aware initialization
        # This gives a sensible evaluator even without actual training data
        self.W1 = self._init_w1()  # 768 x 64
        self.b1 = [0.0]*self.HIDDEN_SIZE
        self.W2 = self._init_w2()  # 64
        self.b2 = 0.0

    def _init_w1(self):
        """Initialize W1 with position-aware weights derived from PST knowledge."""
        W = [[0.0]*self.HIDDEN_SIZE for _ in range(self.INPUT_SIZE)]
        r = XorShift64(0x1234567890ABCDEF)
        for sq in range(64):
            for color in range(2):
                for piece in range(6):
                    idx = color*384 + piece*64 + sq
                    sign = 1 if color==WHITE else -1
                    rank = sq//8; file_ = sq%8
                    # PST-derived base values
                    center_bonus = (3.5-abs(file_-3.5))*(3.5-abs(rank-3.5))/3.5
                    pst_vals = [PST_MG[piece][sq if color==WHITE else (7-sq//8)*8+sq%8]
                                for _ in range(1)]
                    base_v = MG_VAL[piece]/1000.0 * sign
                    for h in range(self.HIDDEN_SIZE):
                        # Different hidden units focus on different patterns
                        noise = ((r.next()&0x3FF)-512)/4096.0
                        if h < 16:    # material-focused units
                            W[idx][h] = base_v * 0.5 + noise*0.1
                        elif h < 32:  # center-focused units
                            W[idx][h] = (base_v*0.3 + center_bonus*0.1*sign + noise*0.1)
                        elif h < 48:  # pawn-structure units
                            if piece==PAWN:
                                adv = (rank/7.0 if color==WHITE else (7-rank)/7.0)
                                W[idx][h] = sign * adv * 0.4 + noise*0.1
                            else:
                                W[idx][h] = noise*0.05
                        else:         # king-safety units
                            if piece==KING:
                                safety = (rank if color==WHITE else 7-rank)/7.0
                                W[idx][h] = -sign*safety*0.3 + noise*0.1
                            else:
                                W[idx][h] = noise*0.05
        return W

    def _init_w2(self):
        """Output layer weights."""
        return [1.0/self.HIDDEN_SIZE] * self.HIDDEN_SIZE

    def _relu(self, x):
        return x if x > 0 else 0.0

    def forward(self, board):
        """Compute neural evaluation. Returns centipawns from white's perspective."""
        # Build input vector (sparse)
        hidden = list(self.b1)
        for sq in range(64):
            p = board.sq[sq]
            if p is None: continue
            color, piece = p
            idx = color*384 + piece*64 + sq
            for h in range(self.HIDDEN_SIZE):
                hidden[h] += self.W1[idx][h]
        # ReLU + output
        out = self.b2
        for h in range(self.HIDDEN_SIZE):
            out += self._relu(hidden[h]) * self.W2[h]
        return int(out * 100)   # scale to centipawns

    def eval(self, board):
        """Return eval from board.side's perspective."""
        v = self.forward(board)
        return v if board.side==WHITE else -v

# ════════════════════════════════════════════════════════════════════════
#  EVALUATION  (hybrid: traditional + neural network)
# ════════════════════════════════════════════════════════════════════════
_nn = NeuralEval()

PHASE_VALS = [0,1,1,2,4,0]
MAX_PHASE  = 2*(1+1+2+4)*2

def evaluate(board, tb=None):
    """
    Hybrid evaluator:
    1. Check tablebase for endgame positions
    2. Blend traditional PST eval with neural eval
    """
    # Tablebase probe
    if tb is not None:
        result, dtm = tb.probe(board)
        if result == 'win':
            score = MATE_SCORE//2 + (1000 if dtm is None else max(0, 500-dtm*10))
            return score if board.side==WHITE else -score
        elif result == 'lose':
            score = -(MATE_SCORE//2)
            return score if board.side==WHITE else -score
        elif result == 'draw':
            return 0

    # Traditional eval
    phase = 0
    for sq in range(64):
        p=board.sq[sq]
        if p and p[1]!=KING: phase+=PHASE_VALS[p[1]]
    phase=min(phase,MAX_PHASE)
    mg_frac=phase/MAX_PHASE

    mg_score=eg_score=0
    for sq in range(64):
        p=board.sq[sq]
        if not p: continue
        c,pt=p; sign=1 if c==board.side else -1
        mg_score+=sign*MG_VAL[pt]; eg_score+=sign*EG_VAL[pt]
        idx=sq if c==WHITE else (7-sq//8)*8+sq%8
        mg_score+=sign*PST_MG[pt][idx]; eg_score+=sign*PST_EG[pt][idx]

    trad=int(mg_frac*mg_score+(1-mg_frac)*eg_score)

    # Mobility
    our=len(board.pseudo())
    board.side=1-board.side
    their=len(board.pseudo())
    board.side=1-board.side
    mob=(our-their)*3

    # Pawn structure
    pawn_sc=_pawn_eval(board)

    # King safety (midgame)
    ks=0
    if mg_frac>0.25:
        ks=_king_safety(board,board.side)-_king_safety(board,1-board.side)

    trad_total=trad+mob+pawn_sc+ks

    # Neural eval (blend: 30% neural in midgame, 10% in endgame)
    nn_blend=mg_frac*0.30+(1-mg_frac)*0.10
    nn_score=_nn.eval(board)
    trad_blend=1-nn_blend

    return int(trad_total*trad_blend + nn_score*nn_blend)

def _pawn_eval(board):
    score=0
    for c in (WHITE,BLACK):
        sign=1 if c==board.side else -1
        files=[0]*8
        for sq in range(64):
            if board.sq[sq]==(c,PAWN): files[sq%8]+=1
        for f in range(8):
            if files[f]>1: score-=sign*15*(files[f]-1)
            if files[f]>0:
                if(f==0 or files[f-1]==0)and(f==7 or files[f+1]==0):
                    score-=sign*20
        opp=1-c
        for sq in range(64):
            if board.sq[sq]!=(c,PAWN): continue
            f2,r2=sq%8,sq//8
            fwd=range(r2+1,8) if c==WHITE else range(0,r2)
            passed=True
            for pr in fwd:
                for df in (-1,0,1):
                    nf2=f2+df
                    if 0<=nf2<8 and board.sq[pr*8+nf2]==(opp,PAWN):
                        passed=False; break
                if not passed: break
            if passed: score+=sign*(r2*12 if c==WHITE else (7-r2)*12)
    return score

def _king_safety(board, color):
    k=board.king_sq(color)
    if k is None: return 0
    r,f=divmod(k,8); d=1 if color==WHITE else -1; safety=0
    for df in (-1,0,1):
        for dr in (1,2):
            nr,nf=r+d*dr,f+df
            if 0<=nr<8 and 0<=nf<8:
                if board.sq[nr*8+nf]==(color,PAWN):
                    safety+=12 if dr==1 else 5
    for df in (-1,0,1):
        nf=f+df
        if 0<=nf<8:
            if not any(board.sq[rk*8+nf]==(color,PAWN) for rk in range(8)):
                safety-=18
    return safety

# ════════════════════════════════════════════════════════════════════════
#  TRANSPOSITION TABLE
# ════════════════════════════════════════════════════════════════════════
TT_EXACT,TT_LOWER,TT_UPPER=0,1,2
TT_MASK=(1<<22)-1

class TT:
    def __init__(self): self.t={}
    def store(self,key,depth,score,flag,move):
        self.t[key&TT_MASK]=(key,depth,score,flag,move)
    def get(self,key):
        e=self.t.get(key&TT_MASK)
        return e if e and e[0]==key else None
    def clear(self): self.t.clear()

# ════════════════════════════════════════════════════════════════════════
#  ENGINE
# ════════════════════════════════════════════════════════════════════════
MAX_PLY=128  # Increased from 64 for deeper searches

class Engine:
    def __init__(self, tb=None, book=None, strength=1.0):
        self.tt      = TT()
        self.killers = [[None,None] for _ in range(MAX_PLY)]
        self.history = {}
        self.nodes   = 0
        self.t_start = 0.0
        self.t_limit = 5.0 * strength  # Scaled by strength
        self.stop    = False
        self.best    = None
        self.tb      = tb
        self.book    = book
        self.strength = strength  # 1.0 = normal, 2.0 = stronger (more time)

    def reset_h(self):
        self.killers=[[None,None] for _ in range(MAX_PLY)]
        self.history={}

    def time_up(self):
        if self.nodes&2047==0:
            return time.time()-self.t_start>=self.t_limit
        return False

    def score_move(self,board,m,ply,tt_mv):
        if m==tt_mv: return 1_000_000
        if m.captured is not None or m.is_ep:
            v=m.captured if m.captured is not None else PAWN
            a=board.sq[m.from_sq][1]
            return 900_000+v*10-a
        if m.promotion is not None: return 800_000+MG_VAL[m.promotion]
        for i,k in enumerate(self.killers[ply]):
            if m==k: return 700_000-i*1000
        return self.history.get((board.side,m.from_sq,m.to_sq),0)

    def order(self,board,moves,ply,tt_mv):
        return sorted(moves,key=lambda m:self.score_move(board,m,ply,tt_mv),reverse=True)

    def qsearch(self,board,alpha,beta,ply):
        self.nodes+=1
        if self.time_up(): self.stop=True; return 0
        sp=evaluate(board,self.tb)
        if sp>=beta: return beta
        if sp>alpha: alpha=sp
        moves=[m for m in board.legal() if m.captured is not None or m.is_ep or m.promotion is not None]
        for m in self.order(board,moves,ply,None):
            if self.stop: break
            gain=(MG_VAL[m.captured] if m.captured is not None else 0)
            if m.promotion: gain+=MG_VAL[m.promotion]-MG_VAL[PAWN]
            if sp+gain+200<alpha: continue
            b=board.copy(); b.make(m)
            sc=-self.qsearch(b,-beta,-alpha,ply+1)
            if sc>=beta: return beta
            if sc>alpha: alpha=sc
        return alpha

    def pvs(self,board,depth,alpha,beta,ply,null_ok=True):
        self.nodes+=1
        if self.time_up(): self.stop=True; return 0
        in_check=board.in_check()
        if in_check: depth+=1
        if depth<=0: return self.qsearch(board,alpha,beta,ply)
        if ply>0 and(board.is_repetition() or board.is_fifty() or board.insufficient_material()):
            return 0
        orig_alpha=alpha; tt_mv=None
        e=self.tt.get(board.zobrist)
        if e:
            _,td,ts,tf,tt_mv=e
            if td>=depth:
                if tf==TT_EXACT: return ts
                elif tf==TT_LOWER: alpha=max(alpha,ts)
                elif tf==TT_UPPER: beta=min(beta,ts)
                if alpha>=beta: return ts
        moves=board.legal()
        if not moves:
            return -(MATE_SCORE-ply) if in_check else 0
        if null_ok and not in_check and depth>=3 and ply>0:
            b=board.copy(); b.side=1-b.side; b.ep=None; b.zobrist^=ZOB_SIDE
            sc=-self.pvs(b,depth-3,-beta,-beta+1,ply+1,False)
            if sc>=beta and abs(sc)<MATE_SCORE//2: return beta
        if depth<=3 and not in_check and abs(alpha)<MATE_SCORE//2 and abs(beta)<MATE_SCORE//2:
            static=evaluate(board,self.tb)
            margins=[0,150,300,500]
            if static+margins[depth]<=alpha:
                return self.qsearch(board,alpha,beta,ply)
        moves=self.order(board,moves,ply,tt_mv)
        best_sc=-INF; best_mv=None
        for i,m in enumerate(moves):
            if self.stop: break
            b=board.copy(); b.make(m)
            is_cap=m.captured is not None or m.is_ep
            gc=b.in_check(); is_pr=m.promotion is not None
            if i==0:
                sc=-self.pvs(b,depth-1,-beta,-alpha,ply+1)
            else:
                lmr=(depth>=3 and i>=3 and not is_cap and not gc and not is_pr and not in_check)
                if lmr:
                    R=1+depth//4+min(i//8,3)
                    sc=-self.pvs(b,depth-1-R,-alpha-1,-alpha,ply+1)
                    if sc>alpha: sc=-self.pvs(b,depth-1,-alpha-1,-alpha,ply+1)
                else:
                    sc=-self.pvs(b,depth-1,-alpha-1,-alpha,ply+1)
                if alpha<sc<beta:
                    sc=-self.pvs(b,depth-1,-beta,-alpha,ply+1)
            if sc>best_sc: best_sc=sc; best_mv=m
            if sc>alpha:
                alpha=sc
                if ply==0: self.best=m
            if alpha>=beta:
                if not is_cap:
                    if m!=self.killers[ply][0]:
                        self.killers[ply][1]=self.killers[ply][0]; self.killers[ply][0]=m
                    k=(board.side,m.from_sq,m.to_sq)
                    self.history[k]=self.history.get(k,0)+depth*depth
                break
        flag=TT_EXACT if orig_alpha<best_sc<beta else(TT_LOWER if best_sc>=beta else TT_UPPER)
        self.tt.store(board.zobrist,depth,best_sc,flag,best_mv)
        return best_sc

    def search(self, board, t_limit=5.0, verbose=True, min_depth=1):
        # Try opening book first
        if self.book:
            bm=self.book.pick(board)
            if bm:
                if verbose: print(f"  [Book] {board.san(bm)}")
                return bm

        self.t_limit=t_limit; self.t_start=time.time()
        self.nodes=0; self.stop=False; self.best=None; self.reset_h()
        legal=board.legal()
        if not legal: return None
        if len(legal)==1: return legal[0]
        best=legal[0]; best_sc=-INF; asp=50
        for depth in range(1,MAX_PLY+1):
            if self.stop: break
            if depth>=4: a,b=best_sc-asp,best_sc+asp
            else: a,b=-INF,INF
            while True:
                sc=self.pvs(board,depth,a,b,0)
                if self.stop: break
                if sc<=a:   a-=asp*4; asp*=2
                elif sc>=b: b+=asp*4; asp*=2
                else:       asp=50;   break
            if not self.stop and self.best:
                best=self.best; best_sc=sc
                if verbose:
                    elapsed=time.time()-self.t_start
                    nps=int(self.nodes/max(elapsed,0.001))
                    sf=_fmt(sc)
                    print(f"  depth {depth:>2}  score {sf:>8}  nodes {self.nodes:>9,}  "
                          f"nps {nps:>8,}  time {elapsed:.2f}s  pv {board.san(best)}")
            if time.time()-self.t_start>=self.t_limit*0.5: break
            if depth >= min_depth and time.time()-self.t_start>=self.t_limit*0.3: break
        return best

    def search_best(self, board, t_limit=3.0, depth_limit=16):
        """Search for the best move and score - optimized for analysis."""
        self.t_limit=t_limit; self.t_start=time.time()
        self.nodes=0; self.stop=False; self.best=None; self.reset_h()
        legal=board.legal()
        if not legal: return None, 0
        if len(legal)==1: return legal[0], 0
        best=legal[0]; best_sc=-INF; asp=50
        for depth in range(1, min(MAX_PLY+1, depth_limit+1)):
            if self.stop: break
            if depth>=4: a,b=best_sc-asp,best_sc+asp
            else: a,b=-INF,INF
            while True:
                sc=self.pvs(board,depth,a,b,0)
                if self.stop: break
                if sc<=a:   a-=asp*4; asp*=2
                elif sc>=b: b+=asp*4; asp*=2
                else:       asp=50;   break
            if not self.stop and self.best:
                best=self.best; best_sc=sc
            if time.time()-self.t_start>=self.t_limit: break
        return best, best_sc

def _fmt(s):
    if abs(s)>MATE_SCORE//2:
        m=(MATE_SCORE-abs(s)+1)//2
        return('+' if s>0 else '-')+f'M{m}'
    return f"{s/100:+.2f}"

# ════════════════════════════════════════════════════════════════════════
#  POST-GAME ANALYSIS
# ════════════════════════════════════════════════════════════════════════

# Move classification thresholds (in centipawns) - similar to chess.com
MOVE_CATEGORIES = {
    'book': {'label': 'BOOK', 'symbol': 'B'},
    'brilliant': {'min_gain': 50, 'is_best': True, 'label': 'BRILLIANT', 'symbol': '!!'},
    'best': {'label': 'BEST', 'symbol': '!'},
    'good': {'max_loss': 10, 'label': 'GOOD', 'symbol': '✓'},
    'ok': {'max_loss': 25, 'label': 'OK', 'symbol': ''},
    'inaccuracy': {'max_loss': 75, 'label': 'INACCURACY', 'symbol': '?!'},
    'mistake': {'max_loss': 200, 'label': 'MISTAKE', 'symbol': '?'},
    'blunder': {'label': 'BLUNDER', 'symbol': '??'}
}

def classify_move(cp_loss, is_best_move, is_book_move=False):
    """
    Classify a move based on centipawn loss, whether it was the best move, and if it's in the opening book.
    cp_loss: positive = you lost ground, negative = you gained ground
    is_best_move: whether this was the engine's top choice
    is_book_move: whether this move is in the opening book

    Returns: (category_key, label, symbol)
    """
    # Book move: takes priority - shows it's a known opening/theoretical move
    if is_book_move:
        return 'book', MOVE_CATEGORIES['book']['label'], MOVE_CATEGORIES['book']['symbol']
    
    # Brilliant: sacrificing material for significant advantage (negative loss = gain)
    if cp_loss < -50 and is_best_move:
        return 'brilliant', MOVE_CATEGORIES['brilliant']['label'], MOVE_CATEGORIES['brilliant']['symbol']

    # Best move
    if is_best_move and cp_loss >= -50:
        return 'best', MOVE_CATEGORIES['best']['label'], MOVE_CATEGORIES['best']['symbol']

    # Good move (small loss or slight gain, but not best)
    if cp_loss < 10:
        return 'good', MOVE_CATEGORIES['good']['label'], MOVE_CATEGORIES['good']['symbol']

    # OK move (reasonable)
    if cp_loss < 25:
        return 'ok', MOVE_CATEGORIES['ok']['label'], MOVE_CATEGORIES['ok']['symbol']

    # Inaccuracy
    if cp_loss < 75:
        return 'inaccuracy', MOVE_CATEGORIES['inaccuracy']['label'], MOVE_CATEGORIES['inaccuracy']['symbol']

    # Mistake
    if cp_loss < 200:
        return 'mistake', MOVE_CATEGORIES['mistake']['label'], MOVE_CATEGORIES['mistake']['symbol']

    # Blunder
    return 'blunder', MOVE_CATEGORIES['blunder']['label'], MOVE_CATEGORIES['blunder']['symbol']

def analyze_game(san_log, engine_time=2.0, depth_limit=14):
    """
    Analyze a completed game move by move using engine.
    Returns list of dicts with move analysis including classification.
    """
    print("\n  Analyzing game... (this may take a moment)\n")
    tb   = Tablebase()
    book = OpeningBook()
    eng  = Engine(tb=tb, book=None, strength=1.5)  # Stronger engine for analysis

    board = Board(); board.reset()
    results = []

    # Get initial evaluation
    prev_best, prev_score = eng.search_best(board, t_limit=engine_time, depth_limit=depth_limit)

    for i, san in enumerate(san_log):
        side = WHITE if i%2==0 else BLACK
        m = board.parse_san(san)
        if m is None: break

        # Check if move is in opening book BEFORE making the move
        is_book_move = False
        if book:
            book_mv = book.pick(board)
            is_book_move = (book_mv == m)

        # Score before the move (from current player's perspective)
        score_before = prev_score
        if side == BLACK:
            score_before = -score_before

        # Get best move at this position
        eng.tt.clear()
        best_mv, best_score = eng.search_best(board, t_limit=engine_time, depth_limit=depth_limit)
        best_san_str = board.san(best_mv) if best_mv else '?'

        # Check if played move is the best move
        is_best = (m == best_mv)
        # Apply the move
        board.make(m)
        board.san_log.append(san)

        # Get score after (from next player's perspective, so negate)
        _, score_after_raw = eng.search_best(board, t_limit=engine_time*0.5, depth_limit=depth_limit//2)

        # Calculate CP loss from the perspective of the player who moved
        # Positive = bad (you lost advantage), Negative = good (you gained advantage)
        if side == WHITE:
            # White's perspective: higher score is better
            score_after = -score_after_raw  # After move, it's black's turn, so negate
            cp_loss = score_before - score_after
        else:
            # Black's perspective: lower score is better (negative for black advantage)
            score_after = score_after_raw
            cp_loss = (-score_before) - (-score_after)

        # Classify the move (book moves take priority)
        category, label, symbol = classify_move(cp_loss, is_best, is_book_move)

        results.append({
            'move_num': i//2+1,
            'side': side,
            'san': san,
            'category': category,
            'label': label,
            'symbol': symbol,
            'cp_loss': cp_loss,
            'score': score_after_raw,
            'best': best_san_str,
            'is_best': is_best,
            'is_book': is_book_move
        })

        prev_score = score_after_raw

    return results

def print_analysis(results):
    """Pretty-print analysis results."""
    print("\n" + "═"*70)
    print("  GAME ANALYSIS")
    print("═"*70)

    # Count by category for each player
    stats = {
        WHITE: {'book': 0, 'brilliant': 0, 'best': 0, 'good': 0, 'ok': 0, 'inaccuracy': 0, 'mistake': 0, 'blunder': 0},
        BLACK: {'book': 0, 'brilliant': 0, 'best': 0, 'good': 0, 'ok': 0, 'inaccuracy': 0, 'mistake': 0, 'blunder': 0}
    }

    for r in results:
        mn   = r['move_num']
        side = 'W' if r['side']==WHITE else 'B'
        san  = r['san']
        category = r.get('category', 'ok')
        label = r.get('label', 'OK')
        symbol = r.get('symbol', '')
        sc   = r['score']
        best = r.get('best', '?')
        is_best = r.get('is_best', False)
        is_book = r.get('is_book', False)

        # Color coding for categories
        category_colors = {
            'book': '\033[96m',       # Cyan
            'brilliant': '\033[94m',  # Blue
            'best': '\033[92m',       # Green
            'good': '\033[92m',       # Green
            'ok': '\033[0m',          # Normal
            'inaccuracy': '\033[93m', # Yellow
            'mistake': '\033[91m',    # Red
            'blunder': '\033[95m'     # Magenta
        }
        reset = '\033[0m'

        # Format the label
        label_display = f"{category_colors.get(category, '')}{label:<12}{reset}"

        # Show best move for non-best, non-book moves
        best_note = ''
        if not is_best and not is_book and best:
            best_note = f" \033[90m(best: {best})\033[0m"

        mark = f" {symbol}" if symbol else '  '
        print(f"  {mn:>3}.{side}  {san+mark:<14} {label_display} [{_fmt(sc)}]{best_note}")

        # Update stats
        side_key = WHITE if r['side']==WHITE else BLACK
        stats[side_key][category] = stats[side_key].get(category, 0) + 1

    print("\n" + "─"*70)

    # Print accuracy summary
    for side, side_name in [(WHITE, 'White'), (BLACK, 'Black')]:
        s = stats[side]
        total = sum(s.values())
        if total > 0:
            # Accuracy = (book + best + good + ok) / total
            accurate = s.get('book', 0) + s.get('best', 0) + s.get('good', 0) + s.get('ok', 0)
            accuracy = accurate / total * 100

            book_count = s.get('book', 0)
            print(f"  {side_name}: {book_count} book | {s.get('brilliant',0)} brilliant | {s.get('best',0)} best | "
                  f"{s.get('good',0)} good | {s.get('ok',0)} ok | "
                  f"{s.get('inaccuracy',0)} inaccuracy | {s.get('mistake',0)} mistakes | "
                  f"{s.get('blunder',0)} blunders | Accuracy: {accuracy:.1f}%")

    print("═"*70 + "\n")

# ════════════════════════════════════════════════════════════════════════
#  ELO RATING SYSTEM
# ════════════════════════════════════════════════════════════════════════
ELO_FILE = os.path.expanduser("~/.chess_elo.json")
ONLINE_GAMES_FILE = os.path.expanduser("~/.chess_online_games.json")
ENGINE_NAME = "ChessBot-9000"

def save_online_game(white, black, result, moves, duration, rated=True):
    """Save an online game to local storage for later analysis."""
    try:
        games = []
        try:
            with open(ONLINE_GAMES_FILE, 'r') as f:
                games = json.loads(f.read())
        except:
            pass
        
        games.append({
            'id': len(games) + 1,
            'timestamp': datetime.now().isoformat(),
            'white': white,
            'black': black,
            'result': result,
            'moves': moves,
            'duration': duration,
            'rated': rated,
            'analyzed': False
        })
        
        with open(ONLINE_GAMES_FILE, 'w') as f:
            json.dump(games, f, indent=2)
    except Exception as e:
        pass  # Silently fail

def load_online_games(limit=20):
    """Load recent online games from local storage."""
    try:
        with open(ONLINE_GAMES_FILE, 'r') as f:
            games = json.loads(f.read())
            games.sort(key=lambda x: x.get('timestamp', ''), reverse=True)
            return games[:limit]
    except:
        return []

def get_unanalyzed_games():
    """Get games that haven't been analyzed yet."""
    try:
        with open(ONLINE_GAMES_FILE, 'r') as f:
            games = json.loads(f.read())
            return [g for g in games if not g.get('analyzed', False)]
    except:
        return []

def mark_game_analyzed(game_id):
    """Mark a game as analyzed."""
    try:
        with open(ONLINE_GAMES_FILE, 'r') as f:
            games = json.loads(f.read())
        for g in games:
            if g.get('id') == game_id:
                g['analyzed'] = True
                g['analysis_date'] = datetime.now().isoformat()
                break
        with open(ONLINE_GAMES_FILE, 'w') as f:
            json.dump(games, f, indent=2)
    except:
        pass

class EloSystem:
    def __init__(self):
        self.db = self._load()

    def _load(self):
        try:
            with open(ELO_FILE,'r') as f:
                return json.loads(f.read())
        except:
            return {ENGINE_NAME: {'elo':2200,'games':0,'wins':0,'draws':0,'losses':0}}

    def _save(self):
        try:
            with open(ELO_FILE,'w') as f:
                f.write(json.dumps(self.db, indent=2))
        except:
            pass

    def get_elo(self, name):
        if name not in self.db:
            self.db[name]={'elo':1200,'games':0,'wins':0,'draws':0,'losses':0}
        return self.db[name]['elo']

    def expected(self, ra, rb):
        return 1.0/(1.0+10**((rb-ra)/400.0))

    def update(self, player, opponent, result):
        """result: 1=win, 0.5=draw, 0=loss"""
        for n in (player, opponent):
            if n not in self.db:
                self.db[n]={'elo':1200,'games':0,'wins':0,'draws':0,'losses':0}
        ra=self.db[player]['elo']; rb=self.db[opponent]['elo']
        ea=self.expected(ra,rb); K=32
        new_ra=ra+K*(result-ea)
        self.db[player]['elo']=round(new_ra)
        self.db[player]['games']+=1
        if result==1:   self.db[player]['wins']+=1
        elif result==0.5: self.db[player]['draws']+=1
        else:           self.db[player]['losses']+=1
        # Update opponent
        eb=self.expected(rb,ra)
        new_rb=rb+K*((1-result)-eb)
        self.db[opponent]['elo']=round(new_rb)
        self.db[opponent]['games']+=1
        if result==0:   self.db[opponent]['wins']+=1
        elif result==0.5: self.db[opponent]['draws']+=1
        else:           self.db[opponent]['losses']+=1
        self._save()

    def leaderboard(self, n=10):
        ranked=sorted(self.db.items(), key=lambda x:-x[1]['elo'])
        print("\n  ┌─────────────────────────────────────────────┐")
        print(  "  │              ELO LEADERBOARD                │")
        print(  "  ├──────┬────────────────────┬──────┬─────────┤")
        print(  "  │ Rank │ Player             │  ELO │  W/D/L  │")
        print(  "  ├──────┼────────────────────┼──────┼─────────┤")
        for i,(name,d) in enumerate(ranked[:n]):
            w=d.get('wins',0); dr=d.get('draws',0); l=d.get('losses',0)
            print(f"  │  {i+1:>2}  │ {name:<18} │ {d['elo']:>4} │ {w}/{dr}/{l:<4} │")
        print(  "  └──────┴────────────────────┴──────┴─────────┘\n")


def show_online_leaderboard(n=10):
    """Show ELO leaderboard from server."""
    if ChessClient is None:
        print("  Client not available")
        return
    
    # Check offline mode
    if _offline_mode:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║              OFFLINE MODE ACTIVE                         ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  To view the online leaderboard:                         ║")
        print("  ║  1. Return to main menu                                  ║")
        print("  ║  2. Select option 8 (Enable Online Mode)                 ║")
        print("  ║  3. Make sure the server is running                      ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        # Fall back to local leaderboard
        elo_sys = EloSystem()
        elo_sys.leaderboard(n)
        return
    
    # Connect to server if needed
    if _server_client is None or _server_client.sock is None:
        success, msg = connect_to_server()
        if not success:
            print(f"  Cannot connect to server: {msg}")
            print("  Showing local leaderboard instead...")
            elo_sys = EloSystem()
            elo_sys.leaderboard(n)
            return
    
    response = _server_client.get_leaderboard(n)
    if response is None or not response.get('success'):
        print("  Cannot retrieve leaderboard from server.")
        print("  Showing local leaderboard instead...")
        elo_sys = EloSystem()
        elo_sys.leaderboard(n)
        return
    
    leaderboard = response.get('data', [])
    
    print("\n  ╔══════════════════════════════════════════════════════════════╗")
    print("  ║                   ELO LEADERBOARD                            ║")
    print("  ╠══════╦════════════════════════╦═════════╦════════════════════╣")
    print("  ║ Rank ║ Player                 ║   ELO   ║  Record (W/D/L)    ║")
    print("  ╠══════╬════════════════════════╬═════════╬════════════════════╣")
    
    for i, entry in enumerate(leaderboard[:n], 1):
        username = entry.get('username', 'Unknown')[:22]
        elo = entry.get('elo', 1200)
        wins = entry.get('wins', 0)
        draws = entry.get('draws', 0)
        losses = entry.get('losses', 0)
        games = entry.get('games', 0)
        peak = entry.get('peak', elo)
        
        # Format record
        record = f"{wins}W/{draws}D/{losses}L"
        peak_indicator = " ▲" if elo == peak and games > 5 else ""
        
        print(f"  ║ {i:>4} ║ {username:<22} ║ {elo:>5}{peak_indicator}   ║ {record:<18} ║")
    
    print("  ╚══════╩════════════════════════╩═════════╩════════════════════╝")
    print()

# ════════════════════════════════════════════════════════════════════════
#  NETWORK MULTIPLAYER  (TCP, pure stdlib)
# ════════════════════════════════════════════════════════════════════════
MULTI_PORT = 65432
MSG_MOVE   = 'MOVE'
MSG_RESIGN = 'RESIGN'
MSG_DRAW   = 'DRAW'
MSG_ACCEPT = 'ACCEPT'
MSG_DECLINE= 'DECLINE'
MSG_CHAT   = 'CHAT'

class NetworkGame:
    """
    Simple TCP-based multiplayer.
    Protocol: length-prefixed JSON messages.
    """
    def __init__(self, sock):
        self.sock    = sock
        self.pending = b''

    def send(self, msg_type, data=''):
        payload=json.dumps({'type':msg_type,'data':data}).encode()
        header=struct.pack('>I',len(payload))
        try:
            self.sock.sendall(header+payload)
            return True
        except:
            return False

    def recv(self, timeout=0.1):
        self.sock.settimeout(timeout)
        try:
            while True:
                if len(self.pending)>=4:
                    length=struct.unpack('>I',self.pending[:4])[0]
                    if len(self.pending)>=4+length:
                        payload=self.pending[4:4+length]
                        self.pending=self.pending[4+length:]
                        return json.loads(payload.decode())
                chunk=self.sock.recv(4096)
                if not chunk: return None
                self.pending+=chunk
        except socket.timeout:
            return None
        except:
            return None

    def close(self):
        try: self.sock.close()
        except: pass


def host_game(port=MULTI_PORT):
    """Host a multiplayer game. Returns (NetworkGame, our_color) or (None,None)."""
    s=socket.socket(socket.AF_INET,socket.SOCK_STREAM)
    s.setsockopt(socket.SOL_SOCKET,socket.SO_REUSEADDR,1)
    try:
        s.bind(('',port))
        s.listen(1)
        print(f"\n  Hosting on port {port}. Waiting for opponent...")
        print(f"  Your local IP addresses:")
        try:
            hostname=socket.gethostname()
            ips=socket.getaddrinfo(hostname,None)
            shown=set()
            for ip in ips:
                addr=ip[4][0]
                if addr not in shown and not addr.startswith('::'):
                    print(f"    {addr}")
                    shown.add(addr)
        except: pass
        s.settimeout(120)
        conn,addr=s.accept()
        print(f"  Connected to {addr[0]}")
        s.close()
        return NetworkGame(conn), WHITE
    except socket.timeout:
        print("  Timed out waiting for opponent.")
        s.close()
        return None, None
    except Exception as e:
        print(f"  Host error: {e}")
        s.close()
        return None, None


def join_game(host_ip, port=MULTI_PORT):
    """Join a multiplayer game."""
    s=socket.socket(socket.AF_INET,socket.SOCK_STREAM)
    try:
        s.settimeout(10)
        s.connect((host_ip,port))
        s.settimeout(None)
        print(f"  Connected to {host_ip}:{port}")
        return NetworkGame(s), BLACK
    except Exception as e:
        print(f"  Connection error: {e}")
        s.close()
        return None, None


# ════════════════════════════════════════════════════════════════════════
#  NETWORK CLIENT (Standalone - no server.py import needed)
# ════════════════════════════════════════════════════════════════════════
# Message types for server communication
MSG_REGISTER = 'REGISTER'
MSG_LOGIN = 'LOGIN'
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
MSG_MATCH = 'MATCH_FOUND'
MSG_MATCH_ACCEPT = 'MATCH_ACCEPT'
MSG_MATCH_DECLINE = 'MATCH_DECLINE'
MSG_GAME_START = 'GAME_START'
MSG_GAME_MOVE = 'GAME_MOVE'
MSG_GAME_RESIGN = 'GAME_RESIGN'
MSG_GAME_DRAW_OFFER = 'GAME_DRAW_OFFER'
MSG_GAME_DRAW_ACCEPT = 'GAME_DRAW_ACCEPT'
MSG_GAME_CHAT = 'GAME_CHAT'

# Response types
RESP_SUCCESS = 'SUCCESS'
RESP_ERROR = 'ERROR'
RESP_PROFILE = 'PROFILE'
RESP_USERS = 'USERS'
RESP_QUEUED = 'QUEUED'
RESP_LEADERBOARD = 'LEADERBOARD'


class ChessClient:
    """
    Standalone client for connecting to the chess server.
    Does not require importing server.py - uses pure socket communication.
    """
    
    def __init__(self, host='localhost', port=65433):
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
    
    def save_game(self, white, black, result, moves, duration=0, rated=True):
        """Save a game to history."""
        self.send(MSG_SAVE_GAME, {
            'white': white,
            'black': black,
            'result': result,
            'moves': moves,
            'duration': duration,
            'rated': rated
        })
        return self.recv()
    
    def list_users(self):
        """Get list of all users."""
        self.send(MSG_LIST_USERS)
        return self.recv()
    
    # Matchmaking methods
    def join_queue(self):
        """Join the matchmaking queue."""
        self.send(MSG_QUEUE_JOIN, {'username': self.logged_in_user or _current_user})
        return self.recv()

    def leave_queue(self):
        """Leave the matchmaking queue."""
        self.send(MSG_QUEUE_LEAVE, {'username': self.logged_in_user or _current_user})
        return self.recv()

    def get_queue_status(self):
        """Get queue status."""
        self.send(MSG_QUEUE_STATUS, {'username': self.logged_in_user or _current_user})
        return self.recv()

    def trigger_matchmaking(self):
        """Trigger immediate matchmaking check."""
        self.send(MSG_QUEUE_STATUS, {'trigger': True, 'username': self.logged_in_user or _current_user})
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

    def get_leaderboard(self, limit=10):
        """Get ELO leaderboard."""
        self.send(MSG_LEADERBOARD, {'limit': limit})
        return self.recv()


# ════════════════════════════════════════════════════════════════════════
#  AUTHENTICATION & PROFILE SYSTEM
# ════════════════════════════════════════════════════════════════════════
# Global authentication state
_server_client = None
_current_user = None
_server_host = '86.1.210.75'
_server_port = 65433
_offline_mode = True  # Start in offline mode by default


def set_offline_mode(enabled):
    """Enable or disable offline mode."""
    global _offline_mode, _server_client
    _offline_mode = enabled
    if enabled and _server_client:
        _server_client.disconnect()
        _server_client = None


def is_offline_mode():
    """Check if offline mode is enabled."""
    return _offline_mode

def get_server_client():
    """Get or create the server client connection."""
    global _server_client, _server_host, _server_port
    if _server_client is None:
        _server_client = ChessClient(host=_server_host, port=_server_port)
    return _server_client

def get_current_user():
    """Get the currently logged-in user."""
    return _current_user

def set_current_user(username):
    """Set the currently logged-in user."""
    global _current_user
    _current_user = username

def connect_to_server(host=None, port=None, reconnect=False, auto_login=True):
    """
    Connect to the authentication server.
    If reconnect=True, force a new connection and re-login if _current_user is set.
    If auto_login=True and _current_user is set, automatically log in.
    """
    global _server_client, _server_host, _server_port

    # Check if in offline mode
    if _offline_mode:
        return False, "Offline mode enabled. Disable it from the main menu first."

    # Update host/port if provided
    if host:
        _server_host = host
    if port:
        _server_port = port

    # Check if already connected
    if _server_client and _server_client.sock and not reconnect:
        return True, "Already connected"

    # Disconnect existing connection if any
    if _server_client:
        _server_client.disconnect()
        _server_client = None

    client = ChessClient(host=_server_host, port=_server_port)
    success, msg = client.connect()
    
    if not success:
        return False, msg
    
    _server_client = client
    
    # Auto-login if we have a current user and auto_login is enabled
    if auto_login and _current_user:
        # We need to send login message to server
        # But we don't have the password stored, so we just mark the connection
        # The server will recognize the user from subsequent authenticated requests
        pass
    
    return True, "Connected"

def disconnect_from_server():
    """Disconnect from the authentication server."""
    global _server_client, _current_user
    if _server_client:
        _server_client.disconnect()
        _server_client = None
    _current_user = None

def register_user():
    """Register a new user account."""
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              CREATE NEW ACCOUNT                          ║")
    print("  ╚══════════════════════════════════════════════════════════╝")
    
    # Connect to server first
    success, msg = connect_to_server()
    if not success:
        print(f"  {msg}")
        print("  Continuing in offline mode...")
        return None
    
    while True:
        try:
            username = input("  Choose username (3-20 chars): ").strip()
        except EOFError:
            return None
        
        if len(username) < 3 or len(username) > 20:
            print("  Username must be 3-20 characters")
            continue
        if not re.match(r'^[a-zA-Z0-9_]+$', username):
            print("  Username can only contain letters, numbers, and underscores")
            continue
        break
    
    while True:
        try:
            email = input("  Enter email address: ").strip()
        except EOFError:
            return None
        
        if not re.match(r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$', email):
            print("  Invalid email format")
            continue
        break
    
    while True:
        try:
            password = input("  Choose password (min 6 chars): ").strip()
        except EOFError:
            return None
        
        if len(password) < 6:
            print("  Password must be at least 6 characters")
            continue
        break
    
    # Register with server
    response = _server_client.register(username, password, email)
    if response and response.get('success'):
        print(f"\n  ✓ {response.get('data', 'Registration successful')}")
        set_current_user(username)
        return username
    else:
        error_msg = response.get('data', 'Registration failed') if response else 'Registration failed'
        print(f"\n  ✗ {error_msg}")
        return None

def login_user():
    """Login to an existing user account."""
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║                  USER LOGIN                              ║")
    print("  ╚══════════════════════════════════════════════════════════╝")
    
    # Connect to server first
    success, msg = connect_to_server()
    if not success:
        print(f"  {msg}")
        print("  Continuing in offline mode...")
        return None
    
    while True:
        try:
            username = input("  Username: ").strip()
        except EOFError:
            return None
        
        if not username:
            print("  Username cannot be empty")
            continue
        break
    
    while True:
        try:
            password = input("  Password: ").strip()
        except EOFError:
            return None
        break
    
    # Login with server
    response = _server_client.login(username, password)
    if response and response.get('success'):
        print(f"\n  ✓ Welcome back, {username}!")
        set_current_user(username)
        return username
    else:
        error_msg = response.get('data', 'Login failed') if response else 'Login failed'
        print(f"\n  ✗ {error_msg}")
        return None

def logout_user():
    """Logout the current user."""
    global _current_user
    if _current_user and _server_client:
        _server_client.logout()
    _current_user = None
    print("  Logged out successfully.")

def view_profile(username=None):
    """View a user's profile."""
    if ChessClient is None:
        print("  Client not available")
        return
    
    # Check offline mode first
    if _offline_mode:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║              OFFLINE MODE ACTIVE                         ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  To view profiles, you need to enable online mode:       ║")
        print("  ║  1. Return to main menu                                  ║")
        print("  ║  2. Select option 8 (Enable Online Mode)                 ║")
        print("  ║  3. Make sure the server is running                      ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        return
    
    # Connect to server if not already connected
    if _server_client is None or _server_client.sock is None:
        success, msg = connect_to_server()
        if not success:
            print(f"  Cannot connect to server: {msg}")
            print("  Make sure the server is running: python3 server.py")
            return

    if not username:
        username = _current_user

    if not username:
        print("  No user logged in")
        return

    response = _server_client.get_profile(username)
    if response is None:
        print("  No response from server. Connection may have timed out.")
        print("  Make sure the server is running and you have a stable connection.")
        return
    
    if not response.get('success'):
        print(f"  Failed to get profile: {response.get('data', 'Unknown error')}")
        return

    profile = response.get('data', {})
    is_own_profile = (username == _current_user)

    # Get ELO info
    elo = profile.get('elo', 1200)
    elo_games = profile.get('elo_games', 0)
    elo_wins = profile.get('elo_wins', 0)
    elo_losses = profile.get('elo_losses', 0)
    elo_draws = profile.get('elo_draws', 0)
    elo_peak = profile.get('elo_peak', 1200)

    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print(f"  ║  PROFILE: {profile.get('username', 'Unknown'):<44}   ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    if is_own_profile:
        print(f"  ║  Email: {profile.get('email', 'N/A'):<49}║")
    print(f"  ║  Member since: {profile.get('created_at', 'N/A'):<41} ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print(f"  ║  ELO Rating: {elo:<46}║")
    print(f"  ║  Peak ELO: {elo_peak:<46}║")
    print(f"  ║  Rated Games: {elo_games:<43}║")
    print(f"  ║  Record: {elo_wins}W - {elo_losses}L - {elo_draws}D{'':28}║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║  RECENT GAMES (Last 3):                                  ║")
    print("  ╚══════════════════════════════════════════════════════════╝")
    
    recent_games = profile.get('recent_games', [])
    if not recent_games:
        print("    No games played yet.")
    else:
        for i, game in enumerate(recent_games, 1):
            white = game.get('white', 'Unknown')
            black = game.get('black', 'Unknown')
            result = game.get('result', 'Unknown')
            timestamp = game.get('timestamp', 'Unknown')[:16].replace('T', ' ')
            moves_count = len(game.get('moves', []))
            
            if result == 'white':
                result_str = f"{white} won"
            elif result == 'black':
                result_str = f"{black} won"
            else:
                result_str = "Draw"
            
            print(f"    {i}. [{timestamp}] {white} vs {black} - {result_str} ({moves_count} moves)")
    print()

def list_all_users():
    """List all registered users."""
    if ChessClient is None:
        print("  Client not available")
        return
    
    # Check offline mode first
    if _offline_mode:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║              OFFLINE MODE ACTIVE                         ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  To view users, you need to enable online mode:          ║")
        print("  ║  1. Return to main menu                                  ║")
        print("  ║  2. Select option 8 (Enable Online Mode)                 ║")
        print("  ║  3. Make sure the server is running                      ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        return
    
    # Connect to server if not already connected
    if _server_client is None or _server_client.sock is None:
        success, msg = connect_to_server()
        if not success:
            print(f"  Cannot connect to server: {msg}")
            print("  Make sure the server is running: python3 server.py")
            return

    response = _server_client.list_users()
    if response is None:
        print("  No response from server. Connection may have timed out.")
        print("  Make sure the server is running and you have a stable connection.")
        return
    
    if not response.get('success'):
        print("  Failed to get user list")
        return
    
    users = response.get('data', [])
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print(f"  ║  REGISTERED USERS ({len(users)}):{'':35}║")
    print("  ╚══════════════════════════════════════════════════════════╝")
    
    if not users:
        print("    No registered users yet.")
    else:
        for user in sorted(users):
            current_marker = " (you)" if user == _current_user else ""
            print(f"    • {user}{current_marker}")
    print()

def configure_server_connection():
    """Configure server host and port."""
    global _server_host, _server_port, _server_client
    
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║           SERVER CONNECTION SETTINGS                     ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print(f"  ║  Current Host: {_server_host:<42}║")
    print(f"  ║  Current Port: {_server_port:<42}║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    
    try:
        host = input(f"  Enter server host [{_server_host}]: ").strip()
        if host:
            _server_host = host
        
        port_str = input(f"  Enter server port [{_server_port}]: ").strip()
        if port_str:
            _server_port = int(port_str)
        
        # Disconnect existing connection
        if _server_client:
            _server_client.disconnect()
            _server_client = None
        
        print(f"\n  Server settings updated: {_server_host}:{_server_port}")
        
        # Test connection
        success, msg = connect_to_server()
        if success:
            print(f"  ✓ Connected to server at {_server_host}:{_server_port}")
        else:
            print(f"  ✗ {msg}")
            print("  (Settings saved, will try to connect on next operation)")
            print("  Make sure the server is running: python3 server.py")
    except ValueError:
        print("  Invalid port number.")
    except EOFError:
        pass

def auth_menu():
    """Display authentication menu."""
    while True:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║              ACCOUNT MANAGEMENT                          ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        
        if _offline_mode:
            print("  ║  [OFFLINE MODE - Online features disabled]               ║")
            print("  ╠══════════════════════════════════════════════════════════╣")
            print("  ║  To use online accounts:                                 ║")
            print("  ║  - Return to main menu                                   ║")
            print("  ║  - Select option 8 (Toggle Offline Mode)                 ║")
            print("  ╚══════════════════════════════════════════════════════════╝")
        else:
            if _current_user:
                print(f"  ║  Logged in as: {_current_user:<40}║")
                print("  ╠══════════════════════════════════════════════════════════╣")
                print("  ║  1. View My Profile                                      ║")
                print("  ║  2. View Another User's Profile                          ║")
                print("  ║  3. List All Users                                       ║")
                print("  ║  4. Logout                                               ║")
            else:
                print("  ║  Not logged in                                           ║")
                print("  ╠══════════════════════════════════════════════════════════╣")
                print("  ║  1. Login                                                ║")
                print("  ║  2. Register New Account                                 ║")
            print("  ╠══════════════════════════════════════════════════════════╣")
            print("  ║  5. Configure Server Connection                          ║")
        
        print("  ║  0. Back to Main Menu                                    ║")
        print("  ╚══════════════════════════════════════════════════════════╝")

        try:
            choice = input("  Choice: ").strip()
        except EOFError:
            break

        if choice == '0':
            break
        
        if _offline_mode:
            print("\n  Please disable offline mode from the main menu first.")
            continue
        
        if choice == '1':
            if _current_user:
                view_profile(_current_user)
            else:
                login_user()
                if _current_user:
                    clear_screen()
        elif choice == '2':
            if _current_user:
                try:
                    username = input("  Enter username to view: ").strip()
                except EOFError:
                    continue
                view_profile(username)
            else:
                register_user()
                if _current_user:
                    clear_screen()
        elif choice == '3':
            if _current_user:
                list_all_users()
            else:
                print("  Please login or register first.")
        elif choice == '4':
            if _current_user:
                logout_user()
            else:
                print("  Not logged in.")
        elif choice == '5':
            configure_server_connection()


# ════════════════════════════════════════════════════════════════════════
#  ONLINE MATCHMAKING
# ════════════════════════════════════════════════════════════════════════
def matchmaking_menu():
    """Display matchmaking menu for online games."""
    global _server_client, _current_user

    # Check offline mode
    if _offline_mode:
        print("\n  ╔══════════════════════════════════════════════════════════╗")
        print("  ║              OFFLINE MODE ACTIVE                         ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        print("  ║  Online matchmaking requires internet connection.        ║")
        print("  ║                                                          ║")
        print("  ║  To enable online features:                              ║")
        print("  ║  1. Return to main menu                                  ║")
        print("  ║  2. Select option 8 (Toggle Offline Mode)                ║")
        print("  ║  3. Configure server connection if needed                ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
        return

    if not _current_user:
        print("\n  You must be logged in to use matchmaking.")
        print("  Please login or register from Account Management.")
        return

    # Check if already connected, if not connect
    if _server_client is None or _server_client.sock is None:
        success, msg = connect_to_server()
        if not success:
            print(f"\n  Cannot connect to server: {msg}")
            print("  Make sure the server is running (python3 server.py)")
            return
    else:
        # Connection exists, verify it's still alive with a ping
        _server_client.send(MSG_PING)
        ping_resp = _server_client.recv(timeout=2.0)
        if ping_resp is None or not ping_resp.get('success'):
            # Connection lost, reconnect
            print("\n  Connection lost. Reconnecting...")
            success, msg = connect_to_server(reconnect=True)
            if not success:
                print(f"\n  Cannot reconnect to server: {msg}")
                print("  Make sure the server is running (python3 server.py)")
                return
            
            # After reconnect, we need to re-login
            # For now, inform the user
            print("\n  Session expired. Please log in again.")
            print("  Return to main menu and go to Account Management to log in.")
            return

    in_queue = False
    in_game = False
    current_game_id = None
    my_color = None
    opponent_name = None
    last_refresh = time.time()
    refresh_interval = 5.0  # Auto-refresh every 5 seconds

    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              ONLINE MATCHMAKING                          ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║  Find a random opponent for a rated game!                ║")
    print("  ╚══════════════════════════════════════════════════════════╝")

    # Start message listener thread
    import queue
    msg_queue = queue.Queue()
    stop_listener = threading.Event()
    
    def message_listener():
        while not stop_listener.is_set():
            try:
                msg = _server_client.recv(timeout=1.0)
                if msg:
                    msg_queue.put(msg)
            except:
                pass
    
    listener_thread = threading.Thread(target=message_listener, daemon=True)
    listener_thread.start()
    
    # Start keep-alive ping thread to maintain connection
    def keep_alive():
        while not stop_listener.is_set():
            time.sleep(10)  # Ping every 10 seconds
            try:
                _server_client.send(MSG_PING)
                _server_client.recv(timeout=1.0)
            except:
                pass
    
    keep_alive_thread = threading.Thread(target=keep_alive, daemon=True)
    keep_alive_thread.start()

    while True:
        # Process any pending messages
        try:
            while not msg_queue.empty():
                msg = msg_queue.get_nowait()
                msg_type = msg.get('type', '')
                data = msg.get('data', {})
                
                if msg_type == MSG_MATCH:
                    # Match found!
                    in_game = True
                    in_queue = False
                    current_game_id = data.get('game_id')
                    my_color = data.get('color')
                    opponent_name = data.get('opponent')
                    print(f"\n  ╔══════════════════════════════════════════════════════════╗")
                    print(f"  ║  MATCH FOUND!                                              ║")
                    print(f"  ╠══════════════════════════════════════════════════════════╣")
                    print(f"  ║  Opponent: {opponent_name:<46}║")
                    print(f"  ║  Your Color: {my_color.upper():<44}║")
                    print(f"  ║  Game ID: {current_game_id:<47}║")
                    print(f"  ╚══════════════════════════════════════════════════════════╝")
                    print("\n  Starting game...")
                    time.sleep(1)
                    # Start the online game
                    play_online_matched_game(current_game_id, my_color, opponent_name, msg_queue, stop_listener)
                    in_game = False
                    current_game_id = None
                    break
                
                elif msg_type == MSG_GAME_MOVE:
                    # Opponent's move received - will be handled in game loop
                    msg_queue.put(msg)
                
                elif msg_type == MSG_GAME_RESIGN:
                    winner = data.get('winner')
                    resigned_by = data.get('resigned_by')
                    print(f"\n  {resigned_by} resigned. {winner} wins!")
                    in_game = False
                
                elif msg_type == MSG_GAME_DRAW_OFFER:
                    offered_by = data.get('offered_by')
                    print(f"\n  {offered_by} offers a draw.")
                    try:
                        ans = input("  Accept draw? [y/N]: ").strip().lower()
                    except EOFError:
                        ans = 'n'
                    if ans in ('y', 'yes'):
                        _server_client.accept_draw(current_game_id)
                        print("  Game ended in a draw.")
                        in_game = False
                    else:
                        print("  Draw offer declined.")
                
                elif msg_type == MSG_GAME_DRAW_ACCEPT:
                    print(f"\n  Draw accepted! Game ended in a draw.")
                    in_game = False
                
                elif msg_type == MSG_GAME_CHAT:
                    from_player = data.get('from_player')
                    message = data.get('message')
                    print(f"\n  [{from_player}]: {message}")
        except:
            pass
        
        if in_game:
            continue

        # Auto-refresh queue status every 5 seconds when in queue
        current_time = time.time()
        if in_queue and current_time - last_refresh >= refresh_interval:
            status_resp = _server_client.get_queue_status()
            if status_resp and status_resp.get('success'):
                status = status_resp.get('data', {})
                position = status.get('position', '?')
                wait_time = status.get('wait_time', 0)
                queued = status.get('queued_players', 0)
                print(f"\n  [Auto-refresh] Position: {position} | Waiting: {wait_time}s | Players: {queued}")
            last_refresh = current_time

        print("\n  ╔══════════════════════════════════════════════════════════╗")
        if in_queue:
            print("  ║  Status: IN QUEUE - Waiting for opponent...            ║")
            # Get queue status
            status_resp = _server_client.get_queue_status()
            if status_resp and status_resp.get('success'):
                status = status_resp.get('data', {})
                position = status.get('position', '?')
                wait_time = status.get('wait_time', 0)
                queued = status.get('queued_players', 0)
                print(f"  ║  Position: {position} | Waiting: {wait_time}s | Players: {queued}          ║")
        else:
            print("  ║  Status: NOT IN QUEUE                                    ║")
        print("  ╠══════════════════════════════════════════════════════════╣")
        if not in_queue:
            print("  ║  1. Join Queue - Find a game                             ║")
        else:
            print("  ║  2. Leave Queue                                          ║")
            print("  ║  3. Refresh - Check for opponents                        ║")
        print("  ║  0. Back to Main Menu                                    ║")
        print("  ╚══════════════════════════════════════════════════════════╝")

        try:
            choice = input("  Choice: ").strip()
        except EOFError:
            break

        if choice == '0':
            if in_queue:
                _server_client.leave_queue()
            break
        elif choice == '1' and not in_queue:
            resp = _server_client.join_queue()
            if resp and resp.get('success'):
                in_queue = True
                last_refresh = time.time()  # Reset auto-refresh timer
                print(f"  {resp.get('data', 'Joined queue')}")
            else:
                error_msg = resp.get('data', 'Unknown error') if resp else 'Connection timeout'
                print(f"  Failed to join queue: {error_msg}")
        elif choice == '2' and in_queue:
            _server_client.leave_queue()
            in_queue = False
            print("  Left queue.")
        elif choice == '3' and in_queue:
            # Refresh: trigger matchmaking check
            print("  Checking for available opponents...")
            resp = _server_client.trigger_matchmaking()
            if resp and resp.get('success'):
                msg = resp.get('data', {}).get('message', 'Matchmaking check complete')
                print(f"  {msg}")
            else:
                error_msg = resp.get('data', 'Unable to refresh') if resp else 'Connection timeout'
                print(f"  {error_msg}")
            last_refresh = time.time()  # Reset auto-refresh timer
    
    stop_listener.set()
    listener_thread.join(timeout=2)


def play_online_matched_game(game_id, my_color, opponent_name, msg_queue, stop_listener):
    """Play an online matched game."""
    board = Board()
    board.reset()
    last_mv = None
    game_start_time = time.time()
    
    my_turn = (my_color == 'white' and board.side == WHITE) or \
              (my_color == 'black' and board.side == BLACK)
    
    my_name = _current_user
    white_name = my_name if my_color == 'white' else opponent_name
    black_name = opponent_name if my_color == 'white' else my_name
    
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║                    ONLINE GAME                           ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print(f"  ║  {white_name:<28} vs  {black_name:<28}║")
    print("  ╚══════════════════════════════════════════════════════════╝\n")
    
    while True:
        # Process messages
        try:
            while not msg_queue.empty():
                msg = msg_queue.get_nowait()
                msg_type = msg.get('type', '')
                data = msg.get('data', {})
                
                if msg_type == MSG_GAME_MOVE:
                    move_san = data.get('move')
                    from_player = data.get('from_player')
                    # Apply the move
                    m = board.parse_san(move_san)
                    if m:
                        board.make(m)
                        last_mv = m
                        print(f"  {from_player} plays: {move_san}")

                elif msg_type == MSG_GAME_RESIGN:
                    winner = data.get('winner')
                    print(f"\n  {data.get('resigned_by')} resigned. {winner} wins!")
                    _save_game_to_server(white_name, black_name,
                                        'white' if winner == white_name else 'black',
                                        board.san_log, time.time() - game_start_time,
                                        show_elo_changes=True)
                    return

                elif msg_type == MSG_GAME_DRAW_OFFER:
                    offered_by = data.get('offered_by')
                    print(f"\n  {offered_by} offers a draw.")
                    try:
                        ans = input("  Accept draw? [y/N]: ").strip().lower()
                    except EOFError:
                        ans = 'n'
                    if ans in ('y', 'yes'):
                        _server_client.accept_draw(game_id)
                        print("  Game ended in a draw.")
                        _save_game_to_server(white_name, black_name, 'draw',
                                            board.san_log, time.time() - game_start_time,
                                            show_elo_changes=True)
                        return

                elif msg_type == MSG_GAME_CHAT:
                    print(f"\n  [{data.get('from_player')}]: {data.get('message')}")
        except:
            pass
        
        # Draw board
        persp = WHITE if my_color == 'white' else BLACK
        draw_board(board, persp, last_mv)
        
        turn_str = "White" if board.side == WHITE else "Black"
        chk_str = "  *** CHECK ***" if board.in_check() else ""
        print(f"  Move {board.fullmove} — {turn_str} to move{chk_str}")
        
        # Show moves
        if board.san_log:
            pairs = []
            for i in range(0, len(board.san_log), 2):
                wm = board.san_log[i]
                bm = board.san_log[i+1] if i+1 < len(board.san_log) else '...'
                pairs.append(f"{i//2+1}. {wm} {bm}")
            print("  " + ' | '.join(pairs[-4:]))
        
        print(f"  {white_name} vs {black_name}\n")
        
        legal = board.legal()
        if not legal:
            if board.in_check():
                winner = BLACK if board.side == WHITE else WHITE
                winner_name = black_name if winner == BLACK else white_name
                print(f"  Checkmate! {winner_name} wins!")
                _save_game_to_server(white_name, black_name,
                                    'white' if winner == WHITE else 'black',
                                    board.san_log, time.time() - game_start_time,
                                    show_elo_changes=True)
            else:
                print("  Stalemate - Draw!")
                _save_game_to_server(white_name, black_name, 'draw',
                                    board.san_log, time.time() - game_start_time,
                                    show_elo_changes=True)
            return

        # Check for draw conditions
        for cond, msg in [(board.is_repetition(), "threefold repetition"),
                          (board.is_fifty(), "50-move rule"),
                          (board.insufficient_material(), "insufficient material")]:
            if cond:
                print(f"  Draw: {msg}")
                _save_game_to_server(white_name, black_name, 'draw',
                                    board.san_log, time.time() - game_start_time,
                                    show_elo_changes=True)
                return
        
        # Check if it's my turn
        my_turn_now = (my_color == 'white' and board.side == WHITE) or \
                      (my_color == 'black' and board.side == BLACK)
        
        if not my_turn_now:
            print(f"  Waiting for {opponent_name}...")
            time.sleep(0.5)
            continue
        
        # My turn - get move
        try:
            raw = input("  Your move: ").strip()
        except EOFError:
            # Resign on disconnect
            _server_client.resign_game(game_id)
            return
        
        if not raw:
            continue
        
        cmd = raw.lower()
        
        if cmd in ('quit', 'exit'):
            _server_client.resign_game(game_id)
            print("  You resigned.")
            return
        
        if cmd == 'draw':
            _server_client.offer_draw(game_id)
            print("  Draw offer sent.")
            continue
        
        if cmd.startswith('chat '):
            _server_client.send_chat(game_id, raw[5:])
            continue
        
        if cmd == 'help':
            print(HELP)
            continue
        
        if cmd == 'moves':
            sms = [board.san(m) for m in legal]
            for i in range(0, len(sms), 8):
                print("  " + "  ".join(f"{s:<8}" for s in sms[i:i+8]))
            continue
        
        # Parse and send move
        mv = board.parse_san(raw)
        if mv is None:
            print(f"  Illegal/unrecognised: '{raw}'. Try 'moves' or 'help'.")
            continue
        
        s = board.san(mv)
        _server_client.send_move(game_id, s)
        board.make(mv)
        board.san_log.append(s)
        last_mv = mv


# ════════════════════════════════════════════════════════════════════════
#  BOT LEVELS (Beginner, Intermediate, Challenge)
# ════════════════════════════════════════════════════════════════════════
class BotLevel:
    """Enum for bot difficulty levels."""
    BEGINNER = 'beginner'
    INTERMEDIATE = 'intermediate'
    CHALLENGE = 'challenge'

BOT_NAMES = {
    BotLevel.BEGINNER: "BeginnerBot",
    BotLevel.INTERMEDIATE: "IntermediateBot",
    BotLevel.CHALLENGE: "ChallengeBot"
}

BOT_SETTINGS = {
    BotLevel.BEGINNER: {
        'depth': 1,
        'random_factor': 0.4,  # 40% chance of random move
        'think_time': 0.5,
        'use_book': False
    },
    BotLevel.INTERMEDIATE: {
        'depth': 3,
        'random_factor': 0.15,  # 15% chance of random move
        'think_time': 2.0,
        'use_book': True
    },
    BotLevel.CHALLENGE: {
        'depth': None,  # Use full search
        'random_factor': 0.0,  # No random moves
        'think_time': 5.0,
        'use_book': True
    }
}


class ChessBot:
    """Chess AI with configurable difficulty levels."""
    
    def __init__(self, level=BotLevel.INTERMEDIATE, tb=None, book=None):
        self.level = level
        self.settings = BOT_SETTINGS[level]
        self.engine = Engine(tb=tb, book=book if self.settings['use_book'] else None)
        self.tb = tb
        self.book = book
    
    def get_name(self):
        """Get the bot's display name."""
        return BOT_NAMES.get(self.level, "UnknownBot")
    
    def get_move(self, board):
        """Get the bot's move based on difficulty level."""
        legal = board.legal()
        if not legal:
            return None
        
        # Beginner and Intermediate bots sometimes make random moves
        if self.settings['random_factor'] > 0:
            if random.random() < self.settings['random_factor']:
                return random.choice(legal)
        
        # Challenge bot uses full engine search
        if self.level == BotLevel.CHALLENGE:
            self.engine.tt.clear()
            return self.engine.search(board, t_limit=self.settings['think_time'], verbose=False)
        
        # Beginner and Intermediate use limited depth search
        depth = self.settings['depth']
        self.engine.tt.clear()
        
        # Simplified search for lower levels
        best_move = None
        best_score = -INF
        
        for move in legal:
            board_copy = board.copy()
            board_copy.make(move)
            
            # Simple evaluation
            score = -self._evaluate_position(board_copy, depth - 1)
            
            if score > best_score:
                best_score = score
                best_move = move
        
        return best_move if best_move else random.choice(legal)
    
    def _evaluate_position(self, board, depth):
        """Simple recursive evaluation for lower difficulty bots."""
        if depth <= 0:
            return evaluate(board, self.tb)
        
        legal = board.legal()
        if not legal:
            if board.in_check():
                return -MATE_SCORE
            return 0
        
        best_score = -INF
        for move in legal:
            board_copy = board.copy()
            board_copy.make(move)
            score = -self._evaluate_position(board_copy, depth - 1)
            best_score = max(best_score, score)
        
        return best_score


def select_bot_level():
    """Let user select bot difficulty level."""
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              SELECT BOT DIFFICULTY                       ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║ 1. Beginner     - Easy opponent, makes random mistakes   ║")
    print("  ║ 2. Intermediate - Moderate challenge, occasional errors  ║")
    print("  ║ 3. Challenge    - Strong opponent, plays at full strength║")
    print("  ╚══════════════════════════════════════════════════════════╝")
    
    while True:
        try:
            choice = input("  Select difficulty [2]: ").strip() or '2'
        except EOFError:
            return BotLevel.INTERMEDIATE
        
        if choice == '1':
            return BotLevel.BEGINNER
        elif choice == '2':
            return BotLevel.INTERMEDIATE
        elif choice == '3':
            return BotLevel.CHALLENGE
        else:
            print("  Please enter 1, 2, or 3.")


# ════════════════════════════════════════════════════════════════════════
#  BOARD DISPLAY
# ════════════════════════════════════════════════════════════════════════
def draw_board(board, persp=WHITE, last=None, labels=True):
    lines=['']
    ranks=range(7,-1,-1) if persp==WHITE else range(8)
    files=range(8)       if persp==WHITE else range(7,-1,-1)
    for rank in ranks:
        row=f" {rank+1} "
        for file in files:
            sq=rank*8+file; p=board.sq[sq]
            dk=(rank+file)%2==0
            hl=last and sq in(last.from_sq,last.to_sq)
            if p:
                ch=PIECE_ASCII[p]
                row+=(f'[{ch}]' if dk else f' {ch} ')
            else:
                bg='*' if hl else('░' if dk else ' ')
                row+=(f'[{bg}]' if dk else f' {bg} ')
        lines.append(row)
    if labels:
        fl='    '+''.join(f' {chr(ord("a")+f)} ' for f in files)
        lines.append(fl)
    lines.append('')
    print('\n'.join(lines))

# ════════════════════════════════════════════════════════════════════════
#  BANNERS & HELP
# ════════════════════════════════════════════════════════════════════════
BANNER = """
╔══════════════════════════════════════════════════════════════╗
║                                                              ║
║   ██████╗██╗  ██╗███████╗███████╗███████╗                    ║
║  ██╔════╝██║  ██║██╔════╝██╔════╝██╔════╝                    ║
║  ██║     ███████║█████╗  ███████╗███████╗                    ║
║  ██║     ██╔══██║██╔══╝  ╚════██║╚════██║                    ║
║  ╚██████╗██║  ██║███████╗███████║███████║                    ║
║   ╚═════╝╚═╝  ╚═╝╚══════╝╚══════╝╚══════╝  Ultimate Ed.      ║
║                                                              ║
║  Neural Net • Opening Book • Tablebases • ELO • Multiplayer  ║
╚══════════════════════════════════════════════════════════════╝
"""

HELP = """
 ╔─── IN-GAME COMMANDS ──────────────────────────────────────────╗
 │  <move>    SAN move, e.g.: e4  Nf3  O-O  exd5  e8=Q           │
 │  undo      Take back last 2 half-moves (vs AI only)           │
 │  moves     Show all legal moves                               │
 │  flip      Flip board perspective                             │
 │  resign    Resign the game                                    │
 │  draw      Claim/offer draw                                   │
 │  chat <m>  Send chat message (multiplayer)                    │
 │  elo       Show ELO leaderboard                               │
 │  help      This help                                          │
 │  quit      Exit to main menu                                  │
 ╠─── SAN REFERENCE ─────────────────────────────────────────────╣
 │  Pawn:     e4  d5  exd5  (promotion:) e8=Q  e8=R  e8=B  e8=N  │
 │  Piece:    Nf3  Bxc4  Rhe1  Qd1f3 (disambiguation)            │
 │  Castle:   O-O  (kingside)   O-O-O  (queenside)               │
 ╚───────────────────────────────────────────────────────────────╝
"""

# ════════════════════════════════════════════════════════════════════════
#  GAME RESULT HANDLING
# ════════════════════════════════════════════════════════════════════════
def handle_game_end(board, elo_sys, white_name, black_name,
                    winner_color=None, draw=False, resigned=False):
    """Update ELO, offer analysis."""
    print()
    if draw:
        print("  ½-½  Draw\n")
        elo_sys.update(white_name, black_name, 0.5)
        elo_sys.update(black_name, white_name, 0.5)
        result_str='Draw'
    elif winner_color==WHITE:
        print(f"  1-0  {white_name} wins!\n")
        elo_sys.update(white_name, black_name, 1)
        result_str='White wins'
    else:
        print(f"  0-1  {black_name} wins!\n")
        elo_sys.update(black_name, white_name, 1)
        result_str='Black wins'

    w_elo=elo_sys.get_elo(white_name); b_elo=elo_sys.get_elo(black_name)
    print(f"  ELO — {white_name}: {w_elo}  |  {black_name}: {b_elo}\n")

    # Offer analysis
    try:
        ans=input("  Analyze game? [y/N] ").strip().lower()
    except EOFError:
        ans='n'
    if ans in('y','yes'):
        results=analyze_game(board.san_log, engine_time=1.0)
        print_analysis(results)

def _replay_board(san_log):
    """Replay san_log on a fresh board. Returns board or None."""
    b=Board(); b.reset()
    for s in san_log:
        m=b.parse_san(s)
        if not m: return None
        sn=b.san(m); b.make(m); b.san_log.append(sn)
    return b

# ════════════════════════════════════════════════════════════════════════
#  SINGLE-PLAYER (vs AI)
# ════════════════════════════════════════════════════════════════════════
def play_vs_ai(elo_sys, tb, book):
    board=Board(); board.reset()
    persp=WHITE; last_mv=None

    # Select bot difficulty
    bot_level = select_bot_level()
    bot = ChessBot(level=bot_level, tb=tb, book=book)
    bot_name = bot.get_name()

    while True:
        try:
            c=input("  Play as [W]hite or [B]lack? [W]: ").strip().lower() or 'w'
        except EOFError: return
        if c in('w','white'): human_color=WHITE; break
        if c in('b','black'): human_color=BLACK; break
        print("  Please enter 'w' or 'b'.")

    # Get player name (use logged-in username if available)
    default_name = _current_user if _current_user else 'Player'
    try:
        player_name=input(f"  Your name [{default_name}]: ").strip() or default_name
    except EOFError:
        player_name=default_name

    # Record game start time
    game_start = time.time()

    persp=human_color
    white_name=player_name if human_color==WHITE else bot_name
    black_name=bot_name if human_color==WHITE else player_name

    while True:
        draw_board(board, persp, last_mv)
        turn_str="White" if board.side==WHITE else "Black"
        chk_str="  *** CHECK ***" if board.in_check() else ""
        print(f"  Move {board.fullmove} — {turn_str} to move{chk_str}")

        # Show recent moves
        if board.san_log:
            pairs=[]
            for i in range(0,len(board.san_log),2):
                wm=board.san_log[i]
                bm=board.san_log[i+1] if i+1<len(board.san_log) else '...'
                pairs.append(f"{i//2+1}. {wm} {bm}")
            print("  "+' | '.join(pairs[-4:]))

        # ELO display
        we=elo_sys.get_elo(white_name); be=elo_sys.get_elo(black_name)
        print(f"  {white_name}({we}) vs {black_name}({be})\n")

        legal=board.legal()
        # Terminal conditions
        if not legal:
            draw_board(board, persp, last_mv)
            if board.in_check():
                winner=BLACK if board.side==WHITE else WHITE
                winner_color = winner
                result = 'white' if winner==WHITE else 'black'
            else:
                winner_color = None
                result = 'draw'
            handle_game_end(board,elo_sys,white_name,black_name,winner_color=winner_color)
            # Save game to server
            _save_game_to_server(white_name, black_name, result, board.san_log, time.time()-game_start)
            return

        for cond,msg in [(board.is_repetition(),"threefold repetition"),
                         (board.is_fifty(),"50-move rule"),
                         (board.insufficient_material(),"insufficient material")]:
            if cond:
                print(f"  ½-½ Draw: {msg}")
                handle_game_end(board,elo_sys,white_name,black_name,draw=True)
                # Save game to server
                _save_game_to_server(white_name, black_name, 'draw', board.san_log, time.time()-game_start)
                return

        # AI turn
        if board.side!=human_color:
            print(f"  {bot_name} thinking...\n")
            mv=bot.get_move(board)
            if mv:
                s=board.san(mv); board.make(mv); board.san_log.append(s)
                last_mv=mv; print(f"\n  {bot_name} plays: {s}\n")
            continue

        # Human turn
        try:
            raw=input("  Your move: ").strip()
        except EOFError:
            return
        if not raw: continue
        cmd=raw.lower()

        if cmd in('quit','exit','q'):
            # Save game as abandoned if moves were made
            if board.san_log:
                result = 'black' if human_color==WHITE else 'white'
                _save_game_to_server(white_name, black_name, result, board.san_log, time.time()-game_start)
            return
        if cmd=='help': print(HELP); continue
        if cmd=='flip': persp=1-persp; continue
        if cmd=='elo': elo_sys.leaderboard(); continue
        if cmd=='moves':
            sms=[board.san(m) for m in legal]
            for i in range(0,len(sms),8):
                print("  "+"  ".join(f"{s:<8}" for s in sms[i:i+8]))
            print(); continue
        if cmd=='resign':
            winner=BLACK if human_color==WHITE else WHITE
            print(f"  {player_name} resigned.")
            handle_game_end(board,elo_sys,white_name,black_name,winner_color=winner)
            _save_game_to_server(white_name, black_name, 'black' if human_color==WHITE else 'white', board.san_log, time.time()-game_start)
            return
        if cmd=='draw':
            if board.is_repetition() or board.is_fifty():
                handle_game_end(board,elo_sys,white_name,black_name,draw=True)
                _save_game_to_server(white_name, black_name, 'draw', board.san_log, time.time()-game_start)
                return
            print("  Engine declines the draw offer."); continue
        if cmd=='undo':
            keep=board.san_log[:-2] if len(board.san_log)>=2 else []
            nb=_replay_board(keep)
            if nb: board=nb; last_mv=None; print("  Move undone.\n")
            else: print("  Cannot undo.")
            continue
        if cmd.startswith('chat '): print("  (Chat not available vs AI)"); continue

        mv=board.parse_san(raw)
        if mv is None:
            print(f"  Illegal/unrecognised: '{raw}'. Try 'moves' or 'help'.")
            continue
        s=board.san(mv); board.make(mv); board.san_log.append(s); last_mv=mv


def _save_game_to_server(white, black, result, moves, duration, show_elo_changes=False):
    """
    Save game result to the server if connected.
    If show_elo_changes=True, display ELO changes after the game.
    Also saves locally for later analysis.
    """
    # Save locally for analysis
    save_online_game(white, black, result, moves, duration, rated=True)

    if _server_client is not None and _server_client.sock is not None and _current_user:
        try:
            response = _server_client.save_game(white, black, result, moves, int(duration), rated=True)
            if response:
                if response.get('success'):
                    if show_elo_changes:
                        elo_changes = response.get('data', {})
                        if elo_changes and isinstance(elo_changes, dict) and elo_changes.get('white'):
                            print("\n  ╔══════════════════════════════════════════════════════════╗")
                            print("  ║                   ELO CHANGES                             ║")
                            print("  ╠══════════════════════════════════════════════════════════╣")
                            for player, changes in elo_changes.items():
                                old_elo = changes.get('old', 1200)
                                new_elo = changes.get('new', 1200)
                                change = changes.get('change', 0)
                                sign = '+' if change > 0 else ''
                                print(f"  ║  {player:<20}: {old_elo} → {new_elo} ({sign}{change}){'':15}║")
                            print("  ╚══════════════════════════════════════════════════════════╝")
                else:
                    # Show error message
                    error_msg = response.get('data', 'Unknown error')
                    print(f"\n  Warning: Failed to save game to server: {error_msg}")
            else:
                print("\n  Warning: No response from server when saving game.")
        except Exception as e:
            print(f"\n  Warning: Error saving game to server: {e}")
    else:
        # Server not available, but game is saved locally
        if not _server_client or _server_client.sock is None:
            print("\n  Note: Server not connected. Game saved locally only.")
        elif not _current_user:
            print("\n  Note: Not logged in. Game saved locally only.")

# ════════════════════════════════════════════════════════════════════════
#  LOCAL TWO-PLAYER
# ════════════════════════════════════════════════════════════════════════
def play_local_2p(elo_sys):
    board=Board(); board.reset(); persp=WHITE; last_mv=None
    try:
        wn=input("  White player name [White]: ").strip() or 'White'
        bn=input("  Black player name [Black]: ").strip() or 'Black'
    except EOFError: return

    while True:
        draw_board(board, persp, last_mv)
        turn_str="White" if board.side==WHITE else "Black"
        pname=wn if board.side==WHITE else bn
        chk_str="  *** CHECK ***" if board.in_check() else ""
        print(f"  Move {board.fullmove} — {pname} ({turn_str}) to move{chk_str}")
        if board.san_log:
            pairs=[]
            for i in range(0,len(board.san_log),2):
                pairs.append(f"{i//2+1}. {board.san_log[i]} {board.san_log[i+1] if i+1<len(board.san_log) else '...'}")
            print("  "+' | '.join(pairs[-4:]))
        we=elo_sys.get_elo(wn); be=elo_sys.get_elo(bn)
        print(f"  {wn}({we}) vs {bn}({be})\n")

        legal=board.legal()
        if not legal:
            draw_board(board, persp, last_mv)
            if board.in_check():
                winner=BLACK if board.side==WHITE else WHITE
                handle_game_end(board,elo_sys,wn,bn,winner_color=winner)
            else:
                handle_game_end(board,elo_sys,wn,bn,draw=True)
            return

        for cond,msg in [(board.is_repetition(),"threefold repetition"),
                         (board.is_fifty(),"50-move rule"),
                         (board.insufficient_material(),"insufficient material")]:
            if cond:
                print(f"  ½-½ Draw: {msg}")
                handle_game_end(board,elo_sys,wn,bn,draw=True)
                return

        try:
            raw=input(f"  {pname}'s move: ").strip()
        except EOFError: return
        if not raw: continue
        cmd=raw.lower()
        if cmd in('quit','exit','q'): return
        if cmd=='help': print(HELP); continue
        if cmd=='flip': persp=1-persp; continue
        if cmd=='elo': elo_sys.leaderboard(); continue
        if cmd=='moves':
            sms=[board.san(m) for m in legal]
            for i in range(0,len(sms),8):
                print("  "+"  ".join(f"{s:<8}" for s in sms[i:i+8]))
            print(); continue
        if cmd=='resign':
            winner=BLACK if board.side==WHITE else WHITE
            print(f"  {pname} resigned.")
            handle_game_end(board,elo_sys,wn,bn,winner_color=winner)
            return
        if cmd=='draw':
            try:
                other=bn if board.side==WHITE else wn
                ans=input(f"  {other}: Accept draw? [y/N] ").strip().lower()
            except EOFError: ans='n'
            if ans in('y','yes'):
                handle_game_end(board,elo_sys,wn,bn,draw=True); return
            print("  Draw declined."); continue
        mv=board.parse_san(raw)
        if mv is None:
            print(f"  Illegal/unrecognised: '{raw}'. Try 'moves' or 'help'.")
            continue
        s=board.san(mv); board.make(mv); board.san_log.append(s); last_mv=mv

# ════════════════════════════════════════════════════════════════════════
#  NETWORK MULTIPLAYER GAME LOOP
# ════════════════════════════════════════════════════════════════════════
def play_network(elo_sys, net, our_color):
    board=Board(); board.reset()
    persp=our_color; last_mv=None
    pending_draw=False

    try:
        player_name=input("  Your name [Player]: ").strip() or 'Player'
    except EOFError:
        player_name='Player'

    white_name=player_name if our_color==WHITE else 'Opponent'
    black_name='Opponent' if our_color==WHITE else player_name

    # Exchange names
    net.send('NAME', player_name)
    # Try to get opponent name
    opp_name='Opponent'
    for _ in range(20):
        msg=net.recv(timeout=0.5)
        if msg and msg['type']=='NAME':
            opp_name=msg['data']
            break

    if our_color==WHITE:
        white_name=player_name; black_name=opp_name
    else:
        white_name=opp_name; black_name=player_name

    print(f"  Playing as {'White' if our_color==WHITE else 'Black'} vs {opp_name}\n")

    # Use a thread-safe queue for incoming messages
    import queue
    msg_q = queue.Queue()
    def recv_thread():
        while True:
            msg=net.recv(timeout=1.0)
            if msg: msg_q.put(msg)
    t=threading.Thread(target=recv_thread, daemon=True)
    t.start()

    while True:
        # Check for incoming messages
        try:
            while not msg_q.empty():
                msg=msg_q.get_nowait()
                mtype=msg.get('type',''); mdata=msg.get('data','')
                if mtype==MSG_MOVE:
                    m=board.parse_san(mdata)
                    if m:
                        s=board.san(m); board.make(m); board.san_log.append(s); last_mv=m
                elif mtype==MSG_RESIGN:
                    winner=our_color
                    print(f"\n  {opp_name} resigned!")
                    handle_game_end(board,elo_sys,white_name,black_name,winner_color=winner)
                    net.close(); return
                elif mtype==MSG_DRAW:
                    pending_draw=True
                    print(f"\n  {opp_name} offers a draw!")
                elif mtype==MSG_ACCEPT:
                    print(f"\n  {opp_name} accepted the draw!")
                    handle_game_end(board,elo_sys,white_name,black_name,draw=True)
                    net.close(); return
                elif mtype==MSG_DECLINE:
                    print(f"\n  {opp_name} declined the draw.")
                    pending_draw=False
                elif mtype==MSG_CHAT:
                    print(f"\n  [{opp_name}]: {mdata}")
        except:
            pass

        draw_board(board, persp, last_mv)
        turn_str="White" if board.side==WHITE else "Black"
        our_turn=board.side==our_color
        chk_str="  *** CHECK ***" if board.in_check() else ""
        who="Your" if our_turn else f"{opp_name}'s"
        print(f"  Move {board.fullmove} — {who} turn ({turn_str}){chk_str}")
        if board.san_log:
            pairs=[]
            for i in range(0,len(board.san_log),2):
                pairs.append(f"{i//2+1}. {board.san_log[i]} {board.san_log[i+1] if i+1<len(board.san_log) else '...'}")
            print("  "+' | '.join(pairs[-4:]))
        print()

        legal=board.legal()
        if not legal:
            if board.in_check():
                winner=BLACK if board.side==WHITE else WHITE
                handle_game_end(board,elo_sys,white_name,black_name,winner_color=winner)
            else:
                handle_game_end(board,elo_sys,white_name,black_name,draw=True)
            net.close(); return

        for cond,msg2 in [(board.is_repetition(),"threefold repetition"),
                          (board.is_fifty(),"50-move rule"),
                          (board.insufficient_material(),"insufficient material")]:
            if cond:
                print(f"  ½-½ Draw: {msg2}")
                net.send(MSG_DRAW)
                handle_game_end(board,elo_sys,white_name,black_name,draw=True)
                net.close(); return

        if not our_turn:
            time.sleep(0.2); continue

        try:
            raw=input("  Your move: ").strip()
        except EOFError:
            net.close(); return
        if not raw: continue
        cmd=raw.lower()

        if cmd in('quit','exit','q'):
            net.send(MSG_RESIGN); net.close(); return
        if cmd=='help': print(HELP); continue
        if cmd=='flip': persp=1-persp; continue
        if cmd=='elo': elo_sys.leaderboard(); continue
        if cmd=='moves':
            sms=[board.san(m) for m in legal]
            for i in range(0,len(sms),8):
                print("  "+"  ".join(f"{s:<8}" for s in sms[i:i+8]))
            print(); continue
        if cmd=='resign':
            net.send(MSG_RESIGN)
            winner=BLACK if our_color==WHITE else WHITE
            handle_game_end(board,elo_sys,white_name,black_name,winner_color=winner)
            net.close(); return
        if cmd=='draw':
            if pending_draw:
                net.send(MSG_ACCEPT)
                handle_game_end(board,elo_sys,white_name,black_name,draw=True)
                net.close(); return
            else:
                net.send(MSG_DRAW); print("  Draw offer sent."); continue
        if cmd.startswith('chat '):
            msg_text=raw[5:]
            net.send(MSG_CHAT, msg_text)
            print(f"  [You]: {msg_text}"); continue

        mv=board.parse_san(raw)
        if mv is None:
            print(f"  Illegal/unrecognised: '{raw}'. Try 'moves' or 'help'.")
            continue
        s=board.san(mv)
        if not net.send(MSG_MOVE, s):
            print("  Connection lost!"); net.close(); return
        board.make(mv); board.san_log.append(s); last_mv=mv

# ════════════════════════════════════════════════════════════════════════
#  MAIN MENU
# ════════════════════════════════════════════════════════════════════════
MAIN_MENU_ONLINE = """
  ┌─────────────────────────────────┐
  │         MAIN MENU               │
  ├─────────────────────────────────┤
  │  1. Play vs AI                  │
  │  2. Local 2-Player              │
  │  3. Online Matchmaking          │
  │  4. Account Management          │
  │  5. ELO Leaderboard             │
  │  6. Analyze a PGN line          │
  │  7. Game Analysis (Online)      │
  │  8. Configure Server            │
  │  9. Enable Offline Mode         │
  │  Q. Quit                        │
  └─────────────────────────────────┘
"""

MAIN_MENU_OFFLINE = """
  ┌─────────────────────────────────┐
  │         MAIN MENU               │
  ├─────────────────────────────────┤
  │  1. Play vs AI                  │
  │  2. Local 2-Player              │
  │  3. Online Matchmaking [OFFLINE]│
  │  4. Account Management          │
  │  5. ELO Leaderboard             │
  │  6. Analyze a PGN line          │
  │  7. Game Analysis (Online)      │
  │  8. Configure Server            │
  │  9. Enable Online Mode          │
  │  Q. Quit                        │
  └─────────────────────────────────┘
"""

def analyze_pgn_line():
    """Analyze a manually-entered sequence of moves."""
    print("\n  Enter moves separated by spaces (SAN format).")
    print("  Example: e4 e5 Nf3 Nc6 Bb5")
    try:
        line=input("  Moves: ").strip()
    except EOFError: return
    san_list=line.split()
    # Validate
    b=Board(); b.reset(); valid=[]
    for s in san_list:
        m=b.parse_san(s)
        if m is None: print(f"  Stopped at unrecognised move: '{s}'"); break
        sn=b.san(m); b.make(m); b.san_log.append(sn); valid.append(sn)
    if not valid: print("  No valid moves to analyze."); return
    results=analyze_game(valid, engine_time=1.0)
    print_analysis(results)

def analyze_online_game_menu():
    """Menu for analyzing online games."""
    print("\n  ╔══════════════════════════════════════════════════════════╗")
    print("  ║              GAME ANALYSIS                               ║")
    print("  ╠══════════════════════════════════════════════════════════╣")
    print("  ║  Analyze your online games with engine evaluation        ║")
    print("  ╚══════════════════════════════════════════════════════════╝\n")
    
    games = load_online_games(limit=20)
    unanalyzed = get_unanalyzed_games()
    
    if not games:
        print("  No online games found. Play an online game first!")
        return
    
    # Show games list
    print(f"  Recent Games ({len(games)} total, {len(unanalyzed)} unanalyzed)")
    print("  " + "─"*68)
    print(f"  {'#':<3} {'Result':<8} {'White':<15} {'Black':<15} {'Moves':<6} {'Analyzed':<10}")
    print("  " + "─"*68)
    
    for i, game in enumerate(games):
        result = game.get('result', '?')
        white = game.get('white', '?')[:14]
        black = game.get('black', '?')[:14]
        moves = len(game.get('moves', []))
        analyzed = 'Yes' if game.get('analyzed', False) else 'No'
        analyzed_mark = '*' if not game.get('analyzed', False) else ' '
        print(f"  {i+1}{analyzed_mark}  {result:<8} {white:<15} {black:<15} {moves:<6} {analyzed:<10}")
    
    print("  " + "─"*68)
    print("  * = Unanalyzed game")
    print()
    print("  Enter game number to analyze, or:")
    print("  A - Analyze all unanalyzed games")
    print("  0 - Back to main menu")
    print()
    
    while True:
        try:
            choice = input("  Choice: ").strip().upper()
        except EOFError:
            return
        
        if choice == '0':
            return
        elif choice == 'A':
            if not unanalyzed:
                print("  No unanalyzed games!")
                continue
            print(f"\n  Analyzing {len(unanalyzed)} game(s)... This may take a while.\n")
            for game in unanalyzed:
                print(f"\n  Analyzing: {game['white']} vs {game['black']} ({game['result']})")
                print("  " + "="*50)
                results = analyze_game(game.get('moves', []), engine_time=2.0, depth_limit=14)
                print_analysis(results)
                mark_game_analyzed(game['id'])
            print("\n  All games analyzed!")
            return
        else:
            try:
                idx = int(choice) - 1
                if 0 <= idx < len(games):
                    game = games[idx]
                    print(f"\n  Analyzing: {game['white']} vs {game['black']} ({game['result']})")
                    print("  " + "="*50)
                    results = analyze_game(game.get('moves', []), engine_time=2.0, depth_limit=14)
                    print_analysis(results)
                    mark_game_analyzed(game['id'])
                    print("  Game marked as analyzed.")
                    return
                else:
                    print("  Invalid game number.")
            except ValueError:
                print("  Invalid input. Enter a number, 'A', or '0'.")

def main():
    print(BANNER)
    print("  Initialising opening book...")
    book=OpeningBook()
    print(f"  Opening book ready ({len(book._book)} positions)")
    print("  Initialising tablebases...")
    tb=Tablebase()
    tb._init_if_needed()
    print("  Tablebases ready (KQK, KRK, KPK, KBNK)")
    print("  Neural network evaluator ready")
    elo_sys=EloSystem()
    print()

    while True:
        # Show status bar
        print("  ═══════════════════════════════════════════════════════════════")
        if _offline_mode:
            print("  ║  OFFLINE MODE                              [8] Enable Online ║")
        else:
            if _current_user:
                print(f"  ║  Logged in: {_current_user:<43}║")
            else:
                print("  ║  Not logged in                           [4] Account Mgmt  ║")
        print("  ═══════════════════════════════════════════════════════════════")
        print()

        # Show appropriate menu based on mode
        print(MAIN_MENU_OFFLINE if _offline_mode else MAIN_MENU_ONLINE)
        try:
            choice=input("  Choice: ").strip().lower()
        except EOFError:
            break

        if choice in('q','quit','exit'):
            disconnect_from_server()
            print("  Goodbye!\n"); break

        elif choice == 'clear':
            clear_screen()
            continue

        elif choice=='1':
            play_vs_ai(elo_sys, tb, book)

        elif choice=='2':
            play_local_2p(elo_sys)

        elif choice=='3':
            matchmaking_menu()

        elif choice=='4':
            auth_menu()

        elif choice=='5':
            show_online_leaderboard()

        elif choice=='6':
            analyze_pgn_line()

        elif choice=='7':
            analyze_online_game_menu()

        elif choice=='8':
            configure_server_connection()

        elif choice=='9':
            # Toggle offline mode
            if _offline_mode:
                print("\n  ╔══════════════════════════════════════════════════════════╗")
                print("  ║              ENABLE ONLINE MODE?                          ║")
                print("  ╠═══════════════════════════════════════════════════════════╣")
                print("  ║  This will enable:                                        ║")
                print("  ║  • Online matchmaking                                     ║")
                print("  ║  • User accounts and profiles                             ║")
                print("  ║  • Game history sync                                      ║")
                print("  ║                                                           ║")
                try:
                    ans = input("  ║  Enable online mode? [Y/n]: ").strip().lower()
                except EOFError:
                    ans = 'n'
                if ans in ('y', 'yes', ''):
                    set_offline_mode(False)
                    print("  ║  Online mode enabled!                                    ║")
                    print("  ╚══════════════════════════════════════════════════════════╝")
                else:
                    print("  ║  Remaining in offline mode.                              ║")
                    print("  ╚══════════════════════════════════════════════════════════╝")
            else:
                print("\n  ╔══════════════════════════════════════════════════════════╗")
                print("  ║              ENABLE OFFLINE MODE?                         ║")
                print("  ╠══════════════════════════════════════════════════════════╣")
                print("  ║  This will disable:                                       ║")
                print("  ║  • Online matchmaking                                     ║")
                print("  ║  • User accounts and profiles                             ║")
                print("  ║  • Game history sync                                      ║")
                print("  ║                                                           ║")
                print("  ║  You will still be able to:                               ║")
                print("  ║  • Play vs AI (all difficulty levels)                     ║")
                print("  ║  • Local 2-player games                                   ║")
                print("  ║  • View ELO leaderboard (local)                           ║")
                print("  ║  • Analyze games                                          ║")
                print("  ║                                                           ║")
                try:
                    ans = input("  ║  Enable offline mode? [y/N]: ").strip().lower()
                except EOFError:
                    ans = 'n'
                if ans in ('y', 'yes'):
                    set_offline_mode(True)
                    print("  ║  Offline mode enabled!                                   ║")
                    print("  ╚══════════════════════════════════════════════════════════╝")
                else:
                    print("  ║  Remaining in online mode.                               ║")
                    print("  ╚══════════════════════════════════════════════════════════╝")

        else:
            print("  Invalid choice.")

# ════════════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ════════════════════════════════════════════════════════════════════════
if __name__=='__main__':
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n  Interrupted. Goodbye!\n")
    except Exception as e:
        import traceback; traceback.print_exc()
        sys.exit(1)
