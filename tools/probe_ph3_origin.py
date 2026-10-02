# -*- coding: utf-8 -*-
"""PH3s の枠（B ≠ 0 の書き換え）が展開 N = M[n] のどこから来るかを分類する。

  python3 probe_ph3_origin.py <mats.pkl> [limit]

N の列 j は G（j < r）か、ブロック a の列 r + xx（j = r + a·L + xx、L = x − r）。
枠 (i, c) を (i の位置, c の位置, N での種類, M の対応する枠の種類) で数える。
対応する枠: i' = 写像(i)、c' = 写像(c)。c' が M で i' の数える子で書き換えが起きていればその種類、なければ 'none'。
"""
import sys, os, pickle, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collections import Counter
from multiprocessing import Pool
import trio
from probe_close_ph3 import frames, ph3c_kind as ph3s_kind, S, Ctx, split, succ, lt, Z, summ, last, ONE

def frames0(M):
    """B = 0 の書き換えの枠（最初の数える子、hi ≠ 0）: (i, c, 種類)。種類は FC3 の分類。"""
    C = Ctx(list(M))
    if not C.ok: return None
    out = []
    for i in range(len(M)):
        cl = C.CL(i); vi = C.v(i)
        if not cl: continue
        c = cl[0]; s, y, _ = C.o(c)
        if y == Z or not lt((vi, Z, Z), (s, y, Z)): continue
        hi, lo = split(y, (succ(s), Z, Z))
        if hi == Z: continue
        if s == vi: k = '=lim' if (s != Z and last(s) != ONE) else '=BAD'
        else:
            h = summ(hi)[0][0]
            k = '<s+X' if summ(h)[:len(summ(s))] == summ(s) else '<BAD'
        out.append((i, c, k + ('/lo0' if lo == Z else '/lo+')))
    return out

def where(M, n):
    x = len(M) - 1
    if M[x] == (0, 0, 0): return None
    t = max(y for y in range(3) if M[x][y] > 0)
    r = trio.parent(M, t, x)
    return r, x - r, t

def go(M):
    M = list(M); out = Counter(); ex = {}
    w = where(M, 2)
    if w is None: return out, ex
    r, L, t = w
    fM = {(i, c): ph3s_kind(B, hi, lo, s) or 'BAD' for i, c, B, hi, lo, s in (frames(M) or [])}
    fM.update({(i, c): k for i, c, k in (frames0(M) or [])})
    for n in (2, 3):
        N = trio.expand(M, n)
        fN = frames(N)
        if fN is None: continue
        def mp(j):
            if j < r: return ('G', j)
            a, xx = divmod(j - r, L); return ('a%d' % min(a, 2), r + xx)
        allN = [(i, c, ph3s_kind(B, hi, lo, s) or 'BAD') for i, c, B, hi, lo, s in fN] + (frames0(N) or [])
        for i, c, kN in allN:
            (pi, i0), (pc, c0) = mp(i), mp(c)
            kM = fM.get((i0, c0), 'none')
            key = (t, pi, pc, kN, kM)
            out[key] += 1
            if key not in ex: ex[key] = (S(M), n, i, c)
    return out, ex

if __name__ == '__main__':
    mats = pickle.load(open(sys.argv[1], 'rb'))
    if isinstance(mats, (dict, set)): mats = list(mats)
    mats = [m for m in mats if m[-1] != (0, 0, 0)]
    random.Random(1).shuffle(mats)
    if len(sys.argv) > 2: mats = mats[:int(sys.argv[2])]
    c = Counter(); ex = {}
    with Pool(10) as p:
        for o, e in p.imap_unordered(go, mats, chunksize=100):
            c.update(o)
            for k, v in e.items(): ex.setdefault(k, v)
    for k, v in sorted(c.items(), key=lambda kv: (kv[0][3] != 'BAD', -kv[1])):
        print(v, 't=%d i:%s c:%s N:%s M:%s' % k, ex[k] if (k[3] != k[4] or v < 50) else '')
