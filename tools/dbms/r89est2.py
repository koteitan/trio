# -*- coding: utf-8 -*-
"""R89 見積もり その 2: CtxOK 装備チェック（W 所属の再帰）の実測時間。"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter

NS = (1, 2, 3); MAXDEPTH = 9; MAXLEN = 28
def lev(c): return 2 * c[1] + c[2]
def lift1(S, t):
    return [(c[0], c[1] + (t if trio.is_ancestor(S, 1, 0, i) else 0), c[2])
            for i, c in enumerate(S)]
def inW(S, a, depth, memo):
    S = tuple(tuple(c) for c in S); key = (S, a)
    if key in memo: return memo[key]
    if len(S) == 0: return True
    if len(S) == 1:
        r = lev(S[0]) <= a; memo[key] = r; return r
    if depth <= 0 or len(S) > MAXLEN: return None
    memo[key] = None
    out = True
    for n in NS:
        r = inW(trio.expand(list(S), n), a, depth - 1, memo)
        if r is False: memo[key] = False; return False
        if r is None: out = None
    memo[key] = out; return out

DS, BS, CS = (1, 2, 3), (0, 1, 2), (0, 1)
VS, ZS, TS = (0, 1, 2), (0, 1), (0, 1, 2)
COL = [(d, b, c) for d in DS for b in BS for c in CS]
memo = {}
res = Counter()
Ms = [list(m) for m in itertools.islice(itertools.product(COL, repeat=3), 300)]
t0 = time.time(); k = 0
for M in Ms:
    for v in VS:
        for z in ZS:
            st = 'eq'
            for kk in range(len(M)):
                for t in TS:
                    r = inW(lift1([(0, v, z)] + M[:kk], t), 2*(v+t)+z, MAXDEPTH, memo)
                    if r is False: st = 'NOT-eq'
                    elif r is None and st == 'eq': st = 'unknown'
            res[st] += 1; k += 1
dt = time.time() - t0
print(f'ctxOK check: {k} (M,v,z) in {dt:.2f}s -> {dt/k*1e3:.2f} ms each; memo={len(memo)}')
print(res)
print(f'  => |M|<=3 (5832+324+18=6174 contexts x 6 = 37044) ~ {37044*dt/k:.0f} s')
