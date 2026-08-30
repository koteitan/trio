# -*- coding: utf-8 -*-
"""課題 R19 の続き: **B 側を `len<=12` に広げて難しい層を埋める**。

像の表は `bytes -> なし`（存在だけ）にしてメモリを抑える。
`ST_TS v<=5 len<=12` の 19325912 個の像を集合にすると `|T| <= 24` 程度まで届く。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, trio
from rows3 import b2d3
from core import expand
from collections import Counter, deque

vA, LA, vB, LB = (int(sys.argv[1]), int(sys.argv[2]),
                  int(sys.argv[3]), int(sys.argv[4]))
MMAX = int(sys.argv[5]) if len(sys.argv) > 5 else 6


def enc(M):
    return bytes(x for c in M for x in c)


def pool_bytes(v, L):
    seen = set(); fr = deque()
    for k in range(v + 1):
        D = tuple(tuple(c) for c in trio.diag(3, k, zcap=1))
        if enc(D) not in seen:
            seen.add(enc(D)); fr.append(D)
    while fr:
        S = fr.popleft()
        for n in (1, 2, 3):
            T = tuple(tuple(c) for c in trio.expand(list(S), n))
            if T and len(T) <= L and enc(T) not in seen:
                seen.add(enc(T)); fr.append(T)
    return seen


t0 = time.time()
SB = pool_bytes(vB, LB)
print('B 側 ST_TS v<=%d len<=%d  %d 個 (%.0fs)' % (vB, LB, len(SB), time.time() - t0),
      flush=True)
t0 = time.time()
IMG = set(); mx = 0
for i, e in enumerate(SB):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    M = tuple((e[j], e[j + 1], e[j + 2]) for j in range(0, len(e), 3))
    im = b2d3(list(M))
    IMG.add(bytes(x for c in im for x in c))
    mx = max(mx, len(im))
del SB
print('  像の集合 %d 件（最大の長さ %d）(%.0fs)' % (len(IMG), mx, time.time() - t0),
      flush=True)

SA = pool_bytes(vA, LA)
QA = [tuple((e[j], e[j + 1], e[j + 2]) for j in range(0, len(e), 3)) for e in SA]
QA = [M for M in QA if len(M) > 1]
del SA
print('A 側 %d 個' % len(QA), flush=True)


def d0bad(M):
    rows3._DMAP_TRACE = []
    b2d3(list(M))
    r = any(any(old[kk] <= dd for kk in range(k + 1, len(old)))
            for off, k, dd, old in rows3._DMAP_TRACE)
    rows3._DMAP_TRACE = None
    return r


c = Counter()
t0 = time.time()
for i, A in enumerate(QA):
    if i % 5000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    fA = tuple(tuple(x) for x in b2d3(list(A)))
    aD0 = d0bad(A)
    for m in range(2, MMAX + 1):
        T = tuple(tuple(x) for x in expand(fA, m))
        if not T:
            break
        if bytes(x for cc in T for x in cc) not in IMG:
            c['表に無い |T|=%d' % len(T)] += 1
            continue
        c['**三つ組**'] += 1
        c['**|T|>=20**' if len(T) >= 20 else '|T|<20'] += 1
        c["**A が (D0') を破る**" if aD0 else "A は (D0') を破らない"] += 1
        c['|T|=%d' % len(T)] += 1
print('  %.0fs' % (time.time() - t0))
for k in sorted(c, key=str):
    if not k.startswith('表に無い'):
        print('   %-32s %d' % (k, c[k]))
print('  （表に無かった T の合計 %d）'
      % sum(v for k, v in c.items() if k.startswith('表に無い')))
