# -*- coding: utf-8 -*-
"""課題 R19: 三つ組 `(A, m, B)` を**難しさ**で層別する。

`(conv3 A)⟦m⟧ = conv3 B` なる三つ組は稀ではない（チームリードの 149995 組）。
問題は **どの層に母数があるか**。とくに

    `T = (conv3 A)⟦m⟧` の長さ >= 20 の層
    `A` が `SandwichUT3` / (D0') を破る側にいる層

が空なら、「破れ 0」は易しい領域だけを見ていることになる。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3
from core import expand
from collections import Counter

vA, LA = int(sys.argv[1]), int(sys.argv[2])
vB, LB = int(sys.argv[3]), int(sys.argv[4])
MMAX = int(sys.argv[5]) if len(sys.argv) > 5 else 6


def enc(M):
    return bytes(x for c in M for x in c)


def d0bad(M):
    rows3._DMAP_TRACE = []
    b2d3(list(M))
    r = any(any(old[kk] <= dd for kk in range(k + 1, len(old)))
            for off, k, dd, old in rows3._DMAP_TRACE)
    rows3._DMAP_TRACE = None
    return r


t0 = time.time()
QB = r7.stts_pool(vB, LB)
IMG = {}
for i, M in enumerate(QB):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    IMG[enc(b2d3(list(M)))] = M
print('B 側 ST_TS v<=%d len<=%d  %d 個 -> 像の表 %d 件  (%.0fs)'
      % (vB, LB, len(QB), len(IMG), time.time() - t0), flush=True)
del QB

QA = [M for M in r7.stts_pool(vA, LA) if len(M) > 1]
print('A 側 ST_TS v<=%d len<=%d の |A|>1  %d 個' % (vA, LA, len(QA)), flush=True)

c = Counter(); d = Counter()
t0 = time.time()
for i, A in enumerate(QA):
    if i % 5000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    fA = tuple(tuple(x) for x in b2d3(list(A)))
    aD0 = d0bad(A)
    # A が SandwichUT3 を破るか（n = 1..3）
    aSW = False
    for n in (1, 2, 3):
        An = expand(A, n)
        if not An:
            continue
        if tuple(tuple(x) for x in b2d3(list(An))) > tuple(tuple(x) for x in expand(fA, n + 1)):
            aSW = True
    for m in range(2, MMAX + 1):
        T = tuple(tuple(x) for x in expand(fA, m))
        if not T:
            break
        B = IMG.get(enc(T))
        if B is None:
            c['_逆像が表に無い'] += 1
            c['表に無い: |T|=%d' % len(T)] += 1
            continue
        c['**三つ組**'] += 1
        c['|A|=%d' % len(A)] += 1
        c['m=%d' % m] += 1
        c['|T|=%d' % len(T)] += 1
        c['**|T|>=20**' if len(T) >= 20 else '|T|<20'] += 1
        c['**A が (D0\') を破る**' if aD0 else "A は (D0') を破らない"] += 1
        c['**A が SandwichUT3 を破る**' if aSW else 'A は SandwichUT3 を破らない'] += 1
        # 4 本の判定
        for n in range(1, m):
            An = expand(A, n)
            if not An:
                continue
            An = tuple(tuple(x) for x in An)
            fAn = tuple(tuple(x) for x in b2d3(list(An)))
            d['_判定'] += 1
            if fAn == T and An != B:
                d['**(1) Inj3 の破れ**'] += 1
            if fAn < T and not (An < B):
                d['**(2) の破れ**'] += 1
            if T < fA and not (B < A):
                d['**(3) の破れ**'] += 1
            if not (fAn == T or fAn < T):
                d['**(S) SandwichUReindex の破れ**'] += 1
            if not (fAn == fA or fAn < fA):
                d['陽性対照（B := A に取り替える）の破れ'] += 1
print('  %.0fs' % (time.time() - t0))
print('== 三つ組の層別')
for k in sorted(c, key=str):
    if not k.startswith('_'):
        print('   %-36s %d' % (k, c[k]))
print('   （逆像が表に無かった T: %d）' % c['_逆像が表に無い'])
print('== 判定（%d 回）' % d['_判定'])
for k in sorted(d, key=str):
    if not k.startswith('_'):
        print('   %-40s %d' % (k, d[k]))
