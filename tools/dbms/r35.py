# -*- coding: utf-8 -*-
"""課題 R23: 三つ組を **`preimage_try`** で作り直す（母集団を引かない）。

    A ∈ ST_TS v<=5 len<=8、m = 1..MMAX
    T = (conv3 A)⟦m⟧、B = preimage_try(conv3, T, d2b3)
    B が取れたら三つ組。`|T| >= 20` の層が埋まるか。
    埋まらない (A, m) は **`ImgCofinalT` の破れの候補**（`cofinal.py` の hits と同じ形）。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7, inv3
from rows3 import b2d3, preimage_try
from core import expand
from collections import Counter

v, L = int(sys.argv[1]), int(sys.argv[2])
MMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 16
f = lambda X: [tuple(y) for y in b2d3(X)]


def d0bad(M):
    rows3._DMAP_TRACE = []
    b2d3(list(M))
    r = any(any(old[kk] <= dd for kk in range(k + 1, len(old)))
            for off, k, dd, old in rows3._DMAP_TRACE)
    rows3._DMAP_TRACE = None
    return r


P = [M for M in r7.stts_pool(v, L) if len(M) > 1]
print('A 側 ST_TS v<=%d len<=%d の |A|>1  **%d 個**  m = 1..%d'
      % (v, L, len(P), MMAX), flush=True)
c = Counter(); d = Counter(); tailmiss = []
t0 = time.time()
for i, A in enumerate(P):
    if i % 2000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        if i:
            print('   %d / %d  (%.0fs)' % (i, len(P), time.time() - t0), flush=True)
    fA = tuple(tuple(x) for x in b2d3(list(A)))
    aD0 = d0bad(A)
    hits = []
    for m in range(1, MMAX + 1):
        T = tuple(tuple(x) for x in expand(fA, m))
        if not T:
            hits.append('-')
            continue
        B = preimage_try(f, T, inv3.d2b3)
        if B is None:
            hits.append('.')
            c['_逆像なし'] += 1
            c['逆像なし |T|=%d' % len(T)] += 1
            continue
        hits.append('O')
        if m < 2:
            continue
        c['**三つ組**'] += 1
        c['**|T|>=20**' if len(T) >= 20 else '|T|<20'] += 1
        c["**A が (D0') を破る**" if aD0 else "A は (D0') を破らない"] += 1
        B = tuple(tuple(x) for x in B)
        for n in range(1, m):
            An = expand(A, n)
            if not An:
                continue
            An = tuple(tuple(x) for x in An)
            fAn = tuple(tuple(x) for x in b2d3(list(An)))
            d['_判定'] += 1
            if fAn == T:
                d['_(1) 前提'] += 1
                if An != B:
                    d['**(1) Inj3 の破れ**'] += 1
            if fAn < T:
                d['_(2) 前提'] += 1
                if not (An < B):
                    d['**(2) の破れ**'] += 1
            if T < fA:
                d['_(3) 前提'] += 1
                if not (B < A):
                    d['**(3) の破れ**'] += 1
            if not (fAn == T or fAn < T):
                d['**(S) SandwichUReindex の破れ**'] += 1
    s = ''.join(hits)
    if s.rstrip('-').endswith('.'):
        tailmiss.append((A, s))
print('  %.0fs' % (time.time() - t0))
print('== 三つ組の層別')
for k in sorted(c, key=str):
    if not k.startswith('_') and not k.startswith('逆像なし'):
        print('   %-32s %d' % (k, c[k]))
print('   逆像なしの (A,m): %d' % c['_逆像なし'])
for k in sorted(c, key=str):
    if k.startswith('逆像なし'):
        print('     %-28s %d' % (k, c[k]))
print('== 判定（%d 回）' % d['_判定'])
for k in sorted(d, key=str):
    if not k.startswith('_'):
        print('   %-40s %d' % (k, d[k]))
print('   前提の成立: (1) %d / (2) %d / (3) %d'
      % (d['_(1) 前提'], d['_(2) 前提'], d['_(3) 前提']))
print('== 末尾が外れ続ける A（ImgCofinalT の破れの候補）: **%d 個**' % len(tailmiss))
for A, s in tailmiss[:8]:
    print('   %s  %s' % (s, ''.join(str(x).replace(' ', '') for x in A)))
