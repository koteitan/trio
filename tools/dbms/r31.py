# -*- coding: utf-8 -*-
"""課題 R18 (3): **(D0') 違反 90 site** が `OrderReindexT3` の相手の形になりうるか。

順序の破れ (X, Y)（入力 X < Y、像 f X > f Y）が Lean を壊すのは

    (ii)  ∃ A ∈ ST_TS, n>=1, m>=n+1 :  A⟦n⟧ = Y  かつ  (conv3 A)⟦m⟧ = conv3 X
    (iii) ∃ m>=2                     :  (conv3 X)⟦m⟧ = conv3 Y

24 件については 0/24 だった（チームリード）。**90 site 全部**に当てる。
`B`（＝ 逆像）は母集団に居なくてよいよう `rows3.preimage_try` で作る。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7, inv3
from rows3 import b2d3, preimage_try
from core import expand, isstd
from collections import Counter

v, L = int(sys.argv[1]), int(sys.argv[2])
MMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 6


def d0off(M):
    rows3._DMAP_TRACE = []
    b2d3(list(M))
    out = []
    for off, k, dd, old in rows3._DMAP_TRACE:
        if any(old[kk] <= dd for kk in range(k + 1, len(old))):
            out.append(off)
    rows3._DMAP_TRACE = None
    return out


def legal_next(P, zcap=1):
    amax = P[-1][0] + 1
    return sorted((a, b, cz) for a in range(amax + 1) for b in range(a + 1)
                  for cz in range(min(b, zcap) + 1)
                  if isstd(P + ((a, b, cz),), 'BMS'))


P0 = r7.stts_pool(v, L)
print('母集団 %d 個' % len(P0), flush=True)
V = []
for i, M in enumerate(P0):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    o = d0off(M)
    if o:
        V.append((M, o[0]))
print('(D0\') 違反 site **%d**' % len(V), flush=True)

# --- 各 site から破れの対 (X, Y) を作る（X < Y、f X > f Y）
pairs = []
for M, off in V:
    fM = tuple(tuple(x) for x in b2d3(list(M)))
    Pfx = tuple(M[:off]); c1 = M[off]
    for c2 in legal_next(Pfx):
        if c2 <= c1:
            continue
        T = Pfx + (c2,)
        if T <= M:
            continue
        fT = tuple(tuple(x) for x in b2d3(list(T)))
        if fM > fT:
            pairs.append((M, T, fM, fT))
            break
print('破れの対 **%d 組**' % len(pairs), flush=True)

# --- A⟦n⟧ = Y の逆引き表（母集団から）
pre = {}
for A in P0:
    for n in (1, 2, 3):
        E = tuple(tuple(x) for x in expand(A, n))
        if E:
            pre.setdefault(E, []).append((A, n))
del P0
print('逆引き表 %d 件' % len(pre), flush=True)

c = Counter(); ex = []
for X, Y, fX, fY in pairs:
    hit = None
    # (iii) ∃ m>=2 : (conv3 X)⟦m⟧ = conv3 Y
    for m in range(2, MMAX + 1):
        if tuple(tuple(x) for x in expand(fX, m)) == fY:
            hit = ('iii', m); break
    # (ii) ∃A,n,m : A⟦n⟧ = Y かつ (conv3 A)⟦m⟧ = conv3 X
    if not hit:
        for A, n in pre.get(Y, []):
            fA = tuple(tuple(x) for x in b2d3(list(A)))
            for m in range(n + 1, MMAX + 1):
                if tuple(tuple(x) for x in expand(fA, m)) == fX:
                    hit = ('ii', (A, n, m)); break
            if hit:
                break
    if hit:
        c['**当たる %s**' % hit[0]] += 1
        if len(ex) < 3:
            ex.append((X, Y, hit))
    else:
        c['当たらない'] += 1
    # 陽性対照: (iii) の判定を m=1（＝ 恒等）に緩めると当たるか
    if tuple(tuple(x) for x in expand(fX, 1)) == fY:
        c['陽性対照 m=1 で当たる'] += 1
print()
for k in sorted(c, key=str):
    print('   %-40s %d' % (k, c[k]))
for X, Y, hit in ex:
    print('   ### 当たった  %s' % str(hit))
    print('      X = %s' % ''.join(str(x).replace(' ', '') for x in X))
    print('      Y = %s' % ''.join(str(x).replace(' ', '') for x in Y))
