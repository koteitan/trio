# -*- coding: utf-8 -*-
"""(D0') の**十分性**: 違反 90 件のそれぞれに、順序を破る相方が作れるか。

違反の署名は `(k=2, dd=3, 段=(3,))` の 1 種類。違反した offset を `off` として
`P = M[:off]`、`c1 = M[off]` とし、**`c1` より大きい合法な次の柱 `c2`** を全部試して
`M2 = P ++ (c2,) ++ 継続` を作り、`M < M2` なのに `f(M) > f(M2)` になるかを見る。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3
from core import isstd
from collections import Counter

v, L = int(sys.argv[1]), int(sys.argv[2])
K = int(sys.argv[3]) if len(sys.argv) > 3 else 1


def d0(M):
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


def conts(P, k):
    out = [P]; cur = [P]
    for _ in range(k):
        nxt = [S + (x,) for S in cur for x in legal_next(S)]
        out += nxt; cur = nxt
    return out


P0 = r7.stts_pool(v, L)
print('母集団 %d 個' % len(P0), flush=True)
V = []
for i, M in enumerate(P0):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    o = d0(M)
    if o:
        V.append((M, o[0]))
print('(D0\') 違反を持つ行列 **%d**' % len(V), flush=True)
del P0
c = Counter(); ex = []
t0 = time.time()
for M, off in V:
    fM = tuple(tuple(x) for x in b2d3(list(M)))
    P = tuple(M[:off]); c1 = M[off]
    found = None
    for c2 in legal_next(P):
        if c2 <= c1:
            continue
        for T in conts(P + (c2,), K):
            if T <= M:
                continue
            fT = tuple(tuple(x) for x in b2d3(list(T)))
            if fM > fT:
                found = (c2, T, fT)
                break
        if found:
            break
    if found:
        c['**相方が作れる（本当に破れる）**'] += 1
        if len(ex) < 3:
            ex.append((M, off, found))
    else:
        c['相方が作れない（K=%d の範囲で無害）' % K] += 1
print('  %.0fs' % (time.time() - t0))
for k in sorted(c, key=str):
    print('   %-46s %d' % (k, c[k]))
for M, off, (c2, T, fT) in ex:
    print('   ### 相方が作れた例  off=%d  c1=%s -> c2=%s' % (off, M[off], c2))
    print('      M  = %s' % ''.join(str(x).replace(' ', '') for x in M))
    print('      M2 = %s' % ''.join(str(x).replace(' ', '') for x in T))
