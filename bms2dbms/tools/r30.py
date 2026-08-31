# -*- coding: utf-8 -*-
"""R16 の裏取り: 反例 12 件の `T = (conv3 A)⟦m⟧` が **ST_TS の像の集合**に入るか。

`inv3.d2b3` は発見的な逆写像なので「作れない」だけでは弱い。
`ST_TS v<=5 len<=L2` の像を全部集合にして、`T` がその中にあるかを直に見る。
入っていなければ **その長さまでの ST_TS には B が居ない**（確定）。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3
from core import expand

v, L, NMAX = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
V2, L2 = int(sys.argv[4]), int(sys.argv[5])
MMAX = int(sys.argv[6]) if len(sys.argv) > 6 else 8

P = [M for M in r7.stts_pool(v, L) if len(M) > 1]
bad = []
for i, A in enumerate(P):
    if i % 5000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    fA = tuple(tuple(x) for x in b2d3(list(A)))
    for n in range(1, NMAX + 1):
        An = expand(A, n)
        if not An:
            continue
        lhs = tuple(tuple(x) for x in b2d3(list(An)))
        rhs = tuple(tuple(x) for x in expand(fA, n + 1))
        if lhs > rhs:
            bad.append((A, n, fA, lhs))
print('反例 **%d 件**' % len(bad), flush=True)

need = {}
for A, n, fA, lhs in bad:
    for m in range(n + 1, MMAX + 1):
        T = tuple(tuple(x) for x in expand(fA, m))
        if not T:
            break
        # sle3 が破れるものだけが問題
        if not (lhs == T or lhs < T):
            need.setdefault(T, []).append((A, n, m))
print('  検算が要る T（sle3 が破れる側）: **%d 個**  長さ %s'
      % (len(need), sorted(set(len(t) for t in need))), flush=True)

t0 = time.time()
Q = r7.stts_pool(V2, L2)
print('  照合用の母集団 ST_TS v<=%d len<=%d  %d 個 (%.0fs)'
      % (V2, L2, len(Q), time.time() - t0), flush=True)
t0 = time.time()
hit = 0
IMG = set()
for i, M in enumerate(Q):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    IMG.add(bytes(x for c in b2d3(list(M)) for x in c))
print('  像の集合を作った (%.0fs)' % (time.time() - t0), flush=True)
for T in need:
    if bytes(x for c in T for x in c) in IMG:
        hit += 1
print()
print('  **像の集合に入る T: %d / %d**' % (hit, len(need)))
print('  ⟹ 入らなければ、その長さまでの ST_TS に B は居ない（確定）')
mx = max(len(t) for t in need) if need else 0
print('  T の最大の長さ %d、照合用の像の最大の長さ %d'
      % (mx, max((len(b) // 3 for b in IMG), default=0)))
