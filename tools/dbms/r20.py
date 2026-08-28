# -*- coding: utf-8 -*-
"""課題 R12: `SandwichUT3` を **直接** 測る（5 分解を経由しない）。

    SandwichUT3 := ∀ A ∈ ST_TS, |A| > 1, ∀ n >= 1,
                     sle3 (conv3 (A⟦n⟧)) ((conv3 A)⟦n+1⟧)
    sle3 M N := (M = N) ∨ seqlex M N     （seqlex = Python のタプル順序）
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3
from core import expand
from collections import Counter

v, L, NMAX = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
P = r7.stts_pool(v, L)
P = [M for M in P if len(M) > 1]
print('母集団 ST_TS v<=%d len<=%d の |A|>1  **%d 個**  n = 1..%d'
      % (v, L, len(P), NMAX), flush=True)
c = Counter(); ex = []
t0 = time.time()
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
        c['_判定'] += 1
        if lhs == rhs:
            c['等号'] += 1
        elif lhs < rhs:
            c['真に小さい'] += 1
        else:
            c['**破れ**'] += 1
            c['破れ n=%d' % n] += 1
            if len(ex) < 4:
                ex.append((A, n, lhs, rhs))
        # 陽性対照: 右辺を (conv3 A)⟦n⟧ に（1 少なく）
        rhs0 = tuple(tuple(x) for x in expand(fA, n))
        if not (lhs == rhs0 or lhs < rhs0):
            c['陽性対照（右辺を n に）の破れ'] += 1
print('判定 %d 回  %.0fs' % (c['_判定'], time.time() - t0))
for k in sorted(c, key=str):
    if not k.startswith('_'):
        print('   %-30s %d' % (k, c[k]))
for A, n, lhs, rhs in ex:
    print('   ### 破れ n=%d' % n)
    print('      A   = %s' % ''.join(str(x).replace(' ', '') for x in A))
    print('      左 = conv3(A⟦%d⟧) = %s' % (n, ''.join(str(x).replace(' ', '') for x in lhs)))
    print('      右 = (conv3 A)⟦%d⟧ = %s' % (n + 1, ''.join(str(x).replace(' ', '') for x in rhs)))
