# -*- coding: utf-8 -*-
"""課題 R16: `SandwichUT3` の反例 12 件は `SandwichUReindexT3` に当たるか。

    SandwichUReindexT3 :=
      ∀ A B n m, ST_TS A → 1<|A| → ST_TS B → 1<=n → n+1<=m →
        (conv3 A)⟦m⟧ = conv3 B → sle3 (conv3 (A⟦n⟧)) (conv3 B)

反例 `(A, n)`（`conv3 (A⟦n⟧) > (conv3 A)⟦n+1⟧`）が当たるのは

    ∃ m >= n+1, ∃ B :  (conv3 A)⟦m⟧ = conv3 B  かつ  sle3 が破れる

とき。母集団の長さで切らずに済むよう、**逆写像 `inv3.d2b3` で `B` を作って
`conv3 B == T` を検算する**（`B` が作れなければその `m` では当たらない）。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7, inv3
from rows3 import b2d3
from core import expand, isstd
from collections import Counter

v, L, NMAX = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
MMAX = int(sys.argv[4]) if len(sys.argv) > 4 else 8

P = [M for M in r7.stts_pool(v, L) if len(M) > 1]
print('母集団 ST_TS v<=%d len<=%d の |A|>1  %d 個' % (v, L, len(P)), flush=True)

# --- SandwichUT3 の反例を集める
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
print('`SandwichUT3` の反例 **%d 件**' % len(bad), flush=True)

c = Counter(); ex = []
for A, n, fA, lhs in bad:
    hit = None
    for m in range(n + 1, MMAX + 1):
        T = tuple(tuple(x) for x in expand(fA, m))
        if not T:
            break
        try:
            B = inv3.d2b3(list(T))
        except Exception:
            B = None
        if not B:
            continue
        B = tuple(tuple(x) for x in B)
        if not isstd(B, 'BMS'):
            continue
        if tuple(tuple(x) for x in b2d3(list(B))) != T:
            continue
        # B が実在した。sle3 が破れるか
        fB = T
        if not (lhs == fB or lhs < fB):
            hit = (m, B)
            break
        c['m=%d で B は在るが sle3 は成り立つ' % m] += 1
    if hit:
        c['**当たる（B が実在して sle3 が破れる）**'] += 1
        ex.append((A, n, hit))
    else:
        c['当たらない（そういう B が無い）'] += 1
print()
for k in sorted(c, key=str):
    print('   %-46s %d' % (k, c[k]))
for A, n, (m, B) in ex[:4]:
    print('   ### 当たった例  n=%d m=%d' % (n, m))
    print('      A = %s' % ''.join(str(x).replace(' ', '') for x in A))
    print('      B = %s' % ''.join(str(x).replace(' ', '') for x in B))
