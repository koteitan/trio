# -*- coding: utf-8 -*-
"""課題 R18 (1): `OrderReindexT3` / `SandwichUReindexT3` / `Inj3` を**述語として**測る。

三つ組 `(A, m, B)` で `(conv3 A)⟦m⟧ = conv3 B` なるもの。
**`B` は母集団に居なくてよい** —— `rows3.preimage_try`（`inv3.d2b3` ＋ 双子戻し
＋ 接頭辞の試行、当たりは `conv3 B == T` で検算）で作る。

    (1) conv3 (A⟦n⟧) = conv3 B          ならば A⟦n⟧ = B        （Inj3 の枝）
    (2) seqlex (conv3 (A⟦n⟧)) (conv3 B) ならば seqlex (A⟦n⟧) B
    (3) seqlex (conv3 B) (conv3 A)      ならば seqlex B A
    (S) sle3 (conv3 (A⟦n⟧)) (conv3 B)                          （SandwichUReindex）
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7, inv3
from rows3 import b2d3, preimage_try
from core import expand
from collections import Counter

v, L = int(sys.argv[1]), int(sys.argv[2])
MMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 6
COUNT = len(sys.argv) > 4 and sys.argv[4] == 'count'

P = [M for M in r7.stts_pool(v, L) if len(M) > 1]
print('母集団 ST_TS v<=%d len<=%d の |A|>1  **%d 個**  m = 2..%d'
      % (v, L, len(P), MMAX), flush=True)
c = Counter(); trip = []
t0 = time.time()
for i, A in enumerate(P):
    if i % 2000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    fA = tuple(tuple(x) for x in b2d3(list(A)))
    for m in range(2, MMAX + 1):
        T = tuple(tuple(x) for x in expand(fA, m))
        if not T:
            break
        c['_T を試した'] += 1
        B = preimage_try(lambda X: [tuple(y) for y in b2d3(X)], T, inv3.d2b3)
        if B is None:
            c['逆像が作れない'] += 1
            continue
        c['**三つ組 (A,m,B) が取れた**'] += 1
        trip.append((A, m, B, fA, T))
print('  三つ組を数えた %.0fs' % (time.time() - t0), flush=True)
for k in sorted(c, key=str):
    if not k.startswith('_'):
        print('   %-36s %d' % (k, c[k]))
print('   （`T` を試した回数 %d）' % c['_T を試した'])
if COUNT or not trip:
    sys.exit(0)

d = Counter()
for A, m, B, fA, T in trip:
    fB = T
    for n in range(1, m):
        An = tuple(tuple(x) for x in expand(A, n))
        if not An:
            continue
        fAn = tuple(tuple(x) for x in b2d3(list(An)))
        d['_判定'] += 1
        if fAn == fB and An != B:
            d['**(1) Inj3 の破れ**'] += 1
        if fAn < fB and not (An < B):
            d['**(2) の破れ**'] += 1
        if fB < fA and not (B < A):
            d['**(3) の破れ**'] += 1
        if not (fAn == fB or fAn < fB):
            d['**(S) SandwichUReindex の破れ**'] += 1
        # 陽性対照: B を「三つ組でないもの」に取り替える（A 自身）
        if not (fAn == fA or fAn < fA):
            d['陽性対照（B := A）の破れ'] += 1
print()
for k in sorted(d, key=str):
    if not k.startswith('_'):
        print('   %-40s %d' % (k, d[k]))
print('   （判定 %d 回）' % d['_判定'])
