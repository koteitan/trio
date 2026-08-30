# -*- coding: utf-8 -*-
"""課題 R41: **`WCat` の残り 36% は文字どおり `graft` の形か。**

    graft M z = M.dropLast ++ z.map (p => (p.1 + entry M 0 (|M|-1), p.2.1, p.2.2))

`graft A z = A ++ B` を要求すると、リストの等式から

    A.dropLast ++ lift(z) = A ++ B
    ⟹ **lift(z) = [A[-1]] ++ B**
    ⟹ z = ([A[-1]] ++ B) の行 0 を A[-1].1 だけ下げたもの

    `based z`（z[0].1 = 0）は**自動**（A[-1].1 - A[-1].1 = 0）
    しかし節 3 は `z ∈ W m`（m = lev A (|A|-1) - 1）を要求し、
    **lev z 0 = lev A[-1] = m + 1 > m**
    ⟹ `lev_root_le_of_mem_W` により **z ∈ W m は不可能**

これを実際に確かめる（(i)）。あわせて **`A ++ B` 自身に節 3 が使えるか**（(ii)）も測る。
"""
import sys, random
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from r60 import why2, lev0, wadd_ok
from r61 import cat_direct, cat_split
from r49 import has_parent


def lv(p):
    return 2 * p[1] + p[2]


CAP = int(sys.argv[1]); PAIRS = int(sys.argv[2])
rng = random.Random(20260829)
COLS = [(a, b, c) for a in range(6) for b in range(6) for c in range(2)]
P = set()
while len(P) < CAP:
    P.add(tuple(rng.choice(COLS) for _ in range(rng.randint(1, 5))))
OK = [M for M in P if why2(M) is not None]
c = Counter(); n = 0
while n < PAIRS:
    A = rng.choice(OK); B = rng.choice(OK)
    if A == B or lev0(B) > lev0(A):
        continue
    n += 1
    if cat_direct(A, B) or cat_split(A, B):
        continue
    T = A + B
    # ---- (i) `A ++ B = graft A z` は可能か
    if len(A) >= 2 and not has_parent(A, len(A) - 1):
        c['(i) A の末尾列は孤児（domT の前提 OK）'] += 1
        d0 = A[-1][0]
        Z = [A[-1]] + list(B)
        if all(p[0] >= d0 for p in Z):
            z = tuple((p[0] - d0, p[1], p[2]) for p in Z)
            m = lv(A[-1]) - 1
            c['  z は based（自動）' if z[0][0] == 0 else '  **z が based でない**'] += 1
            c['  **z ∈ W m が不可能（lev z 0 = m+1 > m）**'
              if lv(z[0]) > m else '  z ∈ W m が可能かもしれない'] += 1
        else:
            c['  持ち上げが負になる（z が作れない）'] += 1
    else:
        c['(i) A の末尾列が親を持つ ⟹ **domT が偽。節 3 は最初から使えない**'] += 1
    # ---- (ii) `A ++ B` 自身に節 3 が使えるか
    j = len(T) - 1
    if lv(T[j]) >= 1 and not has_parent(T, j):
        c['(ii) **A++B 自身に節 3 が使える（末尾が孤児）**'] += 1
        c['   かつ m < lev(A++B) 0' if lv(T[j]) - 1 < lev0(T)
          else '   だが m >= lev(A++B) 0 ⟹ 使えない'] += 1
    else:
        c['(ii) A++B の末尾は親を持つか lev 0 ⟹ 節 3 は使えない'] += 1
print('== 届かない事例（A != B、%d 組から）で `graft` が使えるか' % PAIRS)
for k in sorted(c, key=str):
    print('   %-52s %d' % (k, c[k]))
