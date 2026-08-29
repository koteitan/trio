# -*- coding: utf-8 -*-
"""**R100 —— R98 で残った 1 列族の塔を書き下す。**

R98: `TowerGraft2` が本当に要るのは **`|R| = 1` かつ `srow = 2` かつ 節 3** だけで、
その族は完全に書き下せる:

    `R = [(d, b, c)]`,  `d >= 1`（argOK）,  `c >= 1`（srow=2）,  `v < b`,  `z < c`

この族の塔 `T_n := ((0,v,z) :: R)⟦n⟧` を実際に計算して、閉じた形があるかを見る。
あれば L3 は `TowerGraft2` の一般形ではなく**この族だけ**を証明すればよい。

⚠ `trio.expand` は長さ 1 で `[]` を返すが Lean の `oper` は恒等（R98 の罠）。
  ここで扱うのは `(0,v,z) :: R` で長さ 2 以上なので問題ないが、`oper_lean` を使う。
⚠ 所属 `∈ W a` は R94 より**反証できない**。`ok` は健全（木が長さ <= 1 に落ち切った証拠）。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r98 import oper_lean
from r89 import inW


def lev(c):
    return 2 * c[1] + c[2]


print('### R100 残った 1 列族 `R = [(d,b,c)]`（`d>=1, c>=1, v<b, z<c`）の塔')
print()
print('## 1. 塔 `T_n = ((0,v,z) :: [(d,b,c)])⟦n⟧` の実際の形')
for (d, b, c, v, z) in ((1, 1, 1, 0, 0), (1, 2, 1, 0, 0), (2, 1, 1, 0, 0),
                        (1, 2, 2, 0, 1), (1, 3, 1, 1, 0)):
    X = [(0, v, z), (d, b, c)]
    print(f'  X = {X}   (d={d}, b={b}, c={c}, v={v}, z={z})')
    for n in range(1, 6):
        T = oper_lean(X, n)
        print(f'    ⟦{n}⟧ = {T}')
    print()

print('## 2. 予想の検算: `T_n` は行 0 が `0, d, 2d, …`、行 1 が `v, b, ...` の等差か')
bad = []
tot = Counter()
for d in range(1, 4):
    for b in range(1, 5):
        for c in range(1, 4):
            for v in range(0, b):            # v < b
                for z in range(0, min(c, 2)):  # z < c, z <= 1
                    X = [(0, v, z), (d, b, c)]
                    for n in range(1, 7):
                        T = oper_lean(X, n)
                        pred = [(k * d, v + k * (b - v), z) for k in range(n)]
                        tot['一致' if T == pred else '**不一致**'] += 1
                        if T != pred and len(bad) < 3:
                            bad.append((d, b, c, v, z, n, T, pred))
for k in sorted(tot):
    print(f'  {k:12s} {tot[k]:8d}')
for x in bad:
    print(f'  ex {x}')

print()
print('## 3. 所属（健全な判定器。`ok` のみ意味がある。R94 より反証は不可能）')
memo = {}
r = Counter()
for d in range(1, 4):
    for b in range(1, 5):
        for c in range(1, 4):
            for v in range(0, b):
                for z in range(0, min(c, 2)):
                    X = [(0, v, z), (d, b, c)]
                    a = 2 * v + z
                    x = inW(X, a, 10, memo, 30)
                    r['ok' if x is True else 'VIOL' if x is False else 'unknown'] += 1
for k in sorted(r):
    print(f'  {k:10s} {r[k]:8d}')
