# -*- coding: utf-8 -*-
"""**空虚検査: `snocStep_outOfCone` の前提は実際の場面で満たされるか。**

§254 で `snocStep_outOfCone` を緑にしたが、前提に **`hd1pos : 0 < e`** がある
（`le1_mTower_in_block` が要求）。⟹ **`e = 0` の塔では使えない。**
実際の場面で `e > 0` がどれだけ成り立つかを測らないと、緑でも空虚になりうる。

母集団は h88 と同じ（`LiftTowerExp2` ＋ 錐の外の 行 2 正の列）。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, srow, has_parent, dom_m, argOK, Lift1, shiftr01
from h88 import mTower, le1
from collections import Counter

ref = wref.Ref(maxnodes=4000)


def run(cmax, lens, tmax=2, vmax=3):
    cols = [(a, b, c) for a in range(1, 3) for b in range(3) for c in range(cmax)]
    print('### 箱: 行2 < %d、`v<%d`、`t<%d`、`z = 0`' % (cmax, vmax, tmax))
    print()
    print('| `|R|` | **分母（錐の外の行2正の列を持つ `Q`）** | **`0 < e`** | 割合 |'
          ' `0 < d` | 両方 |')
    print('|--:|--:|--:|--:|--:|--:|')
    for L in lens:
        den = epos = dpos = both = 0
        for R in itertools.product(cols, repeat=L):
            R = list(R)
            if not argOK(R) or dom_m(R) is None:
                continue
            if srow(R, len(R) - 1) != 2:
                continue
            z = 0
            for v in range(vmax):
                if not has_parent([(0, v, z)] + R, 2, len(R)):
                    continue
                for t in range(tmax):
                    M = Lift1([(0, v, z)] + R, t)
                    Q = M[:-1]
                    if ref.inW(Q, 2 * (v + t) + z) is not True:
                        continue
                    d = entry(M, 0, len(M) - 1) - entry(M, 0, 0)
                    e = entry(M, 1, len(M) - 1) - entry(M, 1, 0)
                    bad = [j for j in range(1, len(Q))
                           if entry(Q, 2, j) > 0 and not le1(Q, 0, j)]
                    if not bad:
                        continue
                    den += 1
                    if e > 0:
                        epos += 1
                    if d > 0:
                        dpos += 1
                    if e > 0 and d > 0:
                        both += 1
        print('| %d | **%d** | **%d** | **%.1f%%** | %d (%.1f%%) | %d (%.1f%%) |'
              % (L, den, epos, 100.0 * epos / max(den, 1),
                 dpos, 100.0 * dpos / max(den, 1),
                 both, 100.0 * both / max(den, 1)))
    print()


if __name__ == '__main__':
    print('## 空虚検査: `0 < e` は実際の場面でどれだけ成り立つか')
    print()
    run(2, (2, 3, 4))
