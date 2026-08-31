# -*- coding: utf-8 -*-
"""**残核の実際の大きさ: 消費側の `Q` に「錐の外の 行 2 正の列」がどれだけ出るか。**

§249 で `h2` ⟺ 「`z=0`」＋「行 2 が正の列は全部 行 1 の錐の中」と分かった。
⟹ `z = 0` では **`¬h2` ⟺ 「錐の外の 行 2 正の列がある」** ＝ **残核そのもの**。

    (r1) 残核の割合を `|R|` を伸ばして追う（教訓 21）
    (r2) 破れる列は**末尾**か**内側**か（`hstep` は 1 列ずつ足すので効く）
    (r3) 破れる列は**行 2 の孤児**か（`oper = Pred` に落ちるか）
    (r4) 箱を 2 通り（教訓 27）

⚠ 母集団は `LiftTowerExp2`（`Wset.lean:4046`）から逐語。⚠ 分母を必ず（教訓 23）。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, srow, has_parent, dom_m, argOK, Lift1
from collections import Counter

ref = wref.Ref(maxnodes=4000)


def le1(S, a, b):
    return trio.is_ancestor(list(S), 1, a, b)


def run(cmax, lens, tmax=2, vmax=3):
    cols = [(d, b, c) for d in range(1, 3) for b in range(3) for c in range(cmax)]
    print('### 箱: 行2 < %d、`v<%d`、`t<%d`、`z = 0`' % (cmax, vmax, tmax))
    print()
    print('| `|R|` | **分母** | **残核（錐の外の行2正の列あり）** | 割合 |'
          ' (r2) 破れる列が末尾のみ | (r3) その列は行2の孤児 |')
    print('|--:|--:|--:|--:|--:|--:|')
    for L in lens:
        z = 0
        den = res = last = orph = 0
        for R in itertools.product(cols, repeat=L):
            R = list(R)
            if not argOK(R) or dom_m(R) is None:
                continue
            if srow(R, len(R) - 1) != 2:
                continue
            for v in range(vmax):
                if not has_parent([(0, v, z)] + R, 2, len(R)):
                    continue
                for t in range(tmax):
                    Q = Lift1([(0, v, z)] + R[:-1], t)
                    if ref.inW(Q, 2 * (v + t) + z) is not True:
                        continue
                    den += 1
                    bad = [j for j in range(1, len(Q))
                           if entry(Q, 2, j) > 0 and not le1(Q, 0, j)]
                    if not bad:
                        continue
                    res += 1
                    if bad == [len(Q) - 1]:
                        last += 1
                    if all(not has_parent(Q[:j + 1], 2, j) for j in bad):
                        orph += 1
        print('| %d | **%d** | **%d** | **%.1f%%** | %d (%.1f%%) | %d (%.1f%%) |'
              % (L, den, res, 100.0 * res / max(den, 1),
                 last, 100.0 * last / max(res, 1),
                 orph, 100.0 * orph / max(res, 1)))
    print()


if __name__ == '__main__':
    print('## 残核の実際の大きさ（`z = 0`。`¬h2` ⟺ 残核）')
    print()
    run(2, (2, 3, 4, 5))
    run(3, (2, 3, 4))
