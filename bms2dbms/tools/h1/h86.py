# -*- coding: utf-8 -*-
"""**(B): `h2` を「行 1 の錐の中の列だけ」に緩めたら通るか。**

§248 で `h2`（`L105Cap.lean:11588`）は消費側で偽と分かった。破れる列は
**`le1 Q 0 j` が偽の列（＝ブロッカーの向こう側）**だった。⟹ 錐の中に限れば通るか。

    (B1)  `h2B : ∀ j, 1 <= j → j < |Q| → 0 < entry Q 2 j → le1 Q 0 j
                  → hasParent (Q.take (j+1)) 2 j`
    (B2)  さらに `le1` を `Q.take (j+1)` の上で取った版（`le1_take` で同値のはず）
    (B0)  陰性対照: 錐の外の列で `hasParent` が成り立つ割合（`h2` が全部落ちるなら 0 に近いはず）

⚠ 母集団は `LiftTowerExp2`（`Wset.lean:4046`）から逐語。⚠ 箱を 2 通り（教訓 27）。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, srow, has_parent, dom_m, argOK, Lift1

ref = wref.Ref(maxnodes=4000)


def le1(S, a, b):
    return trio.is_ancestor(list(S), 1, a, b)


def h2B(Q):
    """(B1) 錐の中の列だけ（`1 <= j`）。"""
    return all(has_parent(Q[:j + 1], 2, j)
               for j in range(1, len(Q))
               if entry(Q, 2, j) > 0 and le1(Q, 0, j))


def h2B_take(Q):
    """(B2) `le1` も接頭辞の上で取る。"""
    return all(has_parent(Q[:j + 1], 2, j)
               for j in range(1, len(Q))
               if entry(Q, 2, j) > 0 and le1(Q[:j + 1], 0, j))


def run(cmax, lens, tmax=2, vmax=3):
    cols = [(d, b, c) for d in range(1, 3) for b in range(3) for c in range(cmax)]
    print('### 箱: 行2 < %d、`|R|` = %s、`v<%d`、`t<%d`' % (cmax, list(lens), vmax, tmax))
    print()
    print('| `|R|` | `z` | **分母** | **(B1) 成立** | (B1) 率 | (B2) 成立 | (B2) 率 |'
          ' 錐の外の列を持つ `Q` |')
    print('|--:|--:|--:|--:|--:|--:|--:|--:|')
    ex = []
    for L in lens:
        for z in (0, 1):
            den = b1 = b2 = out = 0
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
                        p, q = h2B(Q), h2B_take(Q)
                        b1 += p
                        b2 += q
                        if any(not le1(Q, 0, j) for j in range(1, len(Q))):
                            out += 1
                        if not p and len(ex) < 4:
                            bad = [j for j in range(1, len(Q))
                                   if entry(Q, 2, j) > 0 and le1(Q, 0, j)
                                   and not has_parent(Q[:j + 1], 2, j)]
                            ex.append((R, v, z, t, Q, bad))
            print('| %d | %d | **%d** | **%d** | **%.1f%%** | %d | %.1f%% | %d (%.1f%%) |'
                  % (L, z, den, b1, 100.0 * b1 / max(den, 1),
                     b2, 100.0 * b2 / max(den, 1),
                     out, 100.0 * out / max(den, 1)))
    print()
    if ex:
        print('**⛔ (B1) が破れる例（錐の中なのに行 2 の親が無い）:**')
        for R, v, z, t, Q, bad in ex:
            print('    R=`%s` v=%d z=%d t=%d Q=`%s`  破れる j = %s'
                  % (fmt(R), v, z, t, fmt(Q), bad))
    else:
        print('> **(B1) の反例ゼロ。⟹ 錐の中に限れば `h2` は成り立つ。**')
    print()


if __name__ == '__main__':
    print('## (B): `h2` を行 1 の錐の中に限ったら通るか')
    print()
    run(2, (2, 3, 4))
    run(3, (2, 3))
