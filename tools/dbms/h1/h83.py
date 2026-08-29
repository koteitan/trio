# -*- coding: utf-8 -*-
"""**課題 (k2)(k3): `L105Cap.lean:11588` の `h2` は消費側の `Q` で成り立つか。**

⚠ **前提は `file:line` から逐語で写した**（教訓 25）:

    `L105Cap.lean:11588`
      `h2 : ∀ j, j < Q.length → 0 < entry Q 2 j → hasParent (Q.take (j+1)) 2 j`

    消費側（`L105Cap.lean:5666` `hQmem` / `:5686` `htow`）:
      `Q = Lift1 ((0,v,z) :: R.dropLast) t`   （`t` は自由変数、`z <= 1`）

`j = 0` では結論が常に偽（`L53.not_hasParent_zero`、`L53Subst.lean:3308`）なので
**`h2` は `entry Q 2 0 = 0`、すなわち `z = 0` を強制する**（`lean/H12H2.lean` で緑）。

⟹ 残る問いは **弱めた版 `h2'`（`1 <= j` に限る）なら通るか**。それを測る。

    (k3) `z = 1` の具体的な反例（前提を全部満たすもの）
    (A)  `h2'` ＝ `∀ j, 1 <= j → …` の成立率（分母つき）
    (A2) `h2'` が破れる例
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, srow, has_parent, dom_m, Lift1
from collections import Counter


def h2_full(Q):
    """`L105Cap.lean:11588` そのまま（`j = 0` を含む）。"""
    return all(has_parent(Q[:j + 1], 2, j)
               for j in range(len(Q)) if entry(Q, 2, j) > 0)


def h2_prime(Q):
    """弱めた版 (A): `1 <= j` に限る。"""
    return all(has_parent(Q[:j + 1], 2, j)
               for j in range(1, len(Q)) if entry(Q, 2, j) > 0)


def main(lens=(2, 3, 4), tmax=3):
    cols = [(d, b, c) for d in range(1, 3) for b in range(3) for c in range(2)]
    print('## (k2)(k3): `h2`（`L105Cap.lean:11588`）は消費側の `Q` で成り立つか')
    print()
    print('列 = 行0∈[1,2]・行1<3・行2<2（12 列）、`v<3`、`z<=1`、`t<%d`。' % tmax)
    print('`Q = Lift1 ((0,v,z) :: R.dropLast) t`')
    print()
    print('| `|R|` | `z` | **分母（前提を全部満たす `(R,v,t)`）** | `h2` 成立 | `h2` 率 |'
          ' `h2\'`（`1<=j`）成立 | `h2\'` 率 |')
    print('|--:|--:|--:|--:|--:|--:|--:|')
    ex3 = []      # (k3) z=1 の反例
    exA = []      # (A) h2' が破れる例
    for L in lens:
        for z in (0, 1):
            den = ok = okp = 0
            for R in itertools.product(cols, repeat=L):
                R = list(R)
                if dom_m(R) is None:
                    continue
                if srow(R, len(R) - 1) != 2:
                    continue
                for v in range(3):
                    if not has_parent([(0, v, z)] + R, 2, len(R)):
                        continue
                    if not any(p[2] != z for p in R[:-1]):
                        continue
                    for t in range(tmax):
                        Q = Lift1([(0, v, z)] + R[:-1], t)
                        den += 1
                        f, p = h2_full(Q), h2_prime(Q)
                        ok += f
                        okp += p
                        if not f and z == 1 and len(ex3) < 3:
                            ex3.append((R, v, z, t, Q))
                        if not p and len(exA) < 5:
                            exA.append((R, v, z, t, Q))
            print('| %d | %d | **%d** | %d | **%.1f%%** | %d | **%.1f%%** |'
                  % (L, z, den, ok, 100.0 * ok / max(den, 1),
                     okp, 100.0 * okp / max(den, 1)))
    print()
    print('### (k3) `z = 1` で `h2` が破れる具体例（前提は全部満たしている）')
    print()
    for R, v, z, t, Q in ex3:
        print('    R=`%s`  v=%d  z=%d  t=%d' % (fmt(R), v, z, t))
        print('        Q = Lift1 ((0,%d,%d) :: R.dropLast) %d = `%s`' % (v, z, t, fmt(Q)))
        print('        entry Q 2 0 = %d > 0、しかし hasParent (Q.take 1) 2 0 は常に偽'
              % entry(Q, 2, 0))
    print()
    print('### (A) 弱めた `h2\'`（`1 <= j`）が破れる例')
    print()
    if exA:
        for R, v, z, t, Q in exA:
            bad = [j for j in range(1, len(Q))
                   if entry(Q, 2, j) > 0 and not has_parent(Q[:j + 1], 2, j)]
            print('    ⛔ R=`%s` v=%d z=%d t=%d Q=`%s`  破れる j = %s'
                  % (fmt(R), v, z, t, fmt(Q), bad))
    else:
        print('> **`h2\'` の反例はゼロ。⟹ `j = 0` を外すだけで前提は消費側で満たせる。**')
    print()


if __name__ == '__main__':
    main(lens=(2, 3, 4), tmax=3)
