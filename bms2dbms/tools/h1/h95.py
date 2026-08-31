# -*- coding: utf-8 -*-
"""**(c) の予測: `j = 0` の窓が `|Q|` より短くなるのはいつか。**

§261 の例を解析すると: 第 `n` ブロックの根の行 1 は `entry Q 1 0 + e*n`。
第 `n-1` ブロックの列 `i`（錐の中）の行 1 は `entry Q 1 i + e*(n-1)`。
⟹ 列 `i` が候補になる条件は

    **`entry Q 1 i < entry Q 1 0 + e`**

⟹ **予測: 窓 < |Q| ⟺ ∃ i > 0（行 0 で末尾の祖先）, `entry Q 1 i < entry Q 1 0 + e`**

⚠ これは `TieFree` と同じ形の**閾値条件**（閾値が `v + e`）。
実測で予測が当たるかを確かめる（分母つき、教訓 23）。
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


def predict_short(Q, e):
    """予測: 窓 < |Q| になるか。"""
    return any(entry(Q, 1, i) < entry(Q, 1, 0) + e for i in range(1, len(Q)))


def main(lens=(2, 3), ns=(1, 2, 3), tmax=2, vmax=3, cmax=2):
    cols = [(a, b, c) for a in range(1, 3) for b in range(3) for c in range(cmax)]
    tab = Counter()
    ex = []
    for L in lens:
        for R in itertools.product(cols, repeat=L):
            R = list(R)
            if not argOK(R) or dom_m(R) is None or srow(R, len(R) - 1) != 2:
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
                    pred = predict_short(Q, e)
                    for n in ns:
                        T = mTower(Q, d, e, n)
                        B = Lift1(shiftr01(d * n, 0, Q), e * n)
                        C1 = T + B[:1]
                        p = len(T)
                        par = trio.parent(C1, srow(C1, p), p)
                        if par is None:
                            tab['親なし'] += 1
                            continue
                        short = (p - par) < len(Q)
                        tab[('予測=%s ・ 実際=%s'
                             % ('短い' if pred else '`|Q|`',
                                '短い' if short else '`|Q|`'))] += 1
                        if pred != short and len(ex) < 4:
                            ex.append((R, v, t, n, Q, d, e, p - par))
    wref.tally(tab, '**予測 vs 実際**（`j = 0` の窓）')
    if ex:
        print('**⛔ 予測が外れた例:**')
        for R, v, t, n, Q, d, e, w in ex:
            print('    R=`%s` v=%d t=%d n=%d Q=`%s` d=%d e=%d 窓=%d'
                  % (fmt(R), v, t, n, fmt(Q), d, e, w))
    else:
        print('> **★ 予測が 100% 当たった。**')
        print('> ⟹ **窓 < |Q| ⟺ ∃ i > 0, `entry Q 1 i < entry Q 1 0 + e`**')
    print()


if __name__ == '__main__':
    print('## (c) `j = 0` の窓が短くなる条件の予測検証')
    print()
    main()
