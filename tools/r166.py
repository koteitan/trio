# -*- coding: utf-8 -*-
"""**課題 (H3')(H2')（L3 の依頼）—— 部分窓 `V` での遺伝。**

**窓の定義**: `M = mTower Q d e n ++ Bn.take (j+1)`、`par` を悪根、**`V = M[par : last]`**
（`oper` が写す塊。§165 `gexp_eq_take_append_mTower` の `V = (M.drop j0).take Lb`）。

    **(H3')** `Q` の非根の列が**全部錐の中**（＝ ブロッカーなし、§152）のとき、
             **`V` の非根の列も `V` の錐の中か**
    **(H2')** `Q` が `h2` を満たすとき、**`V` も `h2` を満たすか**

## ★ 予想を先に書く（教訓 45）＋ 見積もり（L3 の §105.2）

**(H3')** ⚠ **L3 の予測は「偽」**。私の §R159 (y2) では、ブロッカーなしの `Q` でも
**窓 `V` の中に「行 1 が `V` の根以下」の列が 6.34 / 11.10%** あった。
§R133 より **錐の外 ⟸ 鎖上に行 1 が根以下の列がある** なので、
**(H3') の破れは (y2) の率**以上**のはず。⚠ 見積もり 10 〜 30% で破れる。**

**(H2')** `V` は連続する切り出しなので、**`V.take (i+1)` は `Q.take (j+1)` より短い**
⟹ 行 2 の親が落ちうる。**⚠ 見積もり 20 〜 50% で破れる。**
> **⚠ 反例の形: `V` の中で行 2 が正の列の、行 2 の親が `V` の外（`par` より前）にある。**

**箱と単位**: 単位 `(Q,d,e,n,j)` の復活/親ありのもの。箱 = 行0<4, 行1<3, 行2<=1、
`|Q| = 3..4`、`d,e ∈ 0..3`、`n ∈ 2..4`。**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow, le1_root
from r113 import mTower
from r141 import block


def nb(Q):
    return all(Q[0][1] < Q[l][1] for l in range(1, len(Q)))


def h2ok(Q):
    return all(trio.parent(Q[:i + 1], 2, i) is not None
               for i in range(len(Q)) if Q[i][2] > 0)


def h2ok_pos(Q):
    """`h2` の `0 < j` 制限版（§R162-6）。"""
    return all(trio.parent(Q[:i + 1], 2, i) is not None
               for i in range(1, len(Q)) if Q[i][2] > 0)


def run(cm, L, DE, NS):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            qnb = nb(Q); qh2 = h2ok(Q); qh2p = h2ok_pos(Q)
            if not (qnb or qh2 or qh2p):
                continue
            for d in DE:
                for e in DE:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        Bn = block(Q, d, e, n)
                        for j in range(L):
                            S = T + Bn[:j + 1]
                            last = len(S) - 1
                            par = trio.parent(S, srow(S, last), last)
                            if par is None:
                                continue
                            V = S[par:last]
                            if len(V) < 2:
                                continue
                            if qnb:
                                c['(H3\') 分母'] += 1
                                vin = all(le1_root(V, i) for i in range(1, len(V)))
                                c[('★ (H3\') V も全部錐の中', vin)] += 1
                                if not vin:
                                    ex.setdefault('H3 破れ', (Q, d, e, n, j, par, V[:5]))
                            if qh2:
                                c['(H2\') 分母'] += 1
                                c[('★ (H2\') V も h2', h2ok(V))] += 1
                                if not h2ok(V):
                                    ex.setdefault('H2 破れ', (Q, d, e, n, j, par, V[:5]))
                            if qh2p:
                                c['(H2\'制限版) 分母'] += 1
                                c[('(H2\'制限版) V も h2', h2ok_pos(V))] += 1
    print(f'### 行2<={cm} |Q|={L}  [{time.time()-t0:.1f}s]')
    for lab, dn in (("★ (H3') V も全部錐の中", "(H3') 分母"),
                    ("★ (H2') V も h2", "(H2') 分母"),
                    ("(H2'制限版) V も h2", "(H2'制限版) 分母")):
        tot = c[dn]
        if not tot:
            continue
        y = c[(lab, True)]
        print(f'  **{lab}: {y:9d} / {tot} ({100*y/tot:6.2f}%)**  破れ {tot-y}')
    for k in sorted(ex):
        print(f'      {k}: Q={ex[k][0]} d={ex[k][1]} e={ex[k][2]} n={ex[k][3]} '
              f'j={ex[k][4]} par={ex[k][5]} V={ex[k][6]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for cm in (1,):
        for L in range(3, a.L + 1):
            run(cm, L, range(4), (2, 3, 4))
