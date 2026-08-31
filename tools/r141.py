# -*- coding: utf-8 -*-
"""**課題 (q1)-(q3)（L3 の直接依頼）—— `hstep` の場面で親の位置 `p` はどこか。**

**場面**（§94 / §138）: `T = mTower Q d e n`、ブロック `n` は `Bn = Lift1 (shiftr01 (d*n) 0 Q) (e*n)`。
**`S_j = T ++ Bn.take (j+1)`**（塔にブロックの第 `j` 列まで足した列）。
足した列は `Bn[j]`、その親を `par` とする。

    `par >= n*|Q|` ⟹ **同じブロックの中**。**`p = par − n*|Q|`**（L3 の §138 の `p`）
    `par <  n*|Q|` ⟹ **前のブロックへ逃げた**（§138 の想定外）

**L3 の測度の候補**: 窓の長さ `j − p`。**`p >= 1` なら窓はブロックより短く整礎、`p = 0` なら
窓 ＝ ブロック全体で減らない**（§121 の「塔の塔」）。

## ★ 反例の形を先に書く（教訓 45）＋ 充足率の見積もり（L3 の §105.2）

> **⚠ 反例の形: 「親が前のブロックにある（`par < n*|Q|`）」。**
> §138 は親が同じブロックにあると想定している。私は §R134（F2b）で
> **親が 1 つ前のブロックへ逃げる**のを見ている。
> **⚠ 見積もり: 逃げるのは 0 〜 10%**（§R145 では (T1) の場面で「ブロック戻り 0 が 100%」だった）。
>
> **⚠ `j = 0` は必ず逃げる**（ブロックが 1 列では自分の中に親を持てない。L3 の §104）
> ⟹ **`j >= 1` と `j = 0` を分けて数える。**
>
> **(q1) `p = 0` の割合の見積もり: 20 〜 50%**（`|Q|` で減少）。
> 根拠: §R145 の (T1) の場面（`j = 0` に相当）では 47.6 〜 62.1% で `|Q|` とともに減っていた。
> `j >= 1` ではブロック内の候補が増えるので、それより**低いはず**。
>
> **(q2) は定義から自動**: `j <= |Q|−1` かつ `p >= 1` ⟹ `j − p <= |Q| − 2 < |Q|`。

**箱と単位**: 単位 `(Q, d, e, n, j)`。箱 = 行0<4, 行1<3, 行2<=cm（**3 段**）、
`|Q| = 2..5`、`d, e ∈ 0..3`、`n ∈ 1..3`。母集団 = **根が狭義最浅**。
**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow, le1_root
from r113 import mTower


def block(Q, d, e, k):
    """ブロック `k` ＝ `Lift1 (shiftr01 (d*k) 0 Q) (e*k)`。"""
    return [(Q[i][0] + d * k, Q[i][1] + (e * k if le1_root(Q, i) else 0), Q[i][2])
            for i in range(len(Q))]


def run(cm, L, DE, NS):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            for d in DE:
                for e in DE:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        Bn = block(Q, d, e, n)
                        for j in range(L):
                            S = T + Bn[:j + 1]
                            last = len(S) - 1
                            par = trio.parent(S, srow(S, last), last)
                            jk = 'j=0' if j == 0 else '★ j>=1'
                            c[(jk, '分母')] += 1
                            if par is None:
                                c[(jk, '孤児')] += 1
                                continue
                            if par < n * L:
                                c[(jk, '⚠ 親が前のブロック')] += 1
                                ex.setdefault(('前のブロック', jk),
                                              (Q, d, e, n, j, par, n * L))
                                continue
                            p = par - n * L
                            c[(jk, '★ 親は同じブロック')] += 1
                            c[(jk, 'p==0', p == 0)] += 1
                            if p == 0:
                                c[('(q3) p=0 のときの j', j)] += 1
                            else:
                                c[('(q2) 窓 j-p < |Q|', (j - p) < L)] += 1
                                c[('(q2) 窓の長さ j-p', j - p)] += 1
    print(f'### 行2<={cm} |Q|={L}  [{time.time()-t0:.1f}s]')
    for jk in ('★ j>=1', 'j=0'):
        tot = c[(jk, '分母')]
        if not tot:
            continue
        same = c[(jk, '★ 親は同じブロック')]
        print(f'  {jk}: 分母 {tot:8d}  孤児 {c[(jk, "孤児")]:8d}  '
              f'**前のブロックへ逃げた {c[(jk, "⚠ 親が前のブロック")]:8d} '
              f'({100*c[(jk, "⚠ 親が前のブロック")]/tot:6.2f}%)**  同じブロック {same:8d}')
        if same:
            z = c[(jk, 'p==0', True)]
            print(f'      **(q1) `p = 0` の割合: {z:8d} / {same} ({100*z/same:6.2f}%)**')
    print('  **(q2) 窓 `j−p < |Q|`**: ', dict(sorted((k[1], c[k]) for k in c
                                             if isinstance(k, tuple) and k[0] == '(q2) 窓 j-p < |Q|')),
          '   窓の長さ: ', dict(sorted((k[1], c[k]) for k in c
                              if isinstance(k, tuple) and k[0] == '(q2) 窓の長さ j-p')))
    print('  **(q3) `p = 0` のときの `j`**: ', dict(sorted((k[1], c[k]) for k in c
                                              if isinstance(k, tuple) and k[0] == '(q3) p=0 のときの j')))
    for k in sorted(ex, key=str):
        print(f'      例 {k}: Q={ex[k][0]} d={ex[k][1]} e={ex[k][2]} n={ex[k][3]} '
              f'j={ex[k][4]} 親={ex[k][5]}（ブロック先頭 {ex[k][6]}）')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=5)
    a = ap.parse_args()
    for cm in (1, 2):
        for L in range(2, a.L + 1):
            run(cm, L, range(4), (1, 2, 3))
