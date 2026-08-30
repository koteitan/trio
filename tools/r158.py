# -*- coding: utf-8 -*-
"""**課題 (w1)-(w3)（team-lead の依頼）—— 復活の親のブロック内「相対位置」。**

**場面**: `S_j = mTower Q d e n ++ Bn.take (j+1)`。復活 ＝ 親 `par < n*|Q|`。
`k = par // |Q|`（親のブロック）、**`p_rel = par mod |Q|`**（ブロック内の相対位置）。
§R156 より **`k = n − 1` が 100%** なので、親は常に 1 つ前のブロックの中。

## ★ 予想を先に書く（教訓 45）＋ 見積もり（L3 の §105.2）

**(w2)** 「`p_rel == j`（前ブロックの同じ場所）」の割合。
⚠ **§R154 の実測から予想できる**: `|Q|=3` で
**親の列 `q` の分布 `{0: 55,404, 1: 23,827, 2: 95,211}`** に対し
**復活の `j` の分布 `{0: 155,110, 1: 18,972, 2: 360}`** ⟹ **形が全く違う。**
> **予想: `p_rel == j` は低い。見積もり 10 〜 30%。**
> **⚠ 反例の形: `j = 0` の復活（全体の 90.6%）で `p_rel = |Q|-1` なら `p_rel ≠ j`。**

**(w3)** `j = 0` の復活で親が前ブロックの**最終列**（`par == n*|Q| − 1`）か。
⚠ §143 は**行 0** の親についての主張。`j = 0` で要るのは**行 `srow`** の親。
§R154 の `q` 分布で `q = |Q|-1` は 54.6% だった。
> **予想: 100% にはならない。見積もり 50 〜 70%。**

**(w1c)** 窓 `last − par` の分布。`k = n−1` かつ `p_rel` が散るので
**`last − par = |Q| + j − p_rel` ⟹ `|Q|+j−(|Q|−1) = j+1` 〜 `|Q|+j`。**
> **⟹ 有界（`< 2|Q|`）のはず。見積もり: `< 2|Q|` が 100%。**

**箱と単位**: 単位 `(Q,d,e,n,j)` の復活したもの。箱 = 行0<4, 行1<3, 行2<=cm、
`|Q| = 3..4`、`d,e ∈ 0..3`、`n ∈ 2..5`。**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow, le1_root
from r113 import mTower
from r141 import block


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
                            if par is None or par >= n * L:
                                continue
                            k, prel = divmod(par, L)
                            jk = 'j=0' if j == 0 else '★ j>=1'
                            c[(jk, '復活')] += 1
                            c[('(w1a) j 別', j)] += 1 if jk == '★ j>=1' else 0
                            c[(jk, '(w1b) p_rel', prel)] += 1
                            c[(jk, '(w1b) p_rel == |Q|-1', prel == L - 1)] += 1
                            c[(jk, '★ (w2) p_rel == j', prel == j)] += 1
                            c[(jk, '(w2) j - p_rel', j - prel)] += 1
                            win = last - par
                            c[(jk, '(w1c) 窓 last-par', win)] += 1
                            c[(jk, '(w1c) 窓 < 2|Q|', win < 2 * L)] += 1
                            if jk == 'j=0':
                                c[('★ (w3) par == n|Q|-1', par == n * L - 1)] += 1
                                if par != n * L - 1:
                                    ex.setdefault('w3 破れ', (Q, d, e, n, par, n * L - 1))
                            if prel != j:
                                ex.setdefault(('w2 破れ', jk), (Q, d, e, n, j, par, prel))
    print(f'### 行2<={cm} |Q|={L}  [{time.time()-t0:.1f}s]')
    for jk in ('★ j>=1', 'j=0'):
        tot = c[(jk, '復活')]
        if not tot:
            continue
        print(f'  {jk}: 復活 {tot:9d}')
        print(f'      **(w2) `p_rel == j`: {c[(jk, "★ (w2) p_rel == j", True)]:9d} '
              f'({100*c[(jk, "★ (w2) p_rel == j", True)]/tot:6.2f}%)**   '
              f'`j − p_rel` の分布: ' + str(dict(sorted((kk[2], c[kk]) for kk in c
                                              if isinstance(kk, tuple) and len(kk) == 3
                                              and kk[0] == jk and kk[1] == '(w2) j - p_rel'))))
        print(f'      **(w1b) `p_rel`**: ' + str(dict(sorted((kk[2], c[kk]) for kk in c
                                              if isinstance(kk, tuple) and len(kk) == 3
                                              and kk[0] == jk and kk[1] == '(w1b) p_rel')))
              + f'   `p_rel == |Q|-1`: {c[(jk, "(w1b) p_rel == |Q|-1", True)]} '
              f'({100*c[(jk, "(w1b) p_rel == |Q|-1", True)]/tot:6.2f}%)')
        print(f'      **(w1c) 窓 `last−par`**: ' + str(dict(sorted((kk[2], c[kk]) for kk in c
                                                  if isinstance(kk, tuple) and len(kk) == 3
                                                  and kk[0] == jk and kk[1] == '(w1c) 窓 last-par')))
              + f'   **`< 2|Q|`: {c[(jk, "(w1c) 窓 < 2|Q|", True)]} '
              f'({100*c[(jk, "(w1c) 窓 < 2|Q|", True)]/tot:6.2f}%)**')
    print('  **(w1a) `j >= 1` の復活の `j` 分布**: ', dict(sorted((k[1], c[k]) for k in c
                                                    if isinstance(k, tuple) and k[0] == '(w1a) j 別' and c[k])))
    y = c[('★ (w3) par == n|Q|-1', True)]; nn = c[('★ (w3) par == n|Q|-1', False)]
    if y + nn:
        print(f'  **★ (w3) `j=0` の復活で親が前ブロックの最終列: {y} / {y+nn} '
              f'({100*y/(y+nn):6.2f}%)**')
    for k in sorted(ex, key=str):
        print(f'      {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for cm in (1, 2):
        for L in range(3, a.L + 1):
            run(cm, L, range(4), (2, 3, 4, 5))
