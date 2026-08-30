# -*- coding: utf-8 -*-
"""**team-lead の問い (a)/(b)/(c) への回答 ＋ §111 の (A)/(B)/(C) での測り直し。**

## ★ 問いへの回答: **(a) 子（足す列）の添字です**

    私の `j` … **`S_j = mTower Q d e n ++ Bn.take (j+1)` で足す列の、ブロック内の位置**（＝ **子**）
    親の添字は `par`（絶対）／`p_rel = par mod |Q|`（ブロック内）

## ⚠⚠ そして **場面が違います**

    **§111 の場面** … **`Q ++ [p]`**（**`Q` に 1 列足す**）。`j0` は `Q ++ [p]` の中の親の添字
    **私の場面**    … **`mTower Q d e n ++ Bn.take (j+1)`**（**塔に足す**）

⟹ **私の場面では `n >= 2` なので `par >= (n−1)*|Q| >= |Q| > 0` ⟹ §111 の (B)（親 = 根、`j0 = 0`）は
「塔の根」を指し、私の測定では 0% になります。**
⟹ **「90.6% が `j = 0`」は §111 の (B) とは別物**（あちらは**親**の位置、こちらは**子**の位置）。

## ⟹ そこで §111 の場面（`Q ++ [p]`）で (A)(B)(C) を測り直す

`p = (entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0)`（`TowerSnocRoot` の足す列）。

    **(A) 親なし** … `snoc_orphan_W` で無料
    **(B) 親 = 根（`j0 = 0`）** … §110 で `MTowerClosedS` ＝ 核
    **(C) 親が内側（`j0 >= 1`）** … `Q.take j0` は触られない ⟹ 短い `Q` に降りる

## ★ 予想を先に（教訓 45）＋ 見積もり

**§R141（R134）の実測から**: 本丸（`z=0 ∧ d>=1 ∧ e>=1`）で
**親 = 根 47.6 〜 62.1%（`|Q|` で減少）／親 = 末尾列 31.0 〜 37.9%／親 = 内部 0 〜 21.4%（増加）**。
> **予想: (B) は `|Q|` とともに減り、(C) は増える。**
> **見積もり: `|Q|=5` で (B) 45 〜 50%、(C) 20 〜 25%（非孤児のうち）。**

**箱と単位**: 単位 `(Q, d, e)`。箱 = 行0<4, 行1<3, 行2<=cm（3 段）、`|Q| = 2..5`、`d,e ∈ 0..3`。
母集団 = **根が狭義最浅**。**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow


def run(cm, L, DE):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter()
    t0 = time.time()
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            for d in DE:
                for e in DE:
                    p = (Q[0][0] + d, Q[0][1] + e, Q[0][2])
                    S = Q + [p]
                    j = L
                    i = srow(S, j)
                    j0 = trio.parent(S, i, j)
                    c['分母'] += 1
                    if j0 is None:
                        c['(A) 親なし'] += 1
                        continue
                    if j0 == 0:
                        c['★ (B) 親 = 根'] += 1
                    else:
                        c['(C) 親が内側'] += 1
                        c[('(C) の j0', j0)] += 1
                        c[('(C) j0 == |Q|-1（末尾列）', j0 == L - 1)] += 1
                    c[('srow(p)', i)] += 1
    tot = c['分母']; nonorp = tot - c['(A) 親なし']
    print(f'### 行2<={cm} |Q|={L}  分母 {tot:9d}  [{time.time()-t0:.1f}s]')
    print(f'  **(A) 親なし  {c["(A) 親なし"]:9d} ({100*c["(A) 親なし"]/tot:6.2f}%)**')
    print(f'  **★ (B) 親 = 根 {c["★ (B) 親 = 根"]:9d} ({100*c["★ (B) 親 = 根"]/tot:6.2f}% of 全体、'
          f'{100*c["★ (B) 親 = 根"]/max(nonorp,1):6.2f}% of 非孤児)**')
    print(f'  **(C) 親が内側 {c["(C) 親が内側"]:9d} ({100*c["(C) 親が内側"]/tot:6.2f}% of 全体、'
          f'{100*c["(C) 親が内側"]/max(nonorp,1):6.2f}% of 非孤児)**')
    print('      **(C) の `j0` の分布**: ', dict(sorted((k[1], c[k]) for k in c
                                            if isinstance(k, tuple) and k[0] == '(C) の j0')),
          f'   `j0 = |Q|-1`（末尾列）: {c[("(C) j0 == |Q|-1（末尾列）", True)]}')
    print('      `srow(p)`: ', dict(sorted((k[1], c[k]) for k in c
                                      if isinstance(k, tuple) and k[0] == 'srow(p)')))
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=5)
    a = ap.parse_args()
    for cm in (1, 2):
        for L in range(2, a.L + 1):
            run(cm, L, range(4))
