# -*- coding: utf-8 -*-
"""**課題 (n0)(n1)（team-lead の依頼）—— 行 2 の孤児の遺伝と、`|V| < |Q|`。**

## ★ (n0) 予想を先に書く（教訓 45）＋ 見積もり

**(n0)**: `Q` の列 `j` が `Q.take (j+1)` で行 2 の孤児 ⟹ 塔でも孤児か。
⚠ **ブロック 0 は `Lift1 (shiftr01 0 0 Q) 0 = Q` なので自明。⟹ `k >= 1` だけを見る。**
`nextrel2 T a b` は **`le1 T a b`** ∧ 行 2 の狭義増加 ∧ 極小性。塔は行 2 を変えない
（`entry2_Lift1`、`Wset:955`）ので、行 2 の候補は各ブロックに同じだけある。
**⟹ 差は `le1` がブロックをまたげるかどうか。**
> **⚠ 反例の形: 「前のブロックのコピーの列が行 2 の親になる」。見積もり 10 〜 40% で破れる。**

## ★★ (n1) 予想 —— **`j = 0` で `|V| = |Q|` になり、強帰納は回らないはず**

`V = (M.drop j0).take Lb`、`Lb = last − j0`。`M = mTower Q d e n ++ Bn.take (j+1)`。

    **`j >= 1`（同ブロック）** … `par = n*|Q| + p` ⟹ **`Lb = j − p <= |Q| − 2`** ✓（L3 の主張）
    **`j = 0`（ブロックをまたぐ）** … `par = (n−1)*|Q| + p_rel` ⟹ **`Lb = |Q| − p_rel`**
      **⟹ `p_rel = 0` なら `Lb = |Q|` ⟹ `|V| = |Q|`。**真に短くならない。**

⚠ **§R158 の実測**: `j=0` の窓の分布は `|Q|=3` で `{1: 49.2%, 2: 15.1%, 3: 35.7%}`
⟹ **窓 = `|Q|` が 35.7% 起きている。** ⟹ **`|V| < |Q|` は `j = 0` で破れるはず。**
> **⚠ 見積もり: `j = 0` の 30 〜 40% で `|V| = |Q|`。**

**箱と単位**: (n0) 単位 `(Q,d,e,n,k,j)`。(n1) 単位 `(Q,d,e,n,j)` の復活したもの。
箱 = 行0<4, 行1<3, 行2<=1、`|Q| = 3..4`、`d,e ∈ 0..3`、`n ∈ 2..5`。
**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block


def n0(cm, L, DE, NS):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            orph = [j for j in range(L) if Q[j][2] > 0
                    and trio.parent(Q[:j + 1], 2, j) is None]
            if not orph:
                continue
            for d in DE:
                for e in DE:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        for k in range(1, n):        # ブロック 0 は自明
                            for j in orph:
                                b = k * L + j
                                p = trio.parent(T[:b + 1], 2, b)
                                c['分母'] += 1
                                if p is None:
                                    c['★ 塔でも孤児'] += 1
                                else:
                                    c['⛔ 塔では親あり'] += 1
                                    kp = p // L
                                    c[('(n0b) 親のブロック', '同じ' if kp == k else
                                       ('前' if kp < k else '後'))] += 1
                                    c[('(n0b) 戻り', k - kp)] += 1
                                    ex.setdefault('破れ', (Q, d, e, n, k, j, p, kp))
    tot = c['分母']
    print(f'### (n0) 行2<={cm} |Q|={L}  分母 {tot:9d}  [{time.time()-t0:.1f}s]')
    if tot:
        print(f'  **★ 塔でも孤児 {c["★ 塔でも孤児"]:9d} ({100*c["★ 塔でも孤児"]/tot:6.2f}%)**  '
              f'**⛔ 塔では親あり {c["⛔ 塔では親あり"]:9d} ({100*c["⛔ 塔では親あり"]/tot:6.2f}%)**')
        print('      (n0b) 親のブロック: ', dict(sorted((k[1], c[k]) for k in c
                                            if isinstance(k, tuple) and k[0] == '(n0b) 親のブロック')),
              '   戻り: ', dict(sorted((k[1], c[k]) for k in c
                                  if isinstance(k, tuple) and k[0] == '(n0b) 戻り')))
    for k in sorted(ex):
        print(f'      {k}: Q={ex[k][0]} d={ex[k][1]} e={ex[k][2]} n={ex[k][3]} '
              f'k={ex[k][4]} j={ex[k][5]} 親={ex[k][6]}（ブロック {ex[k][7]}）')
    print()


def n1(cm, L, DE, NS):
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
                            if par is None:
                                continue
                            Lb = last - par
                            jk = 'j=0' if j == 0 else 'j>=1'
                            c[(jk, '分母')] += 1
                            c[(jk, '|V| < |Q|', Lb < L)] += 1
                            c[(jk, '|V|', min(Lb, 2 * L))] += 1
                            if Lb >= L:
                                ex.setdefault(jk, (Q, d, e, n, j, par, Lb))
    print(f'### (n1) 行2<={cm} |Q|={L}  [{time.time()-t0:.1f}s]')
    for jk in ('j>=1', 'j=0'):
        tot = c[(jk, '分母')]
        if not tot:
            continue
        y = c[(jk, '|V| < |Q|', True)]
        print(f'  {jk}: 分母 {tot:9d}  **`|V| < |Q|` {y:9d} ({100*y/tot:6.2f}%)**  '
              f'`|V|` の分布 ' + str(dict(sorted((k[2], c[k]) for k in c
                                          if isinstance(k, tuple) and len(k) == 3
                                          and k[0] == jk and k[1] == '|V|'))))
        if jk in ex:
            print(f'      ⛔ `|V| >= |Q|` の例: Q={ex[jk][0]} d={ex[jk][1]} e={ex[jk][2]} '
                  f'n={ex[jk][3]} j={ex[jk][4]} par={ex[jk][5]} |V|={ex[jk][6]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--part', default='01')
    a = ap.parse_args()
    for cm in (1,):
        for L in (3, 4):
            if '0' in a.part:
                n0(cm, L, range(4), (2, 3, 4, 5))
            if '1' in a.part:
                n1(cm, L, range(4), (2, 3, 4, 5))
