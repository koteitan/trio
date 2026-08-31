# -*- coding: utf-8 -*-
"""**課題 (y2a)-(y2c) ＋ (x1)(y1)(x2)（L3 / team-lead の依頼）—— 窓 `V` の中のブロッカー。**

**場面**: `S_j = mTower Q d e n ++ Bn.take (j+1)`、復活（親 `par < n*|Q|`）。
**窓 `V = S[par : last]`**（`oper` が写す塊。`range' par (last−par)`）。

## ⚠ 主語の確認（教訓 68。team-lead の警告どおり）

**`V` の根は `V[0] = S[par]`。** これが `V` の中で行 0 最浅であることは **`nextrel0` から出る**:
`par < j < last` の全列で `entry S 0 last <= entry S 0 j`、かつ `entry S 0 par < entry S 0 last`
⟹ **`S[par]` は `V` の中で狭義に最浅**。∎ ⟹ **`V` の根 ＝ `V[0]` でよい。**

**ブロッカーなし `Q` の定義**（§152、`Lcone.le1_zero_iff` の否定から）:
**`∀ y ∈ [1, |Q|), entry Q 1 0 < entry Q 1 y`**（根が狭義最浅なので全列が行 0 祖先）。

## ★ 予想を先に書く（教訓 45）＋ 見積もり（L3 の §105.2）

**team-lead の式の検算（私の導出）**: ブロッカーなしなら **全列が錐の中** ⟹ `Lift1` が全列に効く。
`V` の根 ＝ ブロック `n−1` の列 `q0` ⟹ `entry V 1 0 = entry Q 1 q0 + e*(n−1)`。
ブロック `n` の列 `q` ⟹ `entry Q 1 q + e*n`。差は

    **`(entry Q 1 q + e*n) − (entry Q 1 q0 + e*(n−1)) = entry Q 1 q − entry Q 1 q0 + e`**

⟹ **`<= 0` ⟺ `entry Q 1 q0 >= entry Q 1 q + e`** ⟹ **team-lead の式は正しい（導出できる）。**

> **予想: 起きる。`Q` の行 1 が「大きい列 → 小さい列」の順に並び、`e` が小さいとき。**
> **⚠ 見積もり: (y2a) は 20 〜 50%。**
> **(y2c) `e` を大きくすると `entry Q 1 q0 − entry Q 1 q < e` になりやすい ⟹ 減るはず。**

**箱と単位**: 単位 `(Q,d,e,n,j)` の復活したもの。箱 = 行0<4, 行1<4, 行2<=cm、
`|Q| = 3..4`、`d ∈ 0..3`、`e ∈ 0..4`、`n ∈ 2..4`。**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow, le1_root
from r113 import mTower
from r141 import block


def blockerfree(Q):
    return all(Q[0][1] < Q[y][1] for y in range(1, len(Q)))


def run(cm, L, DS, ES, NS, R1):
    COL = [(a, b, c) for a in range(4) for b in range(R1) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            bf = blockerfree(Q)
            c[('(x1) ブロッカーなし', bf)] += 1
            c[('(y1) 根の行2 == 0', Q[0][2] == 0)] += 1
            if not bf:
                # (x2) 帯（錐の外 ∧ 行1 が根より上）に入る列の本数
                band = sum(1 for j in range(1, L)
                           if (not le1_root(Q, j)) and Q[0][1] < Q[j][1])
                c[('(x2) 帯の本数', min(band, 3))] += 1
                continue
            for d in DS:
                for e in ES:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        Bn = block(Q, d, e, n)
                        for j in range(L):
                            S = T + Bn[:j + 1]
                            last = len(S) - 1
                            par = trio.parent(S, srow(S, last), last)
                            if par is None or par >= n * L:
                                continue
                            V = S[par:last]
                            c['★ 復活（ブロッカーなし `Q`）'] += 1
                            # (y2a) `V` の中に「行 1 が `V` の根以下」の列があるか
                            bad = [i for i in range(1, len(V)) if V[i][1] <= V[0][1]]
                            c[('★ (y2a) V にブロッカーあり', bool(bad))] += 1
                            c[('(y2c) e 別', e, bool(bad))] += 1
                            if bad:
                                # (y2b) team-lead の式で説明がつくか
                                q0 = par % L
                                ok = any(Q[0][1] + 0 <= 0 or
                                         Q[q0][1] >= Q[(par + i) % L][1] + e for i in bad)
                                c[('(y2b) team-lead の式で説明', ok)] += 1
                                ex.setdefault('★ (y2a) の例',
                                              (Q, d, e, n, j, par, q0,
                                               [(i, (par + i) % L) for i in bad[:3]]))
    print(f'### 行2<={cm} |Q|={L} 行1<{R1}  [{time.time()-t0:.1f}s]')
    bfy = c[('(x1) ブロッカーなし', True)]; bfn = c[('(x1) ブロッカーなし', False)]
    print(f'  **(x1) ブロッカーなしの `Q`: {bfy} / {bfy+bfn} ({100*bfy/(bfy+bfn):6.2f}%)**')
    z0 = c[('(y1) 根の行2 == 0', True)]
    print(f'  **(y1) 根の行 2 = 0: {z0} / {bfy+bfn} ({100*z0/(bfy+bfn):6.2f}%)**')
    print('  **(x2) ブロッカーを持つ `Q` の帯の本数**: ', dict(sorted((k[1], c[k]) for k in c
                                                     if isinstance(k, tuple) and k[0] == '(x2) 帯の本数')))
    tot = c['★ 復活（ブロッカーなし `Q`）']
    print(f'  **★ 復活（ブロッカーなしの `Q`）: {tot}**')
    if tot:
        y = c[('★ (y2a) V にブロッカーあり', True)]
        print(f'  **★★ (y2a) 窓 `V` の中に「行 1 が `V` の根以下」の列: {y} / {tot} '
              f'({100*y/tot:6.2f}%)**')
        print(f'      (y2b) team-lead の式で説明がつく: {c[("(y2b) team-lead の式で説明", True)]} / {y}')
        print('      **(y2c) `e` 別**: ', {e: (c[('(y2c) e 別', e, True)],
                                            c[('(y2c) e 別', e, True)] + c[('(y2c) e 別', e, False)])
                                        for e in ES
                                        if c[('(y2c) e 別', e, True)] + c[('(y2c) e 別', e, False)]})
    for k in sorted(ex):
        print(f'      {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for cm in (1,):
        for R1 in (4,):
            for L in range(3, a.L + 1):
                run(cm, L, range(4), range(5), (2, 3, 4), R1)
