# -*- coding: utf-8 -*-
"""**課題 (t1)-(t4)（L3 の直接依頼）—— 復活する列の帯と、飛び先ブロック `k`。**

**場面**: `S_j = mTower Q d e n ++ Bn.take (j+1)`。復活 ＝ 親が `n*|Q|` 未満。

**L3 の §141-142 の予測:**

    **(t1)** 復活する列は **`Q` の錐の外**（`¬ le1 Q 0 j`）… **予測 100%**
    **(t2)** 復活する列は **`entry Q 1 0 < entry Q 1 j`** … **予測 100%**
    **(t3)** 飛び先のブロック `k` は **`n` に依存しない**
    **(t4)** `k` は **`entry Q 1 0 + e*k < entry Q 1 j` を満たす最大の `k`**、親はその**根**

## ⚠⚠ 反例の形を先に書く（教訓 45）—— **私の §R154 は (t3)(t4) と食い違う**

> **§R154（分母 174,442）で:**
>     **親のブロック戻り `n − k` は 1 が 100%** ⟹ **`k = n − 1`** ⟹ **`n` に依存する**
>     **親の列 `q` は `{0: 55,404, 1: 23,827, 2: 95,211}`** ⟹ **根（`q=0`）は 32% だけ**
>
> **⟹ (t3)「`k` は `n` に依存しない」は**外れるはず**。見積もり: `n` 非依存は 0 〜 20%。**
> **⟹ (t4)「親はブロック `k` の根」も**外れるはず**。見積もり: 根は 25 〜 40%。**
>
> ⚠ **ただし §R154 は `j` を全域（`j=0` 込み）で見ていた。`j = 0` は 88.9〜90.6% を占める。**
> **⟹ `j >= 1` の帯（L3 の核）だけに絞ると違うかもしれない。そこを分けて測る。**

**(t1)(t2) の予測は 100% なので、教訓 21 どおり伸ばして壊しにいく。**

**箱と単位**: 単位 `(Q, d, e, n, j)`。箱 = 行0<4, 行1<4, 行2<=cm、`|Q| = 3..4`、
`d,e ∈ 0..3`、**`n ∈ 2..5`**。母集団 = **根が狭義最浅** ∧ **復活したもの**。
**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow, le1_root
from r113 import mTower
from r141 import block


def run(cm, L, DE, NS, R1):
    COL = [(a, b, c) for a in range(4) for b in range(R1) for c in range(cm + 1)]
    c = Counter(); ex = {}; kmap = {}
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
                            jk = 'j=0' if j == 0 else '★ j>=1（帯）'
                            k, q = divmod(par, L)
                            c[(jk, '復活')] += 1
                            # (t1)(t2)
                            c[(jk, '(t1) 錐の外', not le1_root(Q, j))] += 1
                            c[(jk, '(t2) 行1 が根より上', Q[0][1] < Q[j][1])] += 1
                            c[(jk, '★ (t1)∧(t2)', (not le1_root(Q, j)) and Q[0][1] < Q[j][1])] += 1
                            if le1_root(Q, j):
                                ex.setdefault(('t1 破れ', jk), (Q, d, e, n, j, par))
                            if not (Q[0][1] < Q[j][1]):
                                ex.setdefault(('t2 破れ', jk), (Q, d, e, n, j, par))
                            # (t3)(t4)
                            c[(jk, '(t3) k == n-1', k == n - 1)] += 1
                            c[(jk, '(t4) 親は根 (q=0)', q == 0)] += 1
                            # L3 の式: entry Q 1 0 + e*k' < entry Q 1 j を満たす最大の k'
                            ks = [kk for kk in range(n) if Q[0][1] + e * kk < Q[j][1]]
                            kf = max(ks) if ks else None
                            c[(jk, '(t4) k == L3 の式', k == kf)] += 1
                            kmap.setdefault((tuple(Q), d, e, j), {})[n] = k
    print(f'### 行2<={cm} |Q|={L} 行1<{R1}  [{time.time()-t0:.1f}s]')
    for jk in ('★ j>=1（帯）', 'j=0'):
        tot = c[(jk, '復活')]
        if not tot:
            continue
        print(f'  {jk}: 復活 {tot:8d}')
        for lab in ('(t1) 錐の外', '(t2) 行1 が根より上', '★ (t1)∧(t2)',
                    '(t3) k == n-1', '(t4) 親は根 (q=0)', '(t4) k == L3 の式'):
            y = c[(jk, lab, True)]
            print(f'      {lab:22s}: {y:8d} / {tot} ({100*y/tot:6.2f}%)')
    # (t3) `n` を振って `k` が同じか
    same = sum(1 for v in kmap.values() if len(set(v.values())) == 1 and len(v) > 1)
    diff = sum(1 for v in kmap.values() if len(set(v.values())) > 1)
    nn1 = sum(1 for v in kmap.values() if all(kk == n_ - 1 for n_, kk in v.items()) and len(v) > 1)
    print(f'  **★ (t3) 同じ `(Q,d,e,j)` で `n` を振ったとき**: '
          f'`k` が一定 {same}  **`k` が動く {diff}**  うち **`k = n−1` が常に {nn1}**')
    for k in sorted(ex, key=str):
        print(f'      {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for cm in (1,):
        for R1 in (3, 4):
            for L in range(3, a.L + 1):
                run(cm, L, range(4), (2, 3, 4, 5), R1)
