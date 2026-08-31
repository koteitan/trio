# -*- coding: utf-8 -*-
"""**課題 (v1)-(v3) ＋ (u1')-(u3')（L3 / team-lead の依頼）—— `srow` 別と、実際の親の位置。**

**場面**: `S_j = mTower Q d e n ++ Bn.take (j+1)`。復活 ＝ 親が `n*|Q|` 未満。
足す列 `Bn[j]` の `srow` は行 2 で決まる（塔は行 2 を動かさない）:
**`srow = 2` ⟺ `entry Q 2 j > 0`**。

## ★ 予想を先に書く（教訓 45）＋ 見積もり（L3 の §105.2）

**(v1)** §142（`L105Cap:10246` `block_blockParent_of_cone`）の結論は **行 1 の親**。
⟹ **`srow = 1` なら「要る親」＝「行 1 の親」なので §142 が効く。**
> **予想: `srow = 1` ∧ 錐の中 の復活は **0%**。**
> **⚠ 反例の形: 「`srow = 1` ∧ 錐の中なのに復活する」⟹ §142 の射程に本物の穴。**
> **⚠ 見積もり: 0 〜 5%**（team-lead の読みが当たれば 0%）。

**(u1')(u2')** §R156 で `n = 2..7` すべてで戻り = 1 が 100%。
> **予想: `e` を振っても動かない。見積もり: 戻り >= 2 は 0 〜 2%。**

**(u3') ★** `k* ＝ `entry Q 1 0 + e*k < 足す列の行 1` を満たす最大の `k`（`k ∈ 0..n-1`）。
実際の `k = n − 1`（100%）、`k* == k` は 0.10 〜 0.20%（§R156）。
> **予想: `k − k*` は **`n` とともに増える**（`k = n−1` が動き、`k*` は `Q,e,j` でほぼ決まるため）。**
> **⟹ **有界でない** ⟹ L3 の下界では窓が `n` とともに伸びる。**
> **⚠ 見積もり: `k − k*` の最大値が `n` に比例して増える（`n=7` で 5 以上）。**

**箱と単位**: 単位 `(Q,d,e,n,j)`。箱 = 行0<4, 行1<3, 行2<=1、`|Q| = 3..4`、
`d,e ∈ 0..3`、**`n ∈ 2..7`**。母集団 = 根が狭義最浅。**`W` 所属は判定しない（明記）。**
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
                            sr = srow(S, last)
                            cone = le1_root(Q, j)
                            key = (sr, '錐の中' if cone else '錐の外')
                            par = trio.parent(S, sr, last)
                            c[('(v3) srow 別の分母', sr)] += 1
                            c[(key, '分母')] += 1
                            if par is None:
                                c[(key, '孤児')] += 1
                                continue
                            if par >= n * L:
                                c[(key, '同ブロック')] += 1
                                continue
                            c[(key, '★ 復活')] += 1
                            k = par // L
                            c[('(u1\') 戻り', n - k)] += 1
                            c[('(u2\') e 別の戻り', 'e=0' if e == 0 else 'e>=1', n - k)] += 1
                            ks = [kk for kk in range(n) if Q[0][1] + e * kk < S[last][1]]
                            kst = max(ks) if ks else -1
                            c[('(u3\') k - k*', min(k - kst, 8))] += 1
                            c[('(u3\') n 別の k-k* 最大', n)] = max(
                                c.get(('(u3\') n 別の k-k* 最大', n), 0), k - kst)
                            if sr == 1 and cone:
                                ex.setdefault('★★ (v1) 破れ: srow=1 ∧ 錐の中で復活',
                                              (Q, d, e, n, j, par, k))
    print(f'### 行2<={cm} |Q|={L}  [{time.time()-t0:.1f}s]')
    print('  **(v3) `srow` 別の分母**: ', dict(sorted((k[1], c[k]) for k in c
                                            if isinstance(k, tuple) and k[0] == '(v3) srow 別の分母')))
    print('  **(v1)(v2) `srow` × 錐 別の復活率**:')
    for sr in (0, 1, 2):
        for cn in ('錐の中', '錐の外'):
            tot = c[((sr, cn), '分母')]
            if not tot:
                continue
            rv = c[((sr, cn), '★ 復活')]
            mark = '  ★★ §142 の射程' if (sr == 1 and cn == '錐の中') else ''
            print(f'      srow={sr} {cn}: 分母 {tot:9d}  孤児 {c[((sr,cn),"孤児")]:9d}  '
                  f'同ブロック {c[((sr,cn),"同ブロック")]:9d}  **復活 {rv:8d} ({100*rv/tot:6.3f}%)**{mark}')
    print('  **(u1\') 戻り**: ', dict(sorted((k[1], c[k]) for k in c
                                       if isinstance(k, tuple) and k[0] == "(u1') 戻り")))
    print('  **(u2\') `e` 別の戻り**: ', dict(sorted(((k[1], k[2]), c[k]) for k in c
                                            if isinstance(k, tuple) and len(k) == 3 and k[0] == "(u2') e 別の戻り")))
    print('  **(u3\') `k − k*` の分布**: ', dict(sorted((k[1], c[k]) for k in c
                                            if isinstance(k, tuple) and k[0] == "(u3') k - k*")))
    print('  **(u3\') `n` 別の `k − k*` の最大**: ', dict(sorted((k[1], c[k]) for k in c
                                                   if isinstance(k, tuple) and k[0] == "(u3') n 別の k-k* 最大")))
    for k in sorted(ex):
        print(f'      {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for cm in (1,):
        for L in range(3, a.L + 1):
            run(cm, L, range(4), (2, 3, 4, 5, 6, 7))
