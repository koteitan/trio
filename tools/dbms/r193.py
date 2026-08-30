# -*- coding: utf-8 -*-
"""(y1) の詰め —— **本当の義務は `h2(V)` で、`hz0(V)` はその十分条件にすぎない。**

`L105Cap:11366` の使い所（既に逐語で読んである）:

    block_blockParent_all' … (h2 : 0 < entry Q 2 j → hasParent (Q.take (j + 1)) 2 j)

`h2_cone`（`:11316`）は `hz0` からその `h2` を**出すための道具**。
⟹ **`hz0(V)` が破れても `h2(V)` が別ルートで成り立てば、義務は残らない。**

**測る**: `hz0(V)` が破れ、かつ「錐の中 ∧ 行 2 が正」の列を持つ `V`（= (y1a) の残差）で

    **h2(V) : ∀ j < |V|, 0 < entry V 2 j → hasParent (V.take (j+1)) 2 j**

が成り立つ割合。**成り立てば義務は消える。**

## ★ 予想（教訓 45）
> **⚠ 見積もり 60〜90%。`V` は塔の窓なので、行 2 が正の列は上に親を持ちやすい。**
> **⚠ 残る割合が真の核。**
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r183 import hr0, hz0


def h2(V, lo=1):
    """`∀ j, lo <= j < |V|, 0 < entry V 2 j → hasParent (V.take (j+1)) 2 j`。

    ⚠ **`lo = 1`**。`block_blockParent_all'`（`L105Cap:11366`）は `hj1 : 0 < j` を課すので
    義務は `j >= 1` だけ。`j = 0` は `entry V 2 0 > 0` なら**必ず**偽（1 列に親は無い）
    なので、入れると意味の無い「破れ」が出る。**最初そう測って気づいた。**"""
    for j in range(lo, len(V)):
        if V[j][2] > 0 and trio.parent(V[:j + 1], 2, j) is None:
            return False, j
    return True, None


def run(E, LS, NS, DE, nsamp, seed):
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
    for _ in range(nsamp):
        L = rnd.choice(LS)
        a = rnd.randrange(E - 1)
        Q = [(a, rnd.randrange(E), 0)] + \
            [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
             for _ in range(L - 1)]
        assert hr0(Q) and hz0(Q)
        d, e = rnd.choice(DE), rnd.choice(DE)
        for n in NS:
            for j0 in range(L):
                T = [tuple(x) for x in mTower(Q, d, e, n)]
                S = T + block(Q, d, e, n)[:j0 + 1]
                last = len(S) - 1
                par = trio.parent(S, srow(S, last), last)
                if par is None: continue
                V = [tuple(x) for x in S[par:last]]
                if len(V) < 2: continue
                c['全段'] += 1
                ok, bad = h2(V, 1)
                ok0, _ = h2(V, 0)
                if ok: c['★ h2(V) が成立（j>=1、義務なし）'] += 1
                else:  c['⚠ h2(V) が破れる（j>=1、真の核）'] += 1
                if not ok0: c['(参考) j=0 込みだと破れる'] += 1
                if V[0][2] == 0: continue
                c['hz0(V) が破れた段'] += 1
                hits = [i for i in range(1, len(V))
                        if V[i][2] > 0 and trio.is_ancestor(V, 1, 0, i)]
                if not hits: continue
                c['(y1a) の残差（錐の中に行2>0 あり）'] += 1
                if ok: c['  ★ そのうち h2(V) は成立（義務は消える）'] += 1
                else:
                    c['  ⚠⚠ h2(V) も破れる（★ 真の核）'] += 1
                    if len(ex) < 3: ex.append((Q, d, e, n, j0, V, bad))
    t = c['全段']; r = c['(y1a) の残差（錐の中に行2>0 あり）']
    print(f'### 値域<{E} |Q|∈{LS} n∈{tuple(NS)}  全段 {t}  [{time.time()-t0:.1f}s]')
    for k in ['★ h2(V) が成立（j>=1、義務なし）', '⚠ h2(V) が破れる（j>=1、真の核）',
              '(参考) j=0 込みだと破れる']:
        print(f'    {k:36s} {c[k]:8d} ({100*c[k]/max(t,1):7.3f}%)')
    print(f'    hz0(V) が破れた段 … {c["hz0(V) が破れた段"]}   '
          f'(y1a) の残差 … {r} ({100*r/max(t,1):6.3f}% of 全段)')
    for k in ['  ★ そのうち h2(V) は成立（義務は消える）', '  ⚠⚠ h2(V) も破れる（★ 真の核）']:
        print(f'      {k:40s} {c[k]:8d} ({100*c[k]/max(r,1):7.3f}% of 残差, '
              f'{100*c[k]/max(t,1):6.3f}% of 全段)')
    for x in ex: print(f'      ⚠ 真の核の例 Q={x[0]} (d,e)=({x[1]},{x[2]}) n={x[3]} j={x[4]} '
                       f'V={x[5]}  破れる列 j={x[6]}')
    print()


if __name__ == '__main__':
    run(6,  (3,4,5,6,8), (1,2,3,4,5), range(6),  12000, 221)
    print('#### 教訓 21: 箱を広げる')
    run(9,  (4,6,8,10),  (1,2,3,4,6), range(9),   8000, 223)
    run(12, (5,8,12),    (1,2,3,5,8), range(12),  5000, 225)
