# -*- coding: utf-8 -*-
"""**(CONE) ＋ (CONE1)。**

## ⚠ 主語（どの列の中で錐を見たか）

    `Sj = mTower Q d e n ++ block.take (j+1)`、`br = len(mTower ...)`（ブロックの根）
    `V  = Sj[p:last]`（`p` ＝ 窓の根 ＝ ブロッカー）
    **`Q` の錐**     :⟺ `le1 Q 0 l`      ← **`Q` の中**で見る
    **ブロックの錐** :⟺ `le1 Sj 0' l'`   ← **ブロックだけ**を切り出した中で見る
    **`V` の錐**     :⟺ `le1 V 0 t`      ← **窓 `V` の中**で見る

## 測るもの

    (CONE-a) `V` の列で **`¬ le1 V 0 t`**（窓の錐の外）の割合。**分母 ＝ `V` の全列**
    (CONE-b) ★ **`Q` で錐の中 ⟹ `V` で錐の外**（本体）
    (CONE-c) 逆（`Q` で錐の外 ⟹ `V` で錐の中）
    (CONE1)  残差（`hlocQ(Q)` 真かつ `hlocQ(V)` 偽）で、**的が `V` の錐の中か**
    ⚠ (TAUT) **「`V` の錐の中 ⟹ `hloc` が立つ」**を独立に検算
             ⟹ ★ これが 100% なら **(CONE1) は同語反復**（測る前から 0%）
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r141 import block
from r169 import domT
from r201 import dOf, eOf
from r206 import hr0
from r247 import row1_wit
from r248 import hlocQ


def hloc_col(X, t):
    """`hlocQ` の列 `t` の成分。"""
    if X[t][2] > 0: return trio.parent(X[:t + 1], 2, t) is not None
    if X[t][1] == 0: return True
    return bool(row1_wit(X, t))


def run(L, R1, VS, ZS, TS, NS, tag):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    c = Counter(); ex = []; t0 = time.time()
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt)
        if srow(R, len(R) - 1) != 2: continue
        if not any(domT(R, m) for m in range(4)): continue
        for v in VS:
            for z in ZS:
                if trio.parent([(0, v, z)] + R, 2, len(R)) is None: continue
                for t in TS:
                    M = [tuple(x) for x in Lift1([(0, v, z)] + R, t)]
                    Q = M[:-1]
                    if len(Q) < 2: continue
                    d, e = dOf(M), eOf(M)
                    if not (d > 0 and hr0(Q) and Q[0][2] == 0): continue
                    hq = hlocQ(Q)
                    coneQ = [trio.is_ancestor(Q, 1, 0, l) for l in range(len(Q))]
                    for n in NS:
                        S0 = [tuple(x) for x in mTower(Q, d, e, n)]
                        Bk = [tuple(x) for x in block(Q, d, e, n)]
                        br = len(S0)
                        for j in range(1, len(Q)):
                            Sj = S0 + Bk[:j + 1]
                            lastx = len(Sj) - 1
                            p = trio.parent(Sj, srow(Sj, lastx), lastx)
                            if p is None or lastx - p < 2: continue
                            V = [tuple(x) for x in Sj[p:lastx]]
                            # ブロック単体での錐
                            Bp = Bk[:j + 1]
                            coneB = [trio.is_ancestor(Bp, 1, 0, l)
                                     for l in range(len(Bp))]
                            for tt in range(1, len(V)):
                                cv = trio.is_ancestor(V, 1, 0, tt)
                                c['(CONE-a) 分母（V の全列）'] += 1
                                if not cv: c['★ (CONE-a) V の錐の外'] += 1
                                # ---------- (TAUT) ----------
                                if cv:
                                    c['(TAUT) V の錐の中'] += 1
                                    if hloc_col(V, tt): c['★ (TAUT) hloc が立つ'] += 1
                                    else: c['⛔ (TAUT) 錐の中なのに hloc が偽'] += 1
                                # ---------- (CONE-b)(CONE-c) ----------
                                ab = p + tt
                                if ab < br: continue          # 塔の中の列は対応なし
                                l = ab - br
                                c['(CONE-b) 分母（ブロック内の列）'] += 1
                                cq = coneQ[l]
                                if cq and not cv:
                                    c['★★ (CONE-b) Q で錐の中 ⟹ V で錐の外'] += 1
                                    if len(ex) < 6:
                                        ex.append((Q, d, e, n, j, p - br, V, tt, l,
                                                   coneB[l]))
                                if (not cq) and cv:
                                    c['★ (CONE-c) Q で錐の外 ⟹ V で錐の中'] += 1
                                if cq: c['   Q で錐の中'] += 1
                                if coneB[l] != cq: c['⛔ ブロックの錐 ≠ Q の錐'] += 1
                                if coneB[l] and not cv:
                                    c['★ ブロックで錐の中 ⟹ V で錐の外'] += 1
                            # ---------- (CONE1) 残差 ----------
                            if not hq or hlocQ(V): continue
                            for tt in range(1, len(V)):
                                if hloc_col(V, tt): continue
                                c['(CONE1) 残差の破れ列'] += 1
                                if trio.is_ancestor(V, 1, 0, tt):
                                    c['⛔ (CONE1) 的が V の錐の中'] += 1
                                else:
                                    c['★ (CONE1) 的が V の錐の外'] += 1
    def pc(a, b): return f'{a} ({100*a/max(b,1):8.4f}%)'
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    da = c['(CONE-a) 分母（V の全列）']
    print(f'  (CONE-a) 分母 {da}  ★ **V の錐の外** {pc(c["★ (CONE-a) V の錐の外"], da)}')
    db = c['(CONE-b) 分母（ブロック内の列）']; dq = c['   Q で錐の中']
    print(f'  (CONE-b) ブロック内の列 {db}（うち Q で錐の中 {dq}）  '
          f'★★ **Q で錐の中 ⟹ V で錐の外** '
          f'{pc(c["★★ (CONE-b) Q で錐の中 ⟹ V で錐の外"], dq)}')
    print(f'  (CONE-c) **Q で錐の外 ⟹ V で錐の中** '
          f'{pc(c["★ (CONE-c) Q で錐の外 ⟹ V で錐の中"], db - dq)}   '
          f'⛔ ブロックの錐 ≠ Q の錐 {c["⛔ ブロックの錐 ≠ Q の錐"]}   '
          f'★ ブロックで錐の中 ⟹ V で錐の外 {c["★ ブロックで錐の中 ⟹ V で錐の外"]}')
    dt = c['(TAUT) V の錐の中']
    print(f'  ⚠ (TAUT) V の錐の中 {dt}  ★ **hloc が立つ** {pc(c["★ (TAUT) hloc が立つ"], dt)}  '
          f'⛔ 錐の中なのに偽 {c["⛔ (TAUT) 錐の中なのに hloc が偽"]}')
    d1 = c['(CONE1) 残差の破れ列']
    print(f'  ★★ (CONE1) 残差の破れ列 {d1}  ⛔ **的が V の錐の中** '
          f'{pc(c["⛔ (CONE1) 的が V の錐の中"], d1)}  '
          f'★ 的が V の錐の外 {pc(c["★ (CONE1) 的が V の錐の外"], d1)}')
    for x in ex[:4]:
        print(f'      ★★ (CONE-b) 例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} '
              f'窓の根(ブロック内)={x[5]} V={x[6]} t={x[7]} ⟹ Q の列 {x[8]}'
              f'（ブロックの錐={x[9]}）')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2), '|R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2), '★ |R|=4 行1<3')
    run(4, 4, (0,1,2,3), (0,1), (0,1,2), (1,2), '★★ |R|=4 行1<4')
    run(5, 3, (0,1,2), (0,1), (0,1), (1,2), '★★ |R|=5 行1<3')
