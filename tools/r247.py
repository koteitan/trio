# -*- coding: utf-8 -*-
"""**(Q1') / (Q2) / (FIN) / (ROW2) / (CONS)。**

## ⚠ (Q1') 主語の訂正

§R228 / §R229 で私が測った「孤児」は

    trio.parent(V[:jj+1], srow(V,jj), jj) is None        ← **窓 `V` の中**

です。⟹ ⛔ **(i) ブロック / (ii) 塔＋ブロック / (iii) 全体 の**どれでもありません**。
⟹ ★ ですから **`snoc_orphan_W` が使えるとは言えません**。⟹ ここで測り直します。

    **(0)** 窓 `V.take (jj+1)` の中              ← 私が測ったもの（＝ `hloc V` そのもの）
    **(ii)** `mTower ++ block.take (j+1)` の中   ← 塔＋ブロック（**帰納の実際の接頭辞を含む**）
    **(iii)** `A ++ 塔 ++ ブロック` の中          ← `A` を前に付けたもの

## `A` の対照（★ **破れが出る形**として設計）

    `A_ok`  … `rsum` を満たす（行 0 が `entry S 0 0` 以上）
    `A_bad` … ⛔ **`rsum` を破る**（行 0 が `entry S 0 0` より小さい列を含む）
              ⟹ ★ **`A` が親を供給できるとしたらこの形**のはず（§R226）
"""
import sys, itertools, time, random
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
from r245 import anc0

random.seed(20260830)
A_OK  = [[(5, 0, 0)], [(3, 1, 0), (4, 2, 0)], [(9, 4, 1)]]                 # rsum を満たす
A_BAD = [[(0, 0, 0)], [(0, 5, 0), (0, 9, 1)], [(0, 0, 0), (0, 3, 0)]]      # ⛔ rsum を破る


def orphan_in(S, jab):
    return trio.parent(S[:jab + 1], srow(S, jab), jab) is None


def orphan_with(A, S, jab):
    T = [tuple(x) for x in A] + S
    k = len(A) + jab
    return trio.parent(T[:k + 1], srow(T, k), k) is None


def row1_wit(X, j):
    cj = trio.is_ancestor(X, 1, 0, j)
    return [y for y in range(j)
            if trio.is_ancestor(X, 0, y, j) and X[y][1] < X[j][1]
            and not (trio.is_ancestor(X, 1, 0, y) and not cj)]


def run(L, R1, VS, ZS, TS, NS, tag):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    c = Counter(); ex = {}; t0 = time.time()
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
                    # ---------- (CONS) 消費側 Q での hlocQ ----------
                    for j in range(1, len(Q)):
                        if Q[j][2] > 0:
                            c['(CONS) 行2 分母'] += 1
                            if trio.parent(Q[:j+1], 2, j) is not None: c['★ (CONS) 行2 ok'] += 1
                        elif Q[j][1] > 0:
                            c['(CONS) 行1 分母'] += 1
                            if row1_wit(Q, j): c['★ (CONS) 行1 ok'] += 1
                    for n in NS:
                        S = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = block(Q, d, e, n)
                        for j in range(1, len(Q)):
                            Sj = S + B[:j + 1]
                            lastx = len(Sj) - 1
                            p = trio.parent(Sj, srow(Sj, lastx), lastx)
                            if p is None or lastx - p < 2: continue
                            V = [tuple(x) for x in Sj[p:lastx]]
                            # ================= (FIN) t = 1 =================
                            if V[1][2] == 0 and V[1][1] > 0:
                                out = not trio.is_ancestor(V, 1, 0, 1)
                                for lab, ok in (('全体', True), ('錐の外', out),
                                                ('|V|=2', len(V) == 2)):
                                    if not ok: continue
                                    c[f'(FIN) {lab} 分母'] += 1
                                    if V[0][1] < V[1][1]: c[f'★ (FIN) {lab} 根が証人'] += 1
                                if not (V[0][1] < V[1][1]):
                                    c['⛔ (FIN) 破れ'] += 1
                                    jab = p + 1
                                    if orphan_in(V, 1):   c['★ (FIN-b) (0)窓で孤児'] += 1
                                    if orphan_in(Sj, jab): c['★ (FIN-b) (ii)塔+ブロックで孤児'] += 1
                                    else:                  c['⛔ (FIN-b) (ii)で親がいる'] += 1
                                    if all(orphan_with(A, Sj, jab) for A in A_OK):
                                        c['★ (FIN-b) (iii)A_ok で孤児'] += 1
                                    if all(orphan_with(A, Sj, jab) for A in A_BAD):
                                        c['★ (FIN-b) (iii)A_bad で孤児'] += 1
                                    else: c['⛔ (FIN-b) (iii)A_bad が親を供給'] += 1
                                    ex.setdefault('FIN', []).append((Q, d, e, n, j, V))
                            # ============ (Q1')(Q2)(ROW2) 全列 ============
                            for jj in range(1, len(V)):
                                jab = p + jj
                                if V[jj][2] > 0:
                                    c['(ROW2) 分母'] += 1
                                    if trio.parent(V[:jj+1], 2, jj) is not None:
                                        c['★ (ROW2) 行2 成分 ok'] += 1; continue
                                    c['⛔ (ROW2) 行2 成分 破れ'] += 1
                                    if orphan_in(Sj, jab): c['★ (Q2) (ii)で孤児'] += 1
                                    else:                  c['⛔ (Q2) (ii)で親がいる'] += 1
                                    if all(orphan_with(A, Sj, jab) for A in A_BAD):
                                        c['★ (Q2) (iii)A_bad で孤児'] += 1
                                    else: c['⛔ (Q2) (iii)A_bad が親を供給'] += 1
                                    ex.setdefault('ROW2', []).append((Q, d, e, n, j, V, jj))
                                    continue
                                if V[jj][1] == 0: continue
                                if row1_wit(V, jj): continue
                                c['⛔ (Q1) 行1 成分 破れ'] += 1
                                if orphan_in(Sj, jab): c['★ (Q1甲) (ii)で孤児'] += 1
                                else:                  c['⛔ (Q1甲) (ii)で親がいる'] += 1
                                if all(orphan_with(A, Sj, jab) for A in A_BAD):
                                    c['★ (Q1甲) (iii)A_bad で孤児'] += 1
                                else: c['⛔ (Q1甲) (iii)A_bad が親を供給'] += 1
    def pc(a, b): return f'{a} ({100*a/max(b,1):8.4f}%)'
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    for lab in ('全体', '錐の外', '|V|=2'):
        dn = c[f'(FIN) {lab} 分母']
        print(f'  (FIN-a/c) **{lab}** 分母 {dn}  ★ 根が証人 {pc(c[f"★ (FIN) {lab} 根が証人"], dn)}')
    bf = c['⛔ (FIN) 破れ']
    print(f'  (FIN-b) 破れ {bf}: (0)窓 {pc(c["★ (FIN-b) (0)窓で孤児"], bf)}  '
          f'**(ii)塔+ブロック** {pc(c["★ (FIN-b) (ii)塔+ブロックで孤児"], bf)}  '
          f'(iii)A_ok {pc(c["★ (FIN-b) (iii)A_ok で孤児"], bf)}  '
          f'**(iii)A_bad** {pc(c["★ (FIN-b) (iii)A_bad で孤児"], bf)}')
    b1 = c['⛔ (Q1) 行1 成分 破れ']
    print(f'  (Q1甲) 行1 の破れ {b1}: **(ii)** {pc(c["★ (Q1甲) (ii)で孤児"], b1)}  '
          f'**(iii)A_bad** {pc(c["★ (Q1甲) (iii)A_bad で孤児"], b1)}')
    dr = c['(ROW2) 分母']; br = c['⛔ (ROW2) 行2 成分 破れ']
    print(f'  (ROW2) 分母 {dr}  ★ ok {pc(c["★ (ROW2) 行2 成分 ok"], dr)}  ⛔ 破れ {br}')
    print(f'  (Q2) 行2 の破れ {br}: **(ii)** {pc(c["★ (Q2) (ii)で孤児"], br)}  '
          f'**(iii)A_bad** {pc(c["★ (Q2) (iii)A_bad で孤児"], br)}')
    print(f'  (CONS) 消費側 `Q`: 行2 {pc(c["★ (CONS) 行2 ok"], c["(CONS) 行2 分母"])}'
          f'/{c["(CONS) 行2 分母"]}  行1 {pc(c["★ (CONS) 行1 ok"], c["(CONS) 行1 分母"])}'
          f'/{c["(CONS) 行1 分母"]}')
    for k in ('FIN', 'ROW2'):
        for x in ex.get(k, [])[:3]:
            print(f'      ⛔ {k} 例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} V={x[5]}'
                  + (f' jj={x[6]}' if len(x) > 6 else ''))
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2), '|R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2), '★ |R|=4 行1<3')
