# -*- coding: utf-8 -*-
"""**課題 (ADJ')。L3 の分解「`hlocQ` の本体は 1 つの比較」を測る。**

## L3 の分解（§238）

    ★ 錐のクラス条件 `hcls` は 2 分岐とも自動
    ⟹ `hlocQ` の本体 ＝ 「`le0` 祖先のうち**行 1 が最小**のもの `y*` が、的より小さいか」

## 測るもの

    **(ADJ'-a)** `entry S 1 y* < entry S 1 j` が成り立つ割合   ← 本体そのもの
    **(ADJ'-b)** `y*` の位置。★ `p <= y*` なら窓に残る（`le0_window` で移送）
                 ⛔ `y* < p` の割合 ＝ そのまま遺伝の破れ
    **(ADJ'-c)** `y* < p` のとき、**`V` の中で取り直せる**か
                 ＝ `[p, j)` の `le0` 祖先で行 1 が的より小さいものがあるか

## 母集団（1 行）

消費側の `Q`（`TowerP''` ＋ `d>0`）から `oper` で降りた窓 `V = S[p:last]`、
分母 ＝ `V` の中の `srow = 1` の列（絶対番地 `p+1 .. last-1`）。
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r141 import block
from r169 import domT
from r201 import dOf, eOf
from r206 import hr0


def anc0(S, j):
    return [y for y in range(j) if trio.is_ancestor(S, 0, y, j)]


def run(L, R1, VS, ZS, TS, NS, tag):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    c = Counter(); dist = Counter(); ex = []; t0 = time.time()
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
                    LQ = len(Q)
                    # ---------- (ADJ'-a) 消費側 Q そのもので本体を測る ----------
                    for j in range(1, LQ):
                        if Q[j][2] != 0 or Q[j][1] == 0: continue
                        A = anc0(Q, j)
                        c['(ADJ-a) 消費側 Q の分母'] += 1
                        if A and min(Q[y][1] for y in A) < Q[j][1]:
                            c['★ (ADJ-a) 消費側 Q で本体が真'] += 1
                    # ---------- 窓 ----------
                    for n in NS:
                        P = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = block(Q, d, e, n)
                        for j in range(1, LQ):
                            S = P + B[:j + 1]
                            lastx = len(S) - 1
                            p = trio.parent(S, srow(S, lastx), lastx)
                            if p is None: continue
                            if lastx - p < 2: continue
                            for jab in range(p + 1, lastx):
                                if S[jab][2] != 0 or S[jab][1] == 0: continue
                                c['(ADJ-a) 窓の分母'] += 1
                                A = anc0(S, jab)
                                if not A:
                                    c['⛔ (ADJ-a) le0 祖先が無い'] += 1; continue
                                m = min(S[y][1] for y in A)
                                if not (m < S[jab][1]):
                                    c['⛔ (ADJ-a) 本体が偽（y* が的以上）'] += 1; continue
                                c['★ (ADJ-a) 本体が真'] += 1
                                # ---------- (ADJ'-b) y* の位置 ----------
                                MS = [y for y in A if S[y][1] == m]
                                ys = max(MS)                 # ★ 最小行 1 のうち最も近いもの
                                dist[jab - ys] += 1
                                c['(ADJ-b) 分母'] += 1
                                if ys >= p:
                                    c['★ (ADJ-b) y* が窓に残る'] += 1
                                    continue
                                c['⛔ (ADJ-b) y* < p（窓の外）'] += 1
                                # ---------- (ADJ'-c) V の中で取り直せるか ----------
                                W = [y for y in A if y >= p and S[y][1] < S[jab][1]]
                                if W: c['★ (ADJ-c) V の中で取り直せる'] += 1
                                else:
                                    c['⛔ (ADJ-c) 取り直せない（穴）'] += 1
                                    if len(ex) < 5:
                                        ex.append((Q, d, e, n, j, p, lastx,
                                                   S[p:lastx], jab - p, sorted(A), ys))
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    da = c['(ADJ-a) 消費側 Q の分母']
    print(f'  (ADJ-a) **消費側 `Q`** 分母 {da}  ★ 本体が真 {c["★ (ADJ-a) 消費側 Q で本体が真"]} '
          f'({100*c["★ (ADJ-a) 消費側 Q で本体が真"]/max(da,1):8.4f}%)')
    dw = c['(ADJ-a) 窓の分母']
    print(f'  (ADJ-a) **窓** 分母 {dw}  ★ 本体が真 {c["★ (ADJ-a) 本体が真"]} '
          f'({100*c["★ (ADJ-a) 本体が真"]/max(dw,1):8.4f}%)  '
          f'⛔ y* が的以上 {c["⛔ (ADJ-a) 本体が偽（y* が的以上）"]}  '
          f'⛔ le0 祖先が無い {c["⛔ (ADJ-a) le0 祖先が無い"]}')
    db = c['(ADJ-b) 分母']
    print(f'  (ADJ-b) 分母 {db}  ★ **y* が窓に残る** {c["★ (ADJ-b) y* が窓に残る"]} '
          f'({100*c["★ (ADJ-b) y* が窓に残る"]/max(db,1):8.4f}%)  '
          f'⛔ **y* < p** {c["⛔ (ADJ-b) y* < p（窓の外）"]} '
          f'({100*c["⛔ (ADJ-b) y* < p（窓の外）"]/max(db,1):8.4f}%)')
    print(f'      距離 j-y* の分布: {dict(sorted(dist.items()))}')
    dc = c['⛔ (ADJ-b) y* < p（窓の外）']
    print(f'  ★★ (ADJ-c) `y* < p` の {dc} 件: ★ **V の中で取り直せる** '
          f'{c["★ (ADJ-c) V の中で取り直せる"]} '
          f'({100*c["★ (ADJ-c) V の中で取り直せる"]/max(dc,1):8.4f}%)  '
          f'⛔ **取り直せない（穴）** {c["⛔ (ADJ-c) 取り直せない（穴）"]} '
          f'({100*c["⛔ (ADJ-c) 取り直せない（穴）"]/max(dc,1):8.4f}%)')
    for x in ex:
        print(f'      ⛔ 穴の例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} p={x[5]} '
              f'V={x[7]} 窓内の列={x[8]} le0祖先(絶対)={x[9]} y*={x[10]}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), '消費側 |R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), '★ 消費側 |R|=4 行1<3')
