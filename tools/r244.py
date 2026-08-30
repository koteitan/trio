# -*- coding: utf-8 -*-
"""**課題 (Q1) ＋ (COMP)。**

## `hlocQ`（L3 の定義の逐語）

    ∀ j, 0 < j → j < |Q| →
      (0 < entry Q 2 j → hasParent (Q.take (j+1)) 2 j)                      -- 行 2 の成分
      ∧ (entry Q 2 j = 0 → 0 < entry Q 1 j →
          ∃ y < j, le0 Q y j ∧ entry Q 1 y < entry Q 1 j ∧ (le1 Q 0 y → le1 Q 0 j))  -- 行 1

## 測るもの

    **(Q1)** 行 1 の成分が破れる列は **`hloc` も破れる（＝孤児）** か
    **(COMP-a)** 行 2 の成分・行 1 の成分の**遺伝率を別々に**
    **(COMP-b)** 行 1 の破れが「証人が無い」か「**クラス条件だけ**が合わない」か
      ⟹ ★ クラス条件を外した版（`le1` の含意を落とす）で証人が在るかを見る

## 母集団（1 行）

消費側の `Q`（`TowerP''` ＋ `d>0`）から `oper` で降りた窓。
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


def row2_ok(X, j):
    return X[j][2] == 0 or trio.parent(X[:j + 1], 2, j) is not None


def row1_wit(X, j, cls=True):
    """行 1 の成分の証人。`cls=False` ならクラス条件を外す。"""
    cj = trio.is_ancestor(X, 1, 0, j)
    out = []
    for y in range(j):
        if not trio.is_ancestor(X, 0, y, j): continue
        if not (X[y][1] < X[j][1]): continue
        if cls and trio.is_ancestor(X, 1, 0, y) and not cj: continue
        out.append(y)
    return out


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
                    LQ = len(Q)
                    for n in NS:
                        P = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = block(Q, d, e, n)
                        for j in range(1, LQ):
                            S = P + B[:j + 1]
                            lastx = len(S) - 1
                            par = trio.parent(S, srow(S, lastx), lastx)
                            if par is None: continue
                            V = [tuple(x) for x in S[par:lastx]]
                            if len(V) < 2: continue
                            for jj in range(1, len(V)):
                                # ---------- (COMP-a) 行 2 の成分 ----------
                                if V[jj][2] > 0:
                                    c['(COMP-a) 行 2 の分母'] += 1
                                    if row2_ok(V, jj): c['★ (COMP-a) 行 2 の成分 ok'] += 1
                                    else: c['⛔ (COMP-a) 行 2 の成分 破れ'] += 1
                                # ---------- 行 1 の成分 ----------
                                if V[jj][2] != 0 or V[jj][1] == 0: continue
                                c['(COMP-a) 行 1 の分母'] += 1
                                ws = row1_wit(V, jj, True)
                                if ws:
                                    c['★ (COMP-a) 行 1 の成分 ok'] += 1
                                    continue
                                c['⛔ (COMP-a) 行 1 の成分 破れ'] += 1
                                # ---------- (COMP-b) クラス条件だけか ----------
                                ws2 = row1_wit(V, jj, False)
                                if ws2: c['★ (COMP-b) クラス条件だけが合わない'] += 1
                                else:   c['⛔ (COMP-b) そもそも証人が無い'] += 1
                                # ---------- (Q1) その列は孤児か ----------
                                orph = trio.parent(V[:jj + 1], srow(V, jj), jj) is None
                                if orph: c['★ (Q1) その列は孤児（無料）'] += 1
                                else:
                                    c['⛔ (Q1) 親がいる'] += 1
                                    pp = trio.parent(V[:jj + 1], srow(V, jj), jj)
                                    c[('(Q1) 親の位置', 'V の中')] += 1
                                    if len(ex) < 5:
                                        ex.append((Q, d, e, n, j, V, jj, pp,
                                                   'クラス' if ws2 else '証人無'))
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    d2 = c['(COMP-a) 行 2 の分母']; d1 = c['(COMP-a) 行 1 の分母']
    print(f'  (COMP-a) **行 2 の成分** 分母 {d2}   ★ ok {c["★ (COMP-a) 行 2 の成分 ok"]} '
          f'({100*c["★ (COMP-a) 行 2 の成分 ok"]/max(d2,1):8.4f}%)   '
          f'⛔ 破れ {c["⛔ (COMP-a) 行 2 の成分 破れ"]}')
    print(f'  (COMP-a) **行 1 の成分** 分母 {d1}   ★ ok {c["★ (COMP-a) 行 1 の成分 ok"]} '
          f'({100*c["★ (COMP-a) 行 1 の成分 ok"]/max(d1,1):8.4f}%)   '
          f'⛔ 破れ {c["⛔ (COMP-a) 行 1 の成分 破れ"]}')
    b1 = c['⛔ (COMP-a) 行 1 の成分 破れ']
    print(f'  (COMP-b) 破れ {b1} の内訳: ★ クラス条件だけ '
          f'{c["★ (COMP-b) クラス条件だけが合わない"]} '
          f'({100*c["★ (COMP-b) クラス条件だけが合わない"]/max(b1,1):8.4f}%)   '
          f'⛔ そもそも証人が無い {c["⛔ (COMP-b) そもそも証人が無い"]} '
          f'({100*c["⛔ (COMP-b) そもそも証人が無い"]/max(b1,1):8.4f}%)')
    print(f'  ★★ (Q1) その列は孤児 {c["★ (Q1) その列は孤児（無料）"]} '
          f'({100*c["★ (Q1) その列は孤児（無料）"]/max(b1,1):8.4f}%)   '
          f'⛔ 親がいる {c["⛔ (Q1) 親がいる"]} '
          f'({100*c["⛔ (Q1) 親がいる"]/max(b1,1):8.4f}%)')
    for x in ex:
        print(f'      ⛔ (Q1) 親がいる例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} V={x[5]} '
              f'列 jj={x[6]} 親={x[7]}（{x[8]}）')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), '消費側 |R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), '★ 消費側 |R|=4 行1<3')
