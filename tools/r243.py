# -*- coding: utf-8 -*-
"""**課題 (LOCHER-a) ＋ (ADJ)。**

## `hlocQ`（L3 の §237 の逐語）

    `hlocQ X` … `∀ j >= 1` で `srow X j = 1` のとき
      `∃ y < j, le0 X y j ∧ entry X 1 y < entry X 1 j ∧ (le1 X 0 y → le1 X 0 j)`

## 測るもの

    (LOCHER-a) 窓 `V` での `hlocQ` の成立率（**分母 = `srow = 1` の列**）
    (ADJ) 証人を **`y = j-1`（隣）** に取れる割合。取れないとき **距離 `j - y`** の分布
    ⟹ ★ 距離が窓の長さより小さければ、証人は窓から落ちない

## ★ 予想

⚠ **直近で見立てを外しているので見積もりを書かない。測って答える。**
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


def witnesses(X, j):
    """`hlocQ` の証人 `y` を全部返す。"""
    out = []
    cj = trio.is_ancestor(X, 1, 0, j)
    for y in range(j):
        if not trio.is_ancestor(X, 0, y, j): continue
        if not (X[y][1] < X[j][1]): continue
        cy = trio.is_ancestor(X, 1, 0, y)
        if cy and not cj: continue          # `le1 X 0 y → le1 X 0 j` が偽
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
                            c[(n, '窓')] += 1
                            okall = True
                            for jj in range(1, len(V)):
                                if srow(V, jj) != 1: continue    # ★ 分母は srow=1 の列
                                c[(n, '★ 分母: srow=1 の列')] += 1
                                ws = witnesses(V, jj)
                                if ws:
                                    c[(n, '★ (LOCHER-a) 証人あり')] += 1
                                    # (ADJ)
                                    if (jj - 1) in ws:
                                        c[(n, '★ (ADJ) 隣 (y=j-1) で取れる')] += 1
                                    else:
                                        c[(n, '⛔ (ADJ) 隣では取れない')] += 1
                                        c[('(ADJ) 最も近い証人の距離', min(jj - max(ws), 5))] += 1
                                else:
                                    okall = False
                                    c[(n, '⛔ (LOCHER-a) 証人なし')] += 1
                                    # 「le0 祖先のうち行 1 が最小のもの」
                                    anc = [y for y in range(jj)
                                           if trio.is_ancestor(V, 0, y, jj)]
                                    mn = min((V[y][1], y) for y in anc) if anc else None
                                    if len(ex) < 6:
                                        ex.append((Q, d, e, n, j, V, jj, anc, mn,
                                                   trio.is_ancestor(V, 1, 0, jj)))
                            if okall: c[(n, '★ hlocQ(V) 全体で成立')] += 1
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    print(f'    {"n":>4s} {"窓":>9s} {"★ hlocQ 全体":>16s} {"分母(srow=1 の列)":>16s} '
          f'{"★ 証人あり":>16s} {"★ (ADJ) 隣で取れる":>18s}')
    for n in NS:
        W = c[(n, '窓')]
        if not W: continue
        D = c[(n, '★ 分母: srow=1 の列')]
        ok = c[(n, '★ (LOCHER-a) 証人あり')]
        print(f'    {n:4d} {W:9d} {c[(n,"★ hlocQ(V) 全体で成立")]:11d} ({100*c[(n,"★ hlocQ(V) 全体で成立")]/W:7.4f}%) '
              f'{D:16d} {ok:11d} ({100*ok/max(D,1):7.4f}%) '
              f'{c[(n,"★ (ADJ) 隣 (y=j-1) で取れる")]:11d} ({100*c[(n,"★ (ADJ) 隣 (y=j-1) で取れる")]/max(ok,1):7.4f}%)')
    print('    (ADJ) 隣で取れないときの最も近い証人の距離（5 は 5 以上）: ',
          dict(sorted((k[1], c[k]) for k in c
                      if isinstance(k, tuple) and k[0] == '(ADJ) 最も近い証人の距離')))
    for x in ex:
        print(f'      ⛔ 証人なしの例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} V={x[5]} '
              f'列 jj={x[6]} le0祖先={x[7]} 行1最小={x[8]} 的は錐の中={x[9]}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3,5,10), '消費側 |R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3,5), '★ 消費側 |R|=4 行1<3')
