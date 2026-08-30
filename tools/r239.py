# -*- coding: utf-8 -*-
"""**課題 (FORMULA) —— H12 の式の検算。**

## H12 の式（逐語）

    `outOfCone_becomes_blocker_iff`:
      **的がブロッカー ⟺ `entry Q 1 j <= entry Q 1 p + e*k`**
      （`p` = 窓の根の `Q` 内位置、`k` = 窓の根のブロック番号、`e` = 行 1 のリフト量）
    ⟹ **予算 = `e*k`、距離 = `entry Q 1 j − entry Q 1 p`**

## 測るもの

    (FORMULA-a) ★ 破れる段で「**窓の根が錐の中**」か（H12 の予測: 100%）
    (FORMULA-b) ★ **距離と予算**を並べ、**破れ ⟺ 距離 <= 予算**か
    (FORMULA-c) **`k` の分布**が深さでどう動くか

## 母集団（1 行で再掲）

消費側の `Q`（`TowerP''` ＋ `d>0` ＋ `h1out(Q)` 成立）から **`h1out` を保つ窓だけ**降りた段。
ビーム幅つき（明記）。
"""
import sys, itertools, random, time
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
from r234 import h1out_bad


def run(L, R1, VS, ZS, TS, NS, depth, beam, seed, tag):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt)
        if srow(R, len(R) - 1) != 2: continue
        if not any(domT(R, m) for m in range(4)): continue
        for v in VS:
            for z in ZS:
                if trio.parent([(0, v, z)] + R, 2, len(R)) is None: continue
                for t in TS:
                    M = [tuple(x) for x in Lift1([(0, v, z)] + R, t)]
                    Q0 = M[:-1]
                    if len(Q0) < 2: continue
                    d, e = dOf(M), eOf(M)
                    if not (d > 0 and hr0(Q0) and Q0[0][2] == 0): continue
                    if h1out_bad(Q0): continue
                    front = [(tuple(Q0), d, e)]
                    for dep in range(1, depth + 1):
                        nxt = []
                        for (Xt, dd, ee) in front:
                            X = list(Xt); LX = len(X)
                            for n in NS:
                                T = [tuple(y) for y in mTower(X, dd, ee, n)]
                                B = block(X, dd, ee, n)
                                for j in range(LX):
                                    S = T + B[:j + 1]
                                    lastx = len(S) - 1
                                    par = trio.parent(S, srow(S, lastx), lastx)
                                    if par is None: continue
                                    V = [tuple(y) for y in S[par:lastx]]
                                    if len(V) < 2: continue
                                    bad = h1out_bad(V)
                                    k = par // LX          # 窓の根のブロック番号
                                    p = par % LX           # 窓の根の `X` 内位置
                                    incone = trio.is_ancestor(X, 1, 0, p)
                                    c[(dep, '★ 分母: 段')] += 1
                                    c[(dep, '(FORMULA-c) k', min(k, 4))] += 1
                                    if bad:
                                        c[(dep, '⛔ 破れ')] += 1
                                        if incone: c[(dep, '★ (FORMULA-a) 窓の根が錐の中')] += 1
                                        else:
                                            c[(dep, '⛔ (FORMULA-a) 窓の根が錐の外')] += 1
                                            if len(ex) < 4:
                                                ex.append(('a', X, dd, ee, n, j, par, p, k, V))
                                        # (FORMULA-b) 距離 vs 予算
                                        for jb in bad:
                                            q = par + jb
                                            pj = q % LX
                                            dist = X[pj][1] - X[p][1]
                                            budget = ee * k
                                            c[(dep, '(FORMULA-b) 破れの組')] += 1
                                            if dist <= budget:
                                                c[(dep, '★ (FORMULA-b) 距離 <= 予算')] += 1
                                            else:
                                                c[(dep, '⛔ (FORMULA-b) 距離 > 予算')] += 1
                                                if len(ex) < 8:
                                                    ex.append(('b', X, dd, ee, n, j, par,
                                                               dist, budget, V))
                                    else:
                                        nxt.append((tuple(V), 0, 0))
                                        # 破れなかった段でも距離 vs 予算（対照）
                                        for jj in range(1, len(V)):
                                            if trio.is_ancestor(V, 1, 0, jj): continue
                                            if V[jj][2] != 0 or V[jj][1] == 0: continue
                                            q = par + jj; pj = q % LX
                                            c[(dep, '対照: 破れない組')] += 1
                                            if X[pj][1] - X[p][1] <= ee * k:
                                                c[(dep, '⚠ 対照: 距離 <= 予算なのに破れない')] += 1
                        if not nxt: break
                        # `(d0,e0)` を正しく取り直す
                        nxt2 = []
                        for (Vt, _, _) in nxt:
                            nxt2.append((Vt, 0, 0))
                        rnd.shuffle(nxt2); front = nxt2[:beam]
                        # ⚠ `(d,e)` を 0 にすると次段が別物になるので深さ 1 のみ有効
                        break
    print(f'### {tag} ビーム{beam}  [{time.time()-t0:.1f}s]   ⚠ 深さ 1 のみ有効')
    for dep in range(1, 2):
        D = c[(dep, '★ 分母: 段')]
        if not D: continue
        bd = c[(dep, '⛔ 破れ')]
        print(f'  深さ {dep}: ★ 分母 {D}   ⛔ 破れ {bd} ({100*bd/D:7.4f}%)')
        print(f'      ★ (FORMULA-a) 窓の根が錐の中 {c[(dep,"★ (FORMULA-a) 窓の根が錐の中")]:8d} '
              f'({100*c[(dep,"★ (FORMULA-a) 窓の根が錐の中")]/max(bd,1):8.4f}%)   '
              f'⛔ 錐の外 {c[(dep,"⛔ (FORMULA-a) 窓の根が錐の外")]}')
        bb = c[(dep, '(FORMULA-b) 破れの組')]
        print(f'      (FORMULA-b) 破れの組 {bb}   ★ 距離 <= 予算 '
              f'{c[(dep,"★ (FORMULA-b) 距離 <= 予算")]:8d} '
              f'({100*c[(dep,"★ (FORMULA-b) 距離 <= 予算")]/max(bb,1):8.4f}%)   '
              f'⛔ 距離 > 予算 {c[(dep,"⛔ (FORMULA-b) 距離 > 予算")]}')
        cd = c[(dep, '対照: 破れない組')]
        print(f'      対照: 破れない組 {cd}   ⚠ 距離 <= 予算なのに破れない '
              f'{c[(dep,"⚠ 対照: 距離 <= 予算なのに破れない")]} '
              f'({100*c[(dep,"⚠ 対照: 距離 <= 予算なのに破れない")]/max(cd,1):8.4f}%)')
        print('      (FORMULA-c) `k` の分布: ',
              dict(sorted((kk[2], c[kk]) for kk in c
                          if len(kk) == 3 and kk[0] == dep and kk[1] == '(FORMULA-c) k')))
    for x in ex: print('      ⛔ 例', x)
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 1, 200, 991, '消費側 |R|=3 行1<3')
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), 1, 200, 993, '★ 消費側 |R|=3 行1<5')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 1, 200, 995, '★ 消費側 |R|=4 行1<3')
