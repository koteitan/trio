# -*- coding: utf-8 -*-
"""**課題 (s9) —— (s7) の (D)「親が `A'` の中」で、L3 の 3 本の**前提**はどうなっているか。**

## L3 の 3 本（team-lead が逐語で渡した形）

```lean
no_nextrel0_from_prefix (hy : y < A.length) (hj1 : 0 < j1)
    (hmin : entry T 0 0 < entry T 0 j1) : ¬ nextrel0 (A ++ T) y (A.length + j1)
no_nextrel1_from_prefix (hy) (hle0 : le0 (A ++ T) A.length (A.length + j1))
    (hmin : entry T 1 0 < entry T 1 j1) : ¬ nextrel1 (A ++ T) y (A.length + j1)
no_nextrel2_from_prefix (hy) (hle1 …) (hmin : entry T 2 0 < entry T 2 j1) : ¬ nextrel2 …
```

## ⚠ 先に読み直した（測る前に）

(s7) の的は `T2 = mTower V d0 e0 m ++ B'.take (j2+1)` の添字 **`j1 = m*|V| + j2`**。
`m >= 1` なので **`j1 = 0` は起きない** ⟹ **(s9a) の答えは「`j1 >= 1` が 100%」のはず**。
⟹ ★ ですから破れるのは **`hmin`（その行の最小性）が偽**のときのはず。**そこを測る。**

## 測るもの（(D) の件数を分母に）

    (s9a) `j1 = 0` か `j1 >= 1` か
    (s9c) 親が選ばれた**行**（0 / 1 / 2）
    **★ (s9b') その行の `hmin`（`entry T2 (行) 0 < entry T2 (行) j1`）が成り立っているか**
      ⟹ ⛔ **成り立っているのに親が接頭辞にいるなら L3 の定理が誤り。至急報告。**
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


def ent(S, i, j):
    p = S[j] if j < len(S) else (0, 0, 0)
    return p[0] if i == 0 else (p[1] if i == 1 else p[2])


def run(L, R1, VS, ZS, TS, NS, MS, tag):
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
                            S1 = P + B[:j + 1]; last1 = len(S1) - 1
                            par1 = trio.parent(S1, srow(S1, last1), last1)
                            if par1 is None or par1 < len(P): continue
                            p = par1 - len(P)
                            if p >= j: continue
                            A2 = P + B[:p]
                            V = [tuple(x) for x in S1[par1:last1]]
                            if len(V) < 2: continue
                            i1 = srow(S1, last1)
                            d0 = (S1[last1][0] - S1[par1][0]) if i1 > 0 else 0
                            e0 = (S1[last1][1] - S1[par1][1]) if i1 > 1 else 0
                            LV = len(V)
                            for m in MS:
                                T2 = ([tuple(x) for x in mTower(V, d0, e0, m)]
                                      + block(V, d0, e0, m))
                                for j2 in range(LV):
                                    Tcut = T2[:m * LV + j2 + 1]
                                    S2 = A2 + Tcut
                                    lx = len(S2) - 1
                                    row = srow(S2, lx)
                                    par2 = trio.parent(S2, row, lx)
                                    if par2 is None or par2 >= len(A2): continue
                                    # ★ ここから (D) だけ
                                    j1 = m * LV + j2
                                    c['★ 分母: (D) の件数'] += 1
                                    c[('(s9a) j1', '0' if j1 == 0 else '>=1')] += 1
                                    c[('(s9c) 親の行', row)] += 1
                                    hmin = ent(Tcut, row, 0) < ent(Tcut, row, j1)
                                    c[('(s9b) hmin', row, hmin)] += 1
                                    if hmin and len(ex) < 5:
                                        ex.append((Q, d, e, n, j, p, V, d0, e0, m, j2,
                                                   row, par2, ent(Tcut, row, 0),
                                                   ent(Tcut, row, j1)))
    D = c['★ 分母: (D) の件数']
    print(f'### {tag}   ★ 分母（(D) 親が `A2` の中）{D}  [{time.time()-t0:.1f}s]')
    print('    (s9a) `j1`: ', dict((k[1], c[k]) for k in c
                                   if isinstance(k, tuple) and k[0] == '(s9a) j1'))
    print('    (s9c) 親の行: ', dict(sorted((k[1], c[k]) for k in c
                                       if isinstance(k, tuple) and k[0] == '(s9c) 親の行')))
    print('    ★★ (s9b) その行の `hmin`（entry T 行 0 < entry T 行 j1）:')
    for row in (0, 1, 2):
        tt = c[('(s9b) hmin', row, True)] + c[('(s9b) hmin', row, False)]
        if not tt: continue
        print(f'        行 {row}: 分母 {tt:8d}   ⛔ hmin 成立（＝ L3 の定理が使えるのに破れた）'
              f' {c[("(s9b) hmin", row, True)]:8d} ({100*c[("(s9b) hmin",row,True)]/tt:8.4f}%)'
              f'   ★ hmin 不成立（定理の射程外）{c[("(s9b) hmin", row, False)]:8d} '
              f'({100*c[("(s9b) hmin",row,False)]/tt:8.4f}%)')
    for x in ex:
        print(f'      ⛔⛔ hmin 成立なのに破れた例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} '
              f'p={x[5]} V={x[6]} (d0,e0)=({x[7]},{x[8]}) m={x[9]} j2={x[10]} '
              f'親の行={x[11]} 親={x[12]} entry T 行 0={x[13]} entry T 行 j1={x[14]}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), (1,2,3), '消費側 |R|=3 行1<3')
    run(3, 5, (0,1,2), (0,1), (0,1,2), (1,2), (1,2,3), '★ 消費側 |R|=3 行1<5')
