# -*- coding: utf-8 -*-
"""(z3) の詰め —— 破れた `V` が**行き止まり**なのはなぜか。

r202: 深さ 1・2 で `h2cone(V)` が破れた状態（重複除去 54 個）から**1 段も降りられない**。
⟹ **深さ 3+ の 0% はビームの副作用ではない。**

**⚠ 理由で L3 の対応が変わる:**

    **(i) 親が無い** ⟹ `mTowerClosed_of_snocStepPar` が `snoc_orphan_W` で内部処理（**既に無料**）
    **(ii) `|V| = 1`** ⟹ `MTowerSingle`（`L105Cap` §81、緑）だが**接頭辞つきが未着手**（L3 §191.2）
    **(iii) その他**
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r141 import block
from r169 import domT
from r171 import step_det
from r195 import h2cone
from r201 import dOf, eOf


def run(L, R1, VS, ZS, TS, NS):
    COL = [(a, b, c) for a in range(1, 4) for b in range(R1) for c in (0, 1)]
    bad = set()
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
                    st = {(tuple(Q), dOf(M), eOf(M))}
                    for dep in (1, 2):
                        nxt = set()
                        for (X, dd, ee) in st:
                            for n in NS:
                                for j in range(len(X)):
                                    r = step_det(list(X), dd, ee, n, j)
                                    if r is None or len(r[0]) < 2: continue
                                    nxt.add((tuple(r[0]), r[1], r[2]))
                                    if h2cone(list(r[0])):
                                        bad.add((tuple(r[0]), r[1], r[2]))
                        st = nxt
    c = Counter()
    for (X, dd, ee) in bad:
        c['破れた状態'] += 1
        for n in NS:
            for j in range(len(X)):
                c['(n,j) の組'] += 1
                T = [tuple(x) for x in mTower(list(X), dd, ee, n)]
                S = T + block(list(X), dd, ee, n)[:j + 1]
                last = len(S) - 1
                par = trio.parent(S, srow(S, last), last)
                if par is None:
                    c['(i) 親が無い（snoc_orphan_W が内部処理。既に無料）'] += 1
                elif last - par < 2:
                    c[f'(ii) |V| = {last - par}（MTowerSingle。接頭辞つきが未着手）'] += 1
                else:
                    c['(iii) その他（降りられる）'] += 1
    t = c['(n,j) の組']
    print(f'### |R|={L} 行1<{R1}  破れた状態 {c["破れた状態"]}  `(n,j)` の組 {t}')
    for k in sorted(x for x in c if x.startswith('(')):
        print(f'    {k:52s} {c[k]:7d} ({100*c[k]/max(t,1):6.2f}%)')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3))
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3,4))
