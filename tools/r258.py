# -*- coding: utf-8 -*-
"""★★★★★ **(C4 ＋ hz0(V)) ⟹ `hlocQ` の遺伝は 100% か**を全箱で確かめる。"""
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
from r248 import hlocQ
from r257 import C4


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
                    if not (C4(Q) and hlocQ(Q)): continue
                    for n in NS:
                        S0 = [tuple(x) for x in mTower(Q, d, e, n)]
                        Bk = [tuple(x) for x in block(Q, d, e, n)]
                        for j in range(1, len(Q)):
                            Sj = S0 + Bk[:j + 1]
                            lastx = len(Sj) - 1
                            p = trio.parent(Sj, srow(Sj, lastx), lastx)
                            if p is None or lastx - p < 2: continue
                            V = [tuple(x) for x in Sj[p:lastx]]
                            c['C4 ∧ hlocQ(Q) の窓'] += 1
                            if V[0][2] != 0:
                                c['   ⛔ hz0(V) が偽（除外）'] += 1; continue
                            c['★★ 分母（C4 ∧ hlocQ(Q) ∧ hz0(V)）'] += 1
                            if hlocQ(V): c['★★★ hlocQ(V) が真'] += 1
                            else:
                                c['⛔ **残差**'] += 1
                                if len(ex) < 4: ex.append((Q, d, e, n, j, V))
    dn = c['★★ 分母（C4 ∧ hlocQ(Q) ∧ hz0(V)）']
    print(f'### {tag}  [{time.time()-t0:.1f}s]  窓 {c["C4 ∧ hlocQ(Q) の窓"]}'
          f'（⛔ hz0(V) 偽で除外 {c["   ⛔ hz0(V) が偽（除外）"]}）')
    print(f'    ★★ 分母 {dn}  ★★★ **hlocQ(V) が真** {c["★★★ hlocQ(V) が真"]} '
          f'({100*c["★★★ hlocQ(V) が真"]/max(dn,1):8.4f}%)  ⛔ **残差** {c["⛔ **残差**"]}')
    for x in ex:
        print(f'      ⛔ 例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} V={x[5]}')


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), '|R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), '★ |R|=4 行1<3')
    run(4, 4, (0,1,2,3), (0,1), (0,1,2), (1,2), '★★ |R|=4 行1<4')
    run(5, 3, (0,1,2), (0,1), (0,1), (1,2), '★★ |R|=5 行1<3')
