# -*- coding: utf-8 -*-
"""**残差の形の census。** `hlocQ(Q)` 真かつ `hlocQ(V)` 偽の `V` を正規化して数える。"""
import sys, itertools
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
from r248 import hlocQ
from r247 import orphan_in


def norm(V):   # 行 0 と行 1 を根で平行移動して形だけ残す
    a, b = V[0][0], V[0][1]
    return tuple((x - a, y - b, z) for x, y, z in V)


def run(L, R1, VS, ZS, TS, NS, tag):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    sh = Counter(); c = Counter()
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
                    if not (d > 0 and hr0(Q) and Q[0][2] == 0 and hlocQ(Q)): continue
                    for n in NS:
                        S0 = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = block(Q, d, e, n)
                        for j in range(1, len(Q)):
                            Sj = S0 + B[:j + 1]
                            lastx = len(Sj) - 1
                            p = trio.parent(Sj, srow(Sj, lastx), lastx)
                            if p is None or lastx - p < 2: continue
                            V = [tuple(x) for x in Sj[p:lastx]]
                            if hlocQ(V): continue
                            sh[norm(V)] += 1
                            c['破れ'] += 1
                            c[f'|V|={len(V)}'] += 1
                            bad = [jj for jj in range(1, len(V))
                                   if not (trio.parent(V[:jj+1], 2, jj) is not None
                                           if V[jj][2] > 0 else
                                           bool(__import__('r247').row1_wit(V, jj)))]
                            c[f'破れ列 jj={bad}'] += 1
                            if all(V[y][1] == V[0][1] for y in bad):
                                c['★ 破れ列の行 1 が根と等しい'] += 1
                            if all(V[y][2] == 0 for y in bad):
                                c['★ 破れ列の行 2 = 0'] += 1
                            if any(not orphan_in(Sj, p + jj) for jj in bad):
                                c['⛔ (ii) に親がいる'] += 1
    print(f'### {tag}  破れ {c["破れ"]}')
    for k in sorted(c):
        if k != '破れ': print(f'    {k}: {c[k]}')
    print(f'  ★ 正規化した形（{len(sh)} 種）:')
    for s, n in sh.most_common(12):
        print(f'      {n:7d}  {list(s)}')
    print()


if __name__ == '__main__':
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2), '★ |R|=4 行1<3')
    run(4, 4, (0,1,2,3), (0,1), (0,1,2), (1,2), '★★ |R|=4 行1<4（箱を伸ばす）')
    run(5, 3, (0,1,2), (0,1), (0,1), (1,2), '★★ |R|=5 行1<3（箱を伸ばす）')
