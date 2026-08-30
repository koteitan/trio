# -*- coding: utf-8 -*-
"""**(ADJ'-c) の穴 0.87% は孤児か。** ⟹ 孤児なら `snoc_orphan_W` で無料 ⟹ 穴ではない。"""
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
from r245 import anc0


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
                    for n in NS:
                        P = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = block(Q, d, e, n)
                        for j in range(1, len(Q)):
                            S = P + B[:j + 1]
                            lastx = len(S) - 1
                            p = trio.parent(S, srow(S, lastx), lastx)
                            if p is None or lastx - p < 2: continue
                            V = [tuple(x) for x in S[p:lastx]]
                            for jab in range(p + 1, lastx):
                                if S[jab][2] != 0 or S[jab][1] == 0: continue
                                A = anc0(S, jab)
                                if not A: continue
                                m = min(S[y][1] for y in A)
                                if not (m < S[jab][1]): continue
                                if max(y for y in A if S[y][1] == m) >= p: continue
                                if [y for y in A if y >= p and S[y][1] < S[jab][1]]: continue
                                # ---------- 取り直せない穴 ----------
                                jj = jab - p
                                c['(ADJ-c) 穴の分母'] += 1
                                orph = trio.parent(V[:jj + 1], srow(V, jj), jj) is None
                                if orph: c['★ 穴の列は孤児（無料）'] += 1
                                else:
                                    c['⛔ 穴の列に親がいる'] += 1
                                    if len(ex) < 4:
                                        ex.append((Q, d, e, n, j, V, jj,
                                                   trio.parent(V[:jj+1], srow(V,jj), jj)))
    dc = c['(ADJ-c) 穴の分母']
    print(f'### {tag}  [{time.time()-t0:.1f}s]  穴 {dc}  '
          f'★ **孤児** {c["★ 穴の列は孤児（無料）"]} ({100*c["★ 穴の列は孤児（無料）"]/max(dc,1):8.4f}%)  '
          f'⛔ **親がいる** {c["⛔ 穴の列に親がいる"]} ({100*c["⛔ 穴の列に親がいる"]/max(dc,1):8.4f}%)')
    for x in ex:
        print(f'    ⛔ Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} V={x[5]} jj={x[6]} 親={x[7]}')


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), '|R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), '★ |R|=4 行1<3')
    run(4, 4, (0,1,2,3), (0,1), (0,1,2), (1,2), '★★ |R|=4 行1<4（箱を伸ばす）')
