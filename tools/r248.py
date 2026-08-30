# -*- coding: utf-8 -*-
"""**(COND) `hlocQ(Q)` を仮定した条件つき遺伝**（教訓: 遺伝は条件つきで測る）。
併せて **(FIN-a) の同語反復**「根が証人 ⟺ 錐の中」を明示的に確認する。"""
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
from r247 import row1_wit, orphan_in


def hlocQ(X):
    for j in range(1, len(X)):
        if X[j][2] > 0:
            if trio.parent(X[:j+1], 2, j) is None: return False
        elif X[j][1] > 0:
            if not row1_wit(X, j): return False
    return True


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
                    hq = hlocQ(Q)
                    c['消費側 Q 総数'] += 1
                    if hq: c['★ hlocQ(Q) が真'] += 1
                    for n in NS:
                        S0 = [tuple(x) for x in mTower(Q, d, e, n)]
                        B = block(Q, d, e, n)
                        for j in range(1, len(Q)):
                            Sj = S0 + B[:j + 1]
                            lastx = len(Sj) - 1
                            p = trio.parent(Sj, srow(Sj, lastx), lastx)
                            if p is None or lastx - p < 2: continue
                            V = [tuple(x) for x in Sj[p:lastx]]
                            tagq = '★条件つき' if hq else '（条件なし）'
                            c[f'{tagq} 窓 分母'] += 1
                            if hlocQ(V): c[f'★ {tagq} hlocQ(V) が真'] += 1
                            elif hq and len(ex) < 6:
                                ex.append((Q, d, e, n, j, V))
                            # ---------- (FIN-a) の同語反復の確認 ----------
                            if V[1][2] == 0 and V[1][1] > 0:
                                inc = trio.is_ancestor(V, 1, 0, 1)
                                wit = V[0][1] < V[1][1]
                                c['(FIN-a) 分母'] += 1
                                if inc == wit: c['★ 根が証人 ⟺ 錐の中'] += 1
                                else: c['⛔ 一致しない'] += 1
                                if hq:
                                    c['★条件つき (FIN) 分母'] += 1
                                    if not inc:
                                        c['⛔ 条件つきでも 錐の外'] += 1
                                        if not orphan_in(Sj, p + 1):
                                            c['⛔ 錐の外かつ (ii) に親がいる'] += 1
    def pc(a, b): return f'{a} ({100*a/max(b,1):8.4f}%)'
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    print(f'  消費側 `Q` {c["消費側 Q 総数"]}  ★ **hlocQ(Q) が真** '
          f'{pc(c["★ hlocQ(Q) が真"], c["消費側 Q 総数"])}')
    for k in ('★条件つき', '（条件なし）'):
        print(f'  {k}: 窓 {c[f"{k} 窓 分母"]}  ★ **hlocQ(V) が真** '
              f'{pc(c[f"★ {k} hlocQ(V) が真"], c[f"{k} 窓 分母"])}')
    print(f'  (FIN-a) **根が証人 ⟺ 錐の中** '
          f'{pc(c["★ 根が証人 ⟺ 錐の中"], c["(FIN-a) 分母"])}  ⛔ 一致しない {c["⛔ 一致しない"]}')
    dq = c['★条件つき (FIN) 分母']
    print(f'  ★条件つき (FIN) 分母 {dq}  ⛔ **錐の外** {pc(c["⛔ 条件つきでも 錐の外"], dq)}  '
          f'⛔ **うち (ii) に親がいる** {c["⛔ 錐の外かつ (ii) に親がいる"]}')
    for x in ex:
        print(f'      ⛔ hlocQ(Q) 真だが hlocQ(V) 偽: Q={x[0]} d={x[1]} e={x[2]} n={x[3]} '
              f'j={x[4]} V={x[5]}')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2), '|R|=3 行1<3')
    run(4, 3, (0,1,2), (0,1), (0,1,2), (1,2), '★ |R|=4 行1<3')
