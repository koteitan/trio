# -*- coding: utf-8 -*-
"""**(W15) の対照 —— 正規化（`entry Q 0 0 = 0`）を外す。**

私の箱は `Q[0] = (0,v,z)` 固定なので、`A` は行 0 が `0` 未満になれず、
**構造的に親を供給できません**（＝ 100% が箱の産物の疑い）。
⟹ ★ **行 0 を一様に `u` だけ持ち上げ**、`A` の行 0 を `0..u-1` にして
   **「供給できる形」**を作る（教訓 12: 破れが出る形の対照）。
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


def run(L, R1, VS, ZS, TS, NS, U, tag):
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
                        S0 = [tuple(x) for x in mTower(Q, d, e, n)]
                        Bk = block(Q, d, e, n)
                        for j in range(1, len(Q)):
                            Sj = [tuple(x) for x in S0 + Bk[:j + 1]]
                            for u in U:
                                # ★ 行 0 を一様に u 持ち上げる（nextrel0 は不変）
                                Su = [(x + u, y, zz) for x, y, zz in Sj]
                                for arow in range(u):        # ⛔ 行 0 が根より浅い A
                                    for arow1 in (0, 1, 5):
                                        for arow2 in (0, 1):
                                            A = [(arow, arow1, arow2)]
                                            T = A + Su
                                            for k in range(1, len(T)):
                                                c['(W15対照) 分母'] += 1
                                                pp = trio.parent(T[:k+1], srow(T, k), k)
                                                if pp is not None and pp < len(A):
                                                    c['⛔ **接頭辞が親を供給**'] += 1
                                                    if len(ex) < 5:
                                                        ex.append((A, Su[:k], k, srow(T, k)))
    dn = c['(W15対照) 分母']; bb = c['⛔ **接頭辞が親を供給**']
    print(f'### {tag}  [{time.time()-t0:.1f}s]  分母 {dn}  '
          f'⛔ **接頭辞が親を供給** {bb} ({100*bb/max(dn,1):8.4f}%)')
    for x in ex:
        print(f'    ⛔ A={x[0]} 列 k={x[2]} (srow={x[3]}) 手前={x[1][:4]}...')


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1), (1,), (1, 2), '|R|=3 行1<3, u∈{1,2}（正規化を外す）')
