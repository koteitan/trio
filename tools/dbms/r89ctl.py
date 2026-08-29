# -*- coding: utf-8 -*-
"""**R89 陰性対照 —— 形の検算器 (P1/P2/P3) がちゃんと鳴るか。**

100% は「検算器が何も見ていない」ときにも出る（教訓 12）。そこで**わざと壊した式**を
同じ検算器にかけ、VIOL が出ることを確かめる。

  P1' : `S[0] :: (S.tail)⟦n+1⟧` （コピー数をずらす）
  P2' : `tower(Q, d0+1, d1, n)` / `tower(Q, d0, d1+1, n)` （増分をずらす）
  P2'': `Q = S[0:j1+1]`（cap 列を塊に**入れて**しまう）
  P3' : `S.dropLast.dropLast`
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r89 import lift1, shape, cap
from r89b import tower

NS = (1, 2, 3, 4)
COL = [(d, b, c) for d in (1, 2, 3) for b in (0, 1, 2) for c in (0, 1)]
tot = Counter()
for L in (1, 2):
    for Mt in itertools.product(COL, repeat=L):
        M = list(Mt)
        for v in (0, 1, 2):
            for z in (0, 1):
                for t in (0, 1, 2):
                    for b in (0, 1, 2, 3):
                        for c in (0, 1, 2):
                            S = lift1([(0, v, z)] + cap(M, b, c), t)
                            j1 = len(S) - 1
                            br, j0, i1, d0, d1 = shape(S)
                            E = {n: [tuple(x) for x in trio.expand(list(S), n)]
                                 for n in NS}
                            if br == 'noparent':
                                tot['P3 真/' + ('ok' if all(E[n] == [tuple(x) for x in S[:-1]] for n in NS) else 'VIOL')] += 1
                                tot['P3 壊/' + ('ok' if all(E[n] == [tuple(x) for x in S[:-2]] for n in NS) else 'VIOL')] += 1
                            elif br == 'copy' and j0 >= 1:
                                tot['P1 真/' + ('ok' if all(E[n] == [tuple(S[0])] + [tuple(x) for x in trio.expand(list(S[1:]), n)] for n in NS) else 'VIOL')] += 1
                                tot['P1 壊/' + ('ok' if all(E[n] == [tuple(S[0])] + [tuple(x) for x in trio.expand(list(S[1:]), n + 1)] for n in NS) else 'VIOL')] += 1
                            elif br == 'copy':
                                Q = S[:j1]
                                tot['P2 真/' + ('ok' if all(E[n] == [tuple(x) for x in tower(Q, d0, d1, n)] for n in NS) else 'VIOL')] += 1
                                tot['P2 壊d0/' + ('ok' if all(E[n] == [tuple(x) for x in tower(Q, d0 + 1, d1, n)] for n in NS) else 'VIOL')] += 1
                                tot['P2 壊d1/' + ('ok' if all(E[n] == [tuple(x) for x in tower(Q, d0, d1 + 1, n)] for n in NS) else 'VIOL')] += 1
                                tot['P2 壊Q/' + ('ok' if all(E[n] == [tuple(x) for x in tower(S[:j1 + 1], d0, d1, n)] for n in NS) else 'VIOL')] += 1
print('### R89 陰性対照（壊した式で VIOL が鳴るか）')
for k in sorted(tot):
    print(f'  {k:14s} {tot[k]:10d}')
