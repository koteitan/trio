# -*- coding: utf-8 -*-
"""**R92 その 2 —— 予算を上げると `unknown` は消えるか（教訓 12）。**

R92 の |M|<=2 で `cons(j0>=1)` の枝は ok 270 / unknown 702 だった。
予算（深さ・長さ）を上げて `unknown` が ok に変わるか、それとも VIOL が出るかを見る。
**VIOL が 1 件でも出れば `CoreCap` は偽。** 出なければ「探したが出ない」という証拠。
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r89 import lift1, shape, cap, inW

COL = [(d, b, c) for d in (1, 2, 3) for b in (0, 1, 2) for c in (0, 1)]
z, c = 1, 1
inst = []
for L in (1, 2):
    for Mt in itertools.product(COL, repeat=L):
        M = list(Mt)
        for v in (0, 1, 2):
            for t in (0, 1, 2):
                for b in (0, 1, 2, 3):
                    S = lift1([(0, v, z)] + cap(M, b, c), t)
                    br, j0, i1, d0, d1 = shape(S)
                    if i1 != 2 or br != 'copy' or j0 == 0:
                        continue
                    inst.append((tuple(tuple(x) for x in S), 2 * (v + t) + z))
print(f'### R92b 残核 cons(j0>=1) の枝 {len(inst)} 件で予算を上げる')
for depth, maxlen in ((9, 26), (11, 30), (13, 36), (15, 44), (18, 60)):
    memo = {}
    r = Counter()
    t0 = time.time()
    for S, a in inst:
        x = inW(list(S), a, depth, memo, maxlen)
        r['VIOL' if x is False else 'ok' if x is True else 'unknown'] += 1
    print(f'  depth={depth:3d} maxlen={maxlen:3d} : '
          f'ok {r["ok"]:6d}  unknown {r["unknown"]:6d}  **VIOL {r["VIOL"]:6d}**'
          f'   ({time.time()-t0:.1f}s, memo={len(memo)})')
