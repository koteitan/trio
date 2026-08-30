# -*- coding: utf-8 -*-
"""**R92 その 3 —— 修正した判定器 `winw.inW2` で残核の `unknown` を潰す。**

R92b で「深さ 9 → 11 に上げても `unknown` が 702 のまま」だったのは
既存 `inW` のメモの毒（深さ切れ・循環の `None` を恒久メモする）が原因。
`winw.inW2` で測り直す。**旧判定器の結果と並べて出す**（計器の差が見えるように）。
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
from collections import Counter
from r89 import lift1, shape, cap, inW
from winw import inW2

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
print(f'### R92c 残核 cons(j0>=1) {len(inst)} 件 —— 旧 `inW` と新 `inW2` の比較')
for tag, fn in (('旧 inW ', 'old'), ('新 inW2', 'new')):
    for depth, maxlen in ((9, 26), (11, 30), (13, 40), (16, 60)):
        memo = {}
        r = Counter()
        t0 = time.time()
        for S, a in inst:
            x = (inW(list(S), a, depth, memo, maxlen) if fn == 'old'
                 else inW2(list(S), a, depth, memo, maxlen))
            r['VIOL' if x is False else 'ok' if x is True else 'unknown'] += 1
        print(f'  {tag} depth={depth:3d} maxlen={maxlen:3d} : '
              f'ok {r["ok"]:6d}  unknown {r["unknown"]:6d}  '
              f'**VIOL {r["VIOL"]:6d}**   ({time.time()-t0:.1f}s)')
