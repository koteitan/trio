# -*- coding: utf-8 -*-
"""**R89 その 7 —— `|M| = 4, 5, 6` で形の等式 (P1/P2/P3) が保つか（サンプリング）。**

`|M|<=3` は全数だったが、`|M|>=4` は組合せ爆発するのでランダム標本。
標本の取り方は「列アルファベットから一様に |M| 列」。教訓 11 のとおり、
**母集団の作り方を明示する**。全数（|M|<=3）と比率がどう違うかを併記する。
"""
import sys, itertools, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r89 import lift1, shape, cap
from r89b import tower, rowparent0

NS = (1, 2, 3, 4)
COL = [(d, b, c) for d in (1, 2, 3) for b in (0, 1, 2) for c in (0, 1)]
VS, ZS, TS, CAPB, CAPC = (0, 1, 2), (0, 1), (0, 1, 2), (0, 1, 2, 3), (0, 1, 2)
rng = random.Random(20260830)
tot = Counter(); bad = {}
t0 = time.time()
for L in (4, 5, 6):
    NSAMP = 3000
    for _ in range(NSAMP):
        M = [rng.choice(COL) for _ in range(L)]
        for v in VS:
            for z in ZS:
                for t in TS:
                    for b in CAPB:
                        for c in CAPC:
                            S = lift1([(0, v, z)] + cap(M, b, c), t)
                            j1 = len(S) - 1
                            br, j0, i1, d0, d1 = shape(S)
                            E = {n: [tuple(x) for x in trio.expand(list(S), n)]
                                 for n in NS}
                            if br == 'noparent':
                                ok = all(E[n] == [tuple(x) for x in S[:-1]] for n in NS)
                                tot[f'L{L}/P3/' + ('ok' if ok else 'VIOL')] += 1
                            elif br == 'copy' and j0 >= 1:
                                ok = all(E[n] == [tuple(S[0])] + [tuple(x) for x in trio.expand(list(S[1:]), n)] for n in NS)
                                tot[f'L{L}/P1/' + ('ok' if ok else 'VIOL')] += 1
                            elif br == 'copy':
                                Q = S[:j1]
                                ok = all(E[n] == [tuple(x) for x in tower(Q, d0, d1, n)] for n in NS)
                                tot[f'L{L}/P2/' + ('ok' if ok else 'VIOL')] += 1
                                tot[f'L{L}/tower/srow={i1}'] += 1
                            else:
                                tot[f'L{L}/branch/{br}'] += 1
                            if br == 'copy':
                                tot[f'L{L}/j0=0' if j0 == 0 else f'L{L}/j0>=1'] += 1
                            if not ok:
                                bad.setdefault(f'L{L}/{br}', (M, v, z, b, c, t))
print(f'### R89f 形の検算 |M| ∈ {{4,5,6}} 各 3000 文脈のランダム標本  ({time.time()-t0:.1f}s)')
for k in sorted(tot):
    print(f'  {k:20s} {tot[k]:12d}')
for k in sorted(bad):
    print(f'  ⚠ {k}: {bad[k]}')
