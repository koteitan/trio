# -*- coding: utf-8 -*-
"""H49 の続き: タイで切った `R1` / `R2` が帰納法を回すか。"""
import sys, io, contextlib
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
with contextlib.redirect_stdout(io.StringIO()):
    import h49
import trio
import probe_tiefree_tower as PT
from collections import Counter

tie = h49.tie
N = len(tie)
print('タイの事例 **%d 件**' % N)
print()
print('**R2 は同じ根で TowerOK2 の場面になるか（帰納法が回るか）**')
c = Counter()
for row, ocf, v, R, M, tf in tie:
    t = max(i for i, p in enumerate(R) if p[1] == v)
    R1, R2 = R[:t], R[t + 1:]
    M2 = [(0, v, 0)] + R2
    M1 = [(0, v, 0)] + R1
    c['R2: 末尾に根を付けると親ができる'] += h49.hp(M2, len(R2))
    c['R2: 末尾は R2 内で孤児'] += (not h49.hp(R2, len(R2) - 1)) if R2 else 0
    c['R2: 末尾の srow = 2'] += (h49.srow(R2, len(R2) - 1) == 2) if R2 else 0
    X2 = [tuple(q) for q in trio.expand(list(M2), 1)]
    try:
        c['R2: (0,v,0)::R2 は TieFree'] += PT.tiefree(X2)
    except AssertionError:
        c['R2: coneV_of_le1 が破れた'] += 1
    c['R1: 末尾は R1 内で孤児'] += (not h49.hp(R1, len(R1) - 1)) if R1 else 0
    c['R1: 末尾の srow = 2'] += (h49.srow(R1, len(R1) - 1) == 2) if R1 else 0
    c['R1: 末尾に根を付けると親ができる'] += h49.hp(M1, len(R1)) if R1 else 0
    X1 = [tuple(q) for q in trio.expand(list(M1), 1)]
    try:
        c['R1: (0,v,0)::R1 は TieFree'] += PT.tiefree(X1)
    except AssertionError:
        c['R1: coneV_of_le1 が破れた'] += 1
for k in ('R2: 末尾に根を付けると親ができる', 'R2: 末尾は R2 内で孤児',
          'R2: 末尾の srow = 2', 'R2: (0,v,0)::R2 は TieFree',
          'R1: 末尾は R1 内で孤児', 'R1: 末尾の srow = 2',
          'R1: 末尾に根を付けると親ができる', 'R1: (0,v,0)::R1 は TieFree',
          'R2: coneV_of_le1 が破れた', 'R1: coneV_of_le1 が破れた'):
    print('   %-38s **%3d / %d (%.1f%%)**' % (k, c[k], N, 100.0 * c[k] / N))
