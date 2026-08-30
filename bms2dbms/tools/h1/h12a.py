# -*- coding: utf-8 -*-
"""H12 (1): `first` が行列読みと食い違う 4 か所を 1 つずつ出す。"""
import sys
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3F
from h11m import first_mat, ps_mat, nA_mat
from core import expand, show

lim = int(sys.argv[1]) if len(sys.argv) > 1 else 7
nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 1
A = sorted(rows3.gen3('BMS', lim, zcap=1), key=rows3.key)
Ms = [tuple(map(tuple, M)) for M in A]
for M in list(Ms):
    for n in range(1, nmax + 1):
        x = [tuple(y) for y in expand(M, n)]
        if x:
            Ms.append(tuple(x))
c = Counter()
hits = []
for Mo in Ms:
    out, rec = rows3F.b2d3F(list(Mo))
    for R in rec:
        j = R['off']
        c['_'] += 1
        if R['first'] != first_mat(Mo, j):
            hits.append((Mo, R))
print('lim=%d n<=%d: 柱 %d 本 / first の食い違い %d' % (lim, nmax, c['_'], len(hits)))
for Mo, R in hits:
    j = R['off']
    print()
    print('  %s' % show([list(x) for x in Mo]))
    print('  off=%d 柱=%s  ctx=%s' % (j, Mo[j], R['ctx']))
    print('  conv3: first=%s ps=%s d=%s nA=%s F=%s'
          % (R['first'], R['ps'], R['d'], R['nA'], R['F']))
    print('  行列 : first=%s ps=%s nA=%s' % (first_mat(Mo, j), ps_mat(Mo, j),
                                             nA_mat(Mo, j)))
    print('  L=%s' % (R['L'],))
