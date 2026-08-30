# -*- coding: utf-8 -*-
"""H16: 族 δ の `cB`（縮約の兄弟）でずれる 5 対を 1 件ずつ見る。"""
import sys, pickle
from collections import Counter, defaultdict
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
import rows3, rows3F, provc, inv3
from core import expand, show, isstd

fam = pickle.load(open('/tmp/h1work/h15fam.pkl', 'rb'))
cof = set(e['A'] for e in fam)
bad = defaultdict(list)
for A, m, T in pickle.load(open('/tmp/h1work/img54p.pkl', 'rb')):
    a = tuple(map(tuple, A))
    if a in cof:
        bad[a].append((m, tuple(map(tuple, T))))
n = 0
for e in fam:
    if e['cls'] != 'どれでも直らない':
        continue
    for m, T in sorted(bad[e['A']]):
        B = inv3.d2b3([list(x) for x in T])
        if not B:
            continue
        Bt = tuple(tuple(x) for x in B)
        if not isstd(Bt, 'BMS') or any(x[2] > 1 for x in Bt):
            continue
        C, PR = provc.b2d3p(list(Bt))
        k = 0
        while k < min(len(C), len(T)) and C[k] == T[k]:
            k += 1
        if k >= len(PR):
            continue
        kind, off, why, ctx = PR[k]
        n += 1
        out, rec = rows3F.b2d3F(list(Bt))
        R = next((x for x in rec if x['off'] == off), None)
        print('=== %s  m=%d   ctx=%s why=%s' % (show(list(e['A'])), m, ctx, why))
        print('   B = %s' % show([list(x) for x in Bt]))
        print('   T = %s' % show([list(x) for x in T]))
        print('   C = %s' % show([list(x) for x in C]))
        print('   k=%d  want=%s got=%s  off=%d 柱=%s kind=%s'
              % (k, T[k], C[k], off, Bt[off], kind))
        if R:
            print('   d=%s first=%s ps=%s nA=%s F=%s' %
                  (R['d'], R['first'], R['ps'], R['nA'], R['F'][:3]))
            print('   L=%s' % (R['L'],))
        print()
        if n >= 6:
            sys.exit(0)
