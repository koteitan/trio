# -*- coding: utf-8 -*-
"""H12: 壊れた／新しく一致した対から site の正例・負例を集める（H11 と同じ）。"""
import sys, os, pickle
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3w
from core import expand

TAG = os.environ['TAG']
b0 = pickle.load(open('/tmp/h1work/ag_final_7.pkl', 'rb'))
s0 = pickle.load(open('/tmp/h1work/ag_%s_7.pkl' % TAG, 'rb'))
br = sorted(b0 - s0, key=lambda e: (len(e[0]), e))
new = sorted(s0 - b0, key=lambda e: (len(e[0]), e))
NEG, POS = set(), set()
for tag, pairs, dest in (('壊れた', br, NEG), ('新しく一致', new, POS)):
    for A, n, m in pairs:
        E = tuple(tuple(x) for x in expand(A, n))
        bA = rows3w.b2d3w(list(A), sites=set())[0]
        bE = rows3w.b2d3w(list(E), sites=set())[0]
        tgt = tuple(expand(bA, m))
        for off in sorted(set(f[0] for f in rows3w.b2d3w(list(E))[1])):
            u = rows3w.b2d3w(list(E), sites={off})[0]
            if (u != tgt) == (dest is NEG):
                dest.add((E, off))
        for off in sorted(set(f[0] for f in rows3w.b2d3w(list(A))[1])):
            t = tuple(expand(rows3w.b2d3w(list(A), sites={off})[0], m))
            if (bE != t) == (dest is NEG):
                dest.add((A, off))
    print('%s %d 組 -> %d' % (tag, len(pairs), len(dest)))
pickle.dump(sorted(NEG), open('/tmp/h1work/h12neg_%s.pkl' % TAG, 'wb'))
pickle.dump(sorted(POS), open('/tmp/h1work/h12pos_%s.pkl' % TAG, 'wb'))
