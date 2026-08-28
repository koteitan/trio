# -*- coding: utf-8 -*-
"""H14: 壊れた／新しく一致した対から site を集める（クラス別）。"""
import sys, os, pickle
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3, rows3d
from core import expand
TAG = os.environ['TAG']
b0 = pickle.load(open('/tmp/h1work/ag_v17_7.pkl', 'rb'))
s0 = pickle.load(open('/tmp/h1work/ag_%s_7.pkl' % TAG, 'rb'))
br = sorted(b0 - s0, key=lambda e: (len(e[0]), e))
new = sorted(s0 - b0, key=lambda e: (len(e[0]), e))
NEG = {'D': set(), 'E': set()}
POS = {'D': set(), 'E': set()}
for pairs, dest in ((br, NEG), (new, POS)):
    for A, n, m in pairs:
        E = tuple(tuple(x) for x in expand(A, n))
        bA = rows3d.b2d3d(list(A), sites=set())[0]
        bE = rows3d.b2d3d(list(E), sites=set())[0]
        tgt = tuple(expand(bA, m))
        for M, other, isE in ((E, tgt, True), (A, bE, False)):
            for off, col, cls in rows3d.b2d3d(list(M))[1]:
                if isE:
                    ok = rows3d.b2d3d(list(M), sites={off})[0] != other
                else:
                    ok = other != tuple(expand(
                        rows3d.b2d3d(list(M), sites={off})[0], m))
                if ok == (dest is NEG):
                    dest[cls].add((M, off))
for cls in 'DE':
    print('クラス %s: 負例 %d / 正例 %d' % (cls, len(NEG[cls]), len(POS[cls])))
    pickle.dump(sorted(NEG[cls]), open('/tmp/h1work/h14neg_%s_%s.pkl' % (cls, TAG), 'wb'))
    pickle.dump(sorted(POS[cls]), open('/tmp/h1work/h14pos_%s_%s.pkl' % (cls, TAG), 'wb'))
