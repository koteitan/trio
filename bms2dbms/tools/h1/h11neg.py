# -*- coding: utf-8 -*-
"""H11: 壊れた一致から負例の場所を集める（H8 のやり方）。

壊れた (A,n,m) について、E = A<n>。1 か所だけ発火させて
    conv3s(E) != (conv3s A)<m>
になったら、その場所は**発火してはいけない**（負例）。
"""
import sys, os, pickle
os.environ['SBFLAGS'] = os.environ.get('FL', 'sibnb,sibnb_cov')
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3s
from core import expand

TAG = os.environ.get('TAG', 'cov')
b0 = pickle.load(open('/tmp/h1work/ag_base_7.pkl', 'rb'))
s0 = pickle.load(open('/tmp/h1work/ag_%s_7.pkl' % TAG, 'rb'))
br = sorted(b0 - s0, key=lambda e: (len(e[0]), e))
new = sorted(s0 - b0, key=lambda e: (len(e[0]), e))
NEG = set()
seen = set()
nsolo = 0
for A, n, m in br:
    E = tuple(tuple(x) for x in expand(A, n))
    if (A, n, m) in seen:
        continue
    seen.add((A, n, m))
    fA = sorted(set(f[0] for f in rows3s.b2d3f(list(A))[1]))
    fE = sorted(set(f[0] for f in rows3s.b2d3f(list(E))[1]))
    base_A = rows3s.b2d3f(list(A), sites=set())[0]
    base_E = rows3s.b2d3f(list(E), sites=set())[0]
    for off in fE:
        u = rows3s.b2d3f(list(E), sites={off})[0]
        if u != tuple(expand(base_A, m)):
            NEG.add((E, off))
            nsolo += 1
    for off in fA:
        t = tuple(expand(rows3s.b2d3f(list(A), sites={off})[0], m))
        if base_E != t:
            NEG.add((A, off))
            nsolo += 1
print('壊れた %d 組 -> 単独で壊す場所 %d（相異なる %d）'
      % (len(br), nsolo, len(NEG)))
POS = set()
for A, n, m in new:
    E = tuple(tuple(x) for x in expand(A, n))
    base_A = rows3s.b2d3f(list(A), sites=set())[0]
    base_E = rows3s.b2d3f(list(E), sites=set())[0]
    for off in sorted(set(f[0] for f in rows3s.b2d3f(list(E))[1])):
        if rows3s.b2d3f(list(E), sites={off})[0] == tuple(expand(base_A, m)):
            POS.add((E, off))
    for off in sorted(set(f[0] for f in rows3s.b2d3f(list(A))[1])):
        if base_E == tuple(expand(rows3s.b2d3f(list(A), sites={off})[0], m)):
            POS.add((A, off))
print('新しく一致 %d 組 -> 正例 %d' % (len(new), len(POS)))
pickle.dump(sorted(NEG), open('/tmp/h1work/h11neg_%s.pkl' % TAG, 'wb'))
pickle.dump(sorted(POS), open('/tmp/h1work/h11pos_%s.pkl' % TAG, 'wb'))
