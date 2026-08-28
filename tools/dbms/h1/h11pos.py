# -*- coding: utf-8 -*-
"""H11: 新しく一致した対から正例の場所を集める。"""
import sys, os, pickle
os.environ['SBFLAGS'] = 'sibnb,sibnb_cov'
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3, rows3s
from core import expand
b = pickle.load(open('/tmp/h1work/ag_base_7.pkl', 'rb'))
s = pickle.load(open('/tmp/h1work/ag_cov_7.pkl', 'rb'))
new = sorted(s - b, key=lambda e: (len(e[0]), e))
POS = set()
for A, n, m in new:
    E = tuple(tuple(x) for x in expand(A, n))
    fA = sorted(set(f[0] for f in rows3s.b2d3f(list(A))[1]))
    fE = sorted(set(f[0] for f in rows3s.b2d3f(list(E))[1]))
    base_A = rows3s.b2d3f(list(A), sites=set())[0]
    base_E = rows3s.b2d3f(list(E), sites=set())[0]
    for off in fE:
        if rows3s.b2d3f(list(E), sites={off})[0] == tuple(expand(base_A, m)):
            POS.add((E, off))
    for off in fA:
        if base_E == tuple(expand(rows3s.b2d3f(list(A), sites={off})[0], m)):
            POS.add((A, off))
print('新しく一致した %d 組 -> 単独で直す場所 %d' % (len(new), len(POS)))
pickle.dump(sorted(POS), open('/tmp/h1work/h11pos.pkl', 'wb'))
