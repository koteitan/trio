# -*- coding: utf-8 -*-
"""H12: site の素性表（証人の正例 ＋ シート/一致の負例）。"""
import sys, os, pickle
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from h6feat import atoms
from h11feat import extra

CLS = os.environ['CLS']
names0, X0, Y0, META0 = pickle.load(open('/tmp/h1work/h12f%s.pkl' % CLS, 'rb'))
P = [m for m, y in zip(META0, Y0) if y]
N = [m for m, y in zip(META0, Y0) if not y]
for t in os.environ.get('ADD', '').split(','):
    if t.strip():
        P += [tuple(x) for x in pickle.load(open('/tmp/h1work/h12pos_%s.pkl' % t.strip(), 'rb'))]
        N += [tuple(x) for x in pickle.load(open('/tmp/h1work/h12neg_%s.pkl' % t.strip(), 'rb'))]
sp, sn = set(map(tuple, P)), set(map(tuple, N))
both = sp & sn
print('クラス %s: 正例 %d / 負例 %d / **矛盾 %d**' % (CLS, len(sp), len(sn), len(both)))
P, N = sorted(sp - both), sorted(sn - both)
X, Y, META, names = [], [], [], None
for lab, S in ((1, P), (0, N)):
    for Mo, off in S:
        a = atoms(Mo, off)
        a.update(extra(Mo, off))
        if names is None:
            names = sorted(a)
        X.append(tuple(bool(a[nm]) for nm in names))
        Y.append(lab)
        META.append((Mo, off))
pickle.dump((names, X, Y, META), open('/tmp/h1work/h12g%s.pkl' % CLS, 'wb'))
print('site %d 個  正例 %d / 負例 %d  素性 %d' % (len(Y), sum(Y), len(Y) - sum(Y), len(names)))
