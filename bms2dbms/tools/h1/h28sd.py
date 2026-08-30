# -*- coding: utf-8 -*-
"""H28: `sd` の門を **368 素性ぜんぶ**で学習し直す（単調性の縛りが外れたので）。"""
import sys, os, pickle, random
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
from h6feat import atoms
from h11feat import extra
from h13x import far


def vec(Mo, off):
    a = atoms(Mo, off)
    a.update(extra(Mo, off))
    a.update(far(Mo, off))
    return a


FIX = pickle.load(open('/tmp/h1work/h14fix.pkl', 'rb'))
POS = sorted(set((Bt, off) for Bt, off, val in FIX if val == 'sd'))
NEG = [tuple(x) for x in pickle.load(open('/tmp/h1work/h24neg.pkl', 'rb'))]
random.seed(11)
LIM = int(os.environ.get('NLIM', '12000'))
if len(NEG) > LIM:
    NEG = random.sample(NEG, LIM)
both = set(POS) & set(NEG)
P, N = sorted(set(POS) - both), sorted(set(NEG))
print('正例 %d / 負例 %d / ぶつかり %d' % (len(P), len(N), len(both)))
X, Y, META, names = [], [], [], None
for lab, S in ((1, P), (0, N)):
    for Mo, off in S:
        a = vec(Mo, off)
        if names is None:
            names = sorted(a)
        X.append(tuple(bool(a[nm]) for nm in names))
        Y.append(lab)
        META.append((Mo, off))
nx = {}
for i, y in enumerate(Y):
    if not y:
        nx.setdefault(X[i], []).append(i)
coll = [i for i, y in enumerate(Y) if y and X[i] in nx]
print('素性 **%d**（縛りなし）/ 完全一致する正例 %d / %d' % (len(names), len(coll), sum(Y)))
pickle.dump((names, X, Y, META), open('/tmp/h1work/h28sd.pkl', 'wb'))
