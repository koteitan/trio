# -*- coding: utf-8 -*-
"""H24: `fE` の門の教師データ（正例 = 証人が要求する `sd` / 負例 = C2 を壊す site）。
素性は**単調な 290 本**だけ（`h1/h23feat.py` の絞り込み）。"""
import sys, os, pickle, random
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
from h23feat import vec

FIX = pickle.load(open('/tmp/h1work/h14fix.pkl', 'rb'))
POS = sorted(set((Bt, off) for Bt, off, val in FIX if val == 'sd'))
NEG = [tuple(x) for x in pickle.load(open('/tmp/h1work/h24neg.pkl', 'rb'))]
random.seed(11)
LIM = int(os.environ.get('NLIM', '12000'))
if len(NEG) > LIM:
    NEG = random.sample(NEG, LIM)
print('正例 %d / 負例 %d（全 61410 から抽出）' % (len(POS), len(NEG)))
both = set(POS) & set(NEG)
P, N = sorted(set(POS) - both), sorted(set(NEG))
print('ぶつかり %d' % len(both))
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
print('単調な素性 %d / **完全一致する正例 %d / %d**' % (len(names), len(coll), sum(Y)))
for i in coll[:3]:
    j = nx[X[i]][0]
    from core import show
    print('   正 %s off=%d' % (show([list(x) for x in META[i][0]]), META[i][1]))
    print('   負 %s off=%d' % (show([list(x) for x in META[j][0]]), META[j][1]))
pickle.dump((names, X, Y, META), open('/tmp/h1work/h24f.pkl', 'wb'))
