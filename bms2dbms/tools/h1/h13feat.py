# -*- coding: utf-8 -*-
"""H13: `after_w` の site の素性表（証人の正例 ＋ シート/一致の負例）。"""
import sys, os, pickle
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
from h6feat import atoms
from h11feat import extra
POSR = pickle.load(open('/tmp/h1work/h13awpos.pkl', 'rb'))
P = [(b, o) for b, o, v in POSR]
N = []
for t in os.environ.get('ADD', '').split(','):
    if t.strip():
        N += [tuple(x) for x in pickle.load(open('/tmp/h1work/h13neg_%s.pkl' % t.strip(), 'rb'))]
        if os.environ.get('WITHNEW'):
            P += [tuple(x) for x in pickle.load(open('/tmp/h1work/h13pos_%s.pkl' % t.strip(), 'rb'))]
sp, sn = set(map(tuple, P)), set(map(tuple, N))
both = sp & sn
print('正例 %d / 負例 %d / ぶつかり %d（負例が勝つ）' % (len(sp), len(sn), len(both)))
P, N = sorted(sp - both), sorted(sn)
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
print('site %d 個  正例 %d / 負例 %d  素性 %d' % (len(Y), sum(Y), len(Y) - sum(Y), len(names)))
pickle.dump((names, X, Y, META), open('/tmp/h1work/h13g.pkl', 'wb'))
