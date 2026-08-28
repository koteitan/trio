# -*- coding: utf-8 -*-
"""H13 (2b): `after_w` の site の教師データと集合被覆。"""
import sys, os, pickle
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
import rows3, rows3v, provc, sheet3
from h6feat import atoms
from h11feat import extra
from h13e import aw_sites

POSR = pickle.load(open('/tmp/h1work/h13awpos.pkl', 'rb'))
print('正例（反転すべき after_w の site） %d   内訳 %s'
      % (len(POSR), Counter(v for _, _, v in POSR).most_common()))
NEG = []
T = sheet3.load(1)
n = 0
for row, b, d in T:
    E = tuple(map(tuple, b))
    o0, S = rows3v.b2d3v(list(E))
    if o0 != tuple(map(tuple, d)):
        continue
    n += 1
    aw, wc = aw_sites(E)
    for off, sh, base_s, deep, base_sd, tie in S:
        if off in aw and not tie:
            if rows3v.b2d3v(list(E), {off: not sh})[0] != o0:
                NEG.append((E, off, not sh))
print('シートで正解している %d 行から負例 %d' % (n, len(NEG)))
for tgt in (True, False, None):
    P = [(b, o) for b, o, v in POSR if tgt is None or v == tgt]
    N = [(b, o) for b, o, v in NEG if tgt is None or v == tgt]
    sp, sn = set(P), set(N)
    both = sp & sn
    P, N = sorted(sp - both), sorted(sn)
    if not P:
        continue
    X, Y, META, names = [], [], [], None
    for lab, S2 in ((1, P), (0, N)):
        for Mo, off in S2:
            a = atoms(Mo, off)
            a.update(extra(Mo, off))
            if names is None:
                names = sorted(a)
            X.append(tuple(bool(a[nm]) for nm in names))
            Y.append(lab)
            META.append((Mo, off))
    tag = {True: 'shal', False: 'deep', None: 'all'}[tgt]
    print('  -> %s: 正例 %d / 負例 %d / ぶつかり %d' % (tag, len(P), len(N), len(both)))
    pickle.dump((names, X, Y, META), open('/tmp/h1work/h13aw_%s.pkl' % tag, 'wb'))
