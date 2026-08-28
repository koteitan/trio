# -*- coding: utf-8 -*-
"""H14 (4): 条項 `sbody_w` の教師データ（素性は最初から 368 本）。"""
import sys, os, pickle
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3, rows3b, sheet3, inv3
from core import expand, show, isstd
from h6feat import atoms
from h11feat import extra
from h13x import far

# ---- 正例: 証人（lim=5 の 2 個 ＋ lim=6 の ImgCofinalT の破れ）
POS = set()
targets = [((0, 0, 0), (1, 1, 1), (2, 0, 0), (3, 1, 1), (1, 1, 1)),
           ((0, 0, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1), (2, 1, 0))]
targets += [tuple(map(tuple, A)) for A in
            pickle.load(open('/tmp/h1work/cof6.pkl', 'rb'))]
nfix = 0
for A in targets:
    fA = tuple(map(tuple, rows3.b2d3(list(A))))
    for m in range(1, 7):
        T = tuple(expand(fA, m))
        B = inv3.d2b3([list(x) for x in T])
        if not B:
            continue
        Bt = tuple(tuple(x) for x in B)
        if not isstd(Bt, 'BMS') or any(x[2] > 1 for x in Bt):
            continue
        if tuple(map(tuple, rows3.b2d3(list(Bt)))) == T:
            continue
        oall, F = rows3b.b2d3b(list(Bt))
        if oall != T or not F:
            continue
        nfix += 1
        offs = sorted(set(f[0] for f in F))
        hit = [o for o in offs if rows3b.b2d3b(list(Bt), sites={o})[0] == T]
        for o in (hit if hit else offs):
            POS.add((Bt, o))
print('証人が直る対 %d / 正例 %d' % (nfix, len(POS)))

# ---- 負例: シート
NEG = set()
T2 = sheet3.load(1)
for row, b, d in T2:
    E = tuple(map(tuple, b))
    o0 = tuple(map(tuple, rows3.b2d3(list(E))))
    if o0 != tuple(map(tuple, d)):
        continue
    _, F = rows3b.b2d3b(list(E))
    for off in sorted(set(f[0] for f in F)):
        if rows3b.b2d3b(list(E), sites={off})[0] != o0:
            NEG.add((E, off))
print('シート由来の負例 %d' % len(NEG))
for t in os.environ.get('ADD', '').split(','):
    if t.strip():
        f = '/tmp/h1work/h14sbneg_%s.pkl' % t.strip()
        if os.path.exists(f):
            NEG |= set(tuple(x) for x in pickle.load(open(f, 'rb')))
both = POS & NEG
P, N = sorted(POS - both), sorted(NEG)
print('正例 %d / 負例 %d / ぶつかり %d' % (len(P), len(N), len(both)))
X, Y, META, names = [], [], [], None
for lab, S in ((1, P), (0, N)):
    for Mo, off in S:
        a = atoms(Mo, off)
        a.update(extra(Mo, off))
        a.update(far(Mo, off))
        if names is None:
            names = sorted(a)
        X.append(tuple(bool(a[nm]) for nm in names))
        Y.append(lab)
        META.append((Mo, off))
nx = {}
for i, y in enumerate(Y):
    if not y:
        nx.setdefault(X[i], []).append(i)
coll = sum(1 for i, y in enumerate(Y) if y and X[i] in nx)
print('素性 %d / **完全一致する正例 %d**' % (len(names), coll))
pickle.dump((names, X, Y, META), open('/tmp/h1work/h14sb.pkl', 'wb'))
