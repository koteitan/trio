# -*- coding: utf-8 -*-
"""H14: クラス D（shallow -> deep）/ E（tie -> base_sd）の教師データ。
素性は最初から **近傍 305 ＋ 遠く 63 = 368 本**（H13 の教訓）。"""
import sys, os, pickle
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3, rows3v, sheet3
from h6feat import atoms
from h11feat import extra
from h13x import far


def vec(Mo, off, names=None):
    a = atoms(Mo, off)
    a.update(extra(Mo, off))
    a.update(far(Mo, off))
    return a


FIX = pickle.load(open('/tmp/h1work/h14fix.pkl', 'rb'))
POS = {'D': [], 'E': []}
for Bt, off, val in FIX:
    POS['E' if val == 'sd' else 'D'].append((Bt, off))
NEG = {'D': [], 'E': []}
T = sheet3.load(1)
n = 0
for row, b, d in T:
    E = tuple(map(tuple, b))
    o0, S = rows3v.b2d3v(list(E))
    if o0 != tuple(map(tuple, d)):
        continue
    n += 1
    for off, sh, base_s, deep, base_sd, tie in S:
        if tie:
            if base_sd != deep and rows3v.b2d3v(list(E), {off: 'sd'})[0] != o0:
                NEG['E'].append((E, off))
        elif sh:                       # いま shallow の site だけがクラス D の対象
            if rows3v.b2d3v(list(E), {off: False})[0] != o0:
                NEG['D'].append((E, off))
print('シートで正解している %d 行' % n)
for cls in 'DE':
    for t in os.environ.get('ADD', '').split(','):
        if t.strip():
            f = '/tmp/h1work/h14neg_%s_%s.pkl' % (cls, t.strip())
            if os.path.exists(f):
                NEG[cls] += [tuple(x) for x in pickle.load(open(f, 'rb'))]
    sp, sn = set(POS[cls]), set(NEG[cls])
    both = sp & sn
    P, N = sorted(sp - both), sorted(sn)
    print('クラス %s: 正例 %d / 負例 %d / ぶつかり %d' % (cls, len(P), len(N), len(both)))
    if not P:
        continue
    X, Y, META, names = [], [], [], None
    for lab, S2 in ((1, P), (0, N)):
        for Mo, off in S2:
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
    coll = sum(1 for i, y in enumerate(Y) if y and X[i] in nx)
    print('   素性 %d / **完全一致する正例 %d**' % (len(names), coll))
    pickle.dump((names, X, Y, META), open('/tmp/h1work/h14f%s.pkl' % cls, 'wb'))
