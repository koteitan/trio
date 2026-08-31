# -*- coding: utf-8 -*-
"""H12: 分岐列の決定の教師データ（証人 = 正例 / シート = 負例）。

3 つのクラスに分ける:
  A  いまは deep だが **shallow** が正しい     (14)
  B  いまは shallow だが **deep** が正しい     (11)
  C  tie だが **base_sd**（兄弟の深い側）が正しい (5)
負例は「シートで正解している行の site で、ひっくり返すと像が変わるもの」。
"""
import sys, pickle, os
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3v, sheet3
from h6feat import atoms
from h11feat import extra

FIX = pickle.load(open('/tmp/h1work/h12fix.pkl', 'rb'))
POS = {'A': [], 'B': [], 'C': []}
for Bt, off, val in FIX:
    cls = 'C' if val == 'sd' else ('A' if val is True else 'B')
    POS[cls].append((Bt, off))

NEG = {'A': [], 'B': [], 'C': []}
T = sheet3.load(1)
nsheet = 0
for row, b, d in T:
    E = tuple(map(tuple, b))
    o0, S = rows3v.b2d3v(list(E))
    if o0 != tuple(map(tuple, d)):
        continue
    nsheet += 1
    for off, sh, base_s, deep, base_sd, tie in S:
        if tie:
            if base_sd != deep and rows3v.b2d3v(list(E), {off: 'sd'})[0] != o0:
                NEG['C'].append((E, off))
        else:
            if rows3v.b2d3v(list(E), {off: not sh})[0] != o0:
                NEG['A' if not sh else 'B'].append((E, off))
print('シートで正解している %d 行から負例を集めた' % nsheet)
for cls in 'ABC':
    sp, sn = set(POS[cls]), set(NEG[cls])
    both = sp & sn
    print('クラス %s: 正例 %d / 負例 %d / 矛盾 %d' % (cls, len(sp), len(sn), len(both)))
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
    if not Y or not any(Y):
        continue
    pickle.dump((names, X, Y, META), open('/tmp/h1work/h12f%s.pkl' % cls, 'wb'))
