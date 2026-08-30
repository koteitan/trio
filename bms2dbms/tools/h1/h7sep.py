# -*- coding: utf-8 -*-
"""tt が壊す 18 site（浅くすべき）と term_top が正しく deep と言う site を分ける。"""
import sys, pickle
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
from h6feat import atoms
from rows3 import term_top
from core import show

POS = pickle.load(open('/tmp/h1work/ttbroke.pkl','rb'))          # 浅くすべき
tab, cur, dec, want = pickle.load(open('/tmp/h1work/h6tab.pkl','rb'))
def p0_shallow(Mo, off):
    return off + 1 >= len(Mo) or term_top(Mo, off + 1)
NEG = [k for k in tab
       if dec[k].get('shallow') is not None
       and dec[k]['why'].startswith('prev0')
       and not p0_shallow(k[0], k[1])]          # term_top が deep と言い、それが正しい
print('正例（tt が壊す、浅くすべき）%d 個 / 負例（deep が正しい）%d 個' % (len(POS), len(NEG)))
X, Y, META, names = [], [], [], None
for k, lab in [(p, True) for p in POS] + [(nn, False) for nn in NEG]:
    a = atoms(k[0], k[1])
    if names is None: names = sorted(a)
    X.append(tuple(a[nm] for nm in names)); Y.append(lab); META.append(k)
pickle.dump((names, X, Y, META), open('/tmp/h1work/h7sep.pkl','wb'))
# ラベルの矛盾
d = {}
conf = 0
for x, y in zip(X, Y):
    if x in d and d[x] != y: conf += 1
    d[x] = y
print('相異なる素性ベクトル %d 個  ラベルの矛盾 %d' % (len(d), conf))
