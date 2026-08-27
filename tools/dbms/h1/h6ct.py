# -*- coding: utf-8 -*-
"""H6 (2): closes_top の撃ちすぎ / after_w の誤り を機械生成素性で分ける。"""
import sys, pickle
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
from h6feat import atoms
from rows3 import closes_unit, closes_top
from core import show

WHICH = sys.argv[1] if len(sys.argv) > 1 else 'ct'
tab, cur, dec, want = pickle.load(open('/tmp/h1work/h6tab.pkl','rb'))

def sel(k):
    A, off = k; d = dec[k]
    if WHICH == 'ct':      # closes_top が新しく発火した site
        if closes_unit(d['nxt']) or off + 1 >= len(A): return False
        return closes_top(A, off, d['nxt'])
    if WHICH == 'aw':      # after_w が決めた site
        return d['why'].startswith('after_w')
    if WHICH == 'p0':
        return d['why'].startswith('prev0')
    return True

X, Y, META, names = [], [], [], None
for k in tab:
    if dec[k].get('shallow') is None: continue
    if not sel(k): continue
    a = atoms(k[0], k[1])
    if names is None: names = sorted(a)
    X.append(tuple(a[nm] for nm in names))
    import os
    Y.append((not tab[k]) if os.environ.get('TGT')=='deep' else (cur[k] != tab[k]))
    META.append(k)
n = len(Y)
import os
print('%s の site %d 個   正例 %d / 負例 %d  素性 %d  (TGT=%s)' % (WHICH, n, sum(Y), n-sum(Y), len(names), os.environ.get('TGT','fix')) if True else '')
print('%s の site %d 個   正例 %d / 負例 %d  素性 %d'
      % (WHICH, n, sum(Y), n - sum(Y), len(names)))
pickle.dump((names, X, Y, META), open('/tmp/h1work/h6_%s.pkl' % WHICH, 'wb'))
res = []
for i, nm in enumerate(names):
    h = sum(1 for x, y in zip(X, Y) if x[i] == y)
    res.append((max(h, n - h), nm, h >= n - h))
res.sort(reverse=True)
print('--- 単一素性（最良 8）')
for h, nm, pol in res[:8]:
    print('   %-22s %s %d/%d' % (nm, '   ' if pol else 'not', h, n))
