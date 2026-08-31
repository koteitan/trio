# -*- coding: utf-8 -*-
import sys, pickle
from collections import defaultdict, Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
from h1an import load
from h1p0 import atoms
FILES = ['S.pkl','T5.pkl','T6.pkl','T6_6.pkl','T7_4.pkl']
WHY = sys.argv[1] if len(sys.argv) > 1 else 'prev0'
R = load(*FILES)
tab, cur, dec = {}, {}, {}
for r in R:
    k = (r['A'], r['off'])
    tab[k]=r['shallow']; cur[k]=r['dec']['shallow']; dec[k]=r['dec']
W = {'prev0': ('prev0/shallow','prev0/deep'),
     'after_w': ('after_w/shallow','after_w/deep'),
     'all': None}[WHY]
K = [k for k in tab if W is None or dec[k]['why'] in W]
print('%s の枝 %d 本  正解 深い %d / 浅い %d' % (WHY, len(K),
      sum(1 for k in K if not tab[k]), sum(1 for k in K if tab[k])))
NAMES = sorted(atoms(K[0][0], K[0][1], dec[K[0]]))
X = [tuple(bool(atoms(k[0],k[1],dec[k])[nm]) for nm in NAMES) for k in K]
Y = [not tab[k] for k in K]
n=len(Y); FULL=(1<<n)-1
COLS=[]
for i in range(len(NAMES)):
    v=0
    for r,x in enumerate(X):
        if x[i]: v |= (1<<r)
    COLS.append(v)
YB=0
for r,y in enumerate(Y):
    if y: YB |= (1<<r)
pickle.dump((NAMES,COLS,YB,FULL,n), open('/tmp/h1work/BITS.pkl','wb'))
pickle.dump((NAMES,X,Y,[(k[0],k[1],['?']) for k in K]), open('/tmp/h1work/P0.pkl','wb'))
print('書いた BITS.pkl / P0.pkl  n=%d 深い %d' % (n, bin(YB).count('1')))
