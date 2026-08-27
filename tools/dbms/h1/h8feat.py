# -*- coding: utf-8 -*-
"""h8big が作った (正例, 負例) から素性表を作る。"""
import sys, pickle
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
from h6feat import atoms
WHICH = sys.argv[1] if len(sys.argv)>1 else 'aw'
pos, neg = pickle.load(open('/tmp/h1work/h8big_%s.pkl' % WHICH,'rb'))
# 正例 = 「深くすべきなのに浅いと言っている」site（＝深いのが正解）
# 負例 = いまの決定が正しい site。目標は「深い」を当てる述語なので
#        負例のうち「正解が深い」ものは正例側に回す（当ててよい）
X,Y,META,names=[],[],[],None
for k,lab in list(pos.items()):
    a=atoms(k[0],k[1])
    if names is None: names=sorted(a)
    X.append(tuple(a[n] for n in names)); Y.append(not lab); META.append(k)   # lab=正解が浅いか
for k,lab in list(neg.items()):
    a=atoms(k[0],k[1])
    X.append(tuple(a[n] for n in names)); Y.append(not lab); META.append(k)
print('%s: site %d 個   正例（深いのが正解）%d / 負例（浅いのが正解）%d  素性 %d'
      % (WHICH, len(Y), sum(Y), len(Y)-sum(Y), len(names)))
pickle.dump((names,X,Y,META), open('/tmp/h1work/h8f_%s.pkl' % WHICH,'wb'))
