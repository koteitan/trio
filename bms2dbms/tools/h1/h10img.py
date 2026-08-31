# -*- coding: utf-8 -*-
"""H10 (3): lim=6 の ImgClosedT の破れ 54 個を集めて pickle に落とす。"""
import sys, os, pickle, time
sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3
from rows3 import gen3, key, b2d3
from imgfast import imgclosed_fast
import inv3
t0=time.time()
A=sorted(gen3('BMS',6,zcap=1), key=key)
R=imgclosed_fast(b2d3, A, 3, inv3.d2b3)
ok,tot,bad=R
import pickle as _pk; _pk.dump(getattr(R,'badpairs',None), open('/tmp/h1work/img54p.pkl','wb'))
print('ImgClosedT: 当たり %d / %d  破れ %d  (%.0fs)'%(ok,tot,len(bad),time.time()-t0))
pickle.dump(bad, open('/tmp/h1work/img54.pkl','wb'))
from core import show
for e in sorted(getattr(R,'badpairs',[]))[:6]:
    print('   ', e)
