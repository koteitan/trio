# -*- coding: utf-8 -*-
"""H11: 条項が ImgClosedT の破れ 105 対のうち何対を直すか（速い当たり判定）。"""
import sys, pickle, os, importlib
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
mod = importlib.import_module(sys.argv[1] if len(sys.argv)>1 else 'rows3')
from core import expand, show
bad = pickle.load(open('/tmp/h1work/img54p.pkl','rb'))
hit=0
for A,m,T in bad:
    S=tuple(map(tuple,A)); T=tuple(map(tuple,T))
    for n in range(1,10):
        E=[tuple(x) for x in expand(S,n)]
        if not E: break
        C=tuple(map(tuple,mod.b2d3(list(E))))
        if len(C)>len(T)+6: break
        if C==T: hit+=1; break
print('%s (SBFLAGS=%s): 105 対のうち A<n> で当たる %d 対'
      %(sys.argv[1] if len(sys.argv)>1 else 'rows3', os.environ.get('SBFLAGS',''), hit))
