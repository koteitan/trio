# -*- coding: utf-8 -*-
"""H16: `cB に d+1` の正例（証人が直る場所）とシート由来の負例。"""
import sys, os, pickle
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import rows3, rows3e2, sheet3, inv3
from core import expand, show, isstd
from h6feat import atoms
from h11feat import extra
from h13x import far
POS=set()
targets=[tuple(map(tuple,A)) for A in pickle.load(open('/tmp/h1work/cof6.pkl','rb'))]
targets += [((0,0,0),(1,1,1),(2,0,0),(3,1,1),(1,1,1)), ((0,0,0),(1,1,1),(1,1,0),(2,2,1),(2,1,0))]
nf=0
for A in targets:
    fA=tuple(map(tuple,rows3.b2d3(list(A))))
    for m in range(1,7):
        T=tuple(expand(fA,m)); B=inv3.d2b3([list(x) for x in T])
        if not B: continue
        Bt=tuple(tuple(x) for x in B)
        if not isstd(Bt,'BMS') or any(x[2]>1 for x in Bt): continue
        if tuple(map(tuple,rows3.b2d3(list(Bt))))==T: continue
        o,F=rows3e2.b2d3e(list(Bt))
        if o!=T or not F: continue
        nf+=1
        offs=sorted(set(f[0] for f in F))
        hit=[x for x in offs if rows3e2.b2d3e(list(Bt), sites={x})[0]==T]
        for x in (hit if hit else offs): POS.add((Bt,x))
print('証人が直る対 %d / 正例 %d'%(nf,len(POS)))
NEG=set()
for row,b,d in sheet3.load(1):
    E=tuple(map(tuple,b)); o0=tuple(map(tuple,rows3.b2d3(list(E))))
    if o0!=tuple(map(tuple,d)): continue
    for off,_,_ in rows3e2.b2d3e(list(E))[1]:
        if rows3e2.b2d3e(list(E), sites={off})[0]!=o0: NEG.add((E,off))
print('シート由来の負例 %d'%len(NEG))
for t in os.environ.get('ADD','').split(','):
    if t.strip():
        f='/tmp/h1work/h16neg_%s.pkl'%t.strip()
        if os.path.exists(f): NEG|=set(tuple(x) for x in pickle.load(open(f,'rb')))
both=POS&NEG; P,N=sorted(POS-both),sorted(NEG)
print('正例 %d / 負例 %d / ぶつかり %d'%(len(P),len(N),len(both)))
X,Y,META,names=[],[],[],None
for lab,S in ((1,P),(0,N)):
    for Mo,off in S:
        a=atoms(Mo,off); a.update(extra(Mo,off)); a.update(far(Mo,off))
        if names is None: names=sorted(a)
        X.append(tuple(bool(a[nm]) for nm in names)); Y.append(lab); META.append((Mo,off))
nx={}
for i,y in enumerate(Y):
    if not y: nx.setdefault(X[i],[]).append(i)
coll=sum(1 for i,y in enumerate(Y) if y and X[i] in nx)
print('素性 %d / **完全一致する正例 %d**'%(len(names),coll))
pickle.dump((names,X,Y,META), open('/tmp/h1work/h16f.pkl','wb'))
