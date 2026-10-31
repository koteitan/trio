import sys,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import residual_extension_local_trio_codex as A
from fdshcopy_trio_codex import Y,Z,comp,summ
d=json.load(open('qn46_trace.json'));s=d['witness'][1]
import re
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
C=A.ctx(M);T=A.ctx(M[:-1]);x=len(M)-1
r=C.e.par(2,x);q=C.e.par(0,x);cl=C.CL(r);V=C.v(r)
print('x',x,'r',r,'q',q,'CL r',cl,'CL_T r',T.CL(r))
X1=T.pre(r,T.CL(r));B=C.pre(r,cl[:-1]);sx=summ(X1);t1=sx[-1][0]
print('X1',Y.tstr(X1));print('t1',Y.tstr(t1))
# frames for PathLvAll
def frames():
    out=[]
    for i in range(len(M)):
        cl2=C.CL(i);a=C.v(i)
        for j,c in enumerate(cl2):
            cv=C.o(c)
            if not cv or cv[2]:continue
            s_,y,_=cv;Bb=C.pre(i,cl2[:j])
            if Y.lt(Bb,y) and Y.lt((a,Z,Z),cv):out.append((i,j,c))
    return out
F=frames();par={c:(i,j) for i,j,c in F}
# chain to r
ch=[];c=r
while c in par:
    i,j=par[c];ch.append((i,j,c,Y.tstr(C.v(i))));c=i
print('frame chain to r (k,idx,c,v k):',ch)
S=Y.add(V,Y.omega(A.F.sumN([A.F.ONE]+[C.bumpTerm(q,dd) for dd in C.ch(q) if dd<x]))) if hasattr(A.F,'sumN') else None
from probe_inv3_prefix import sumN,ONE
S=Y.add(V,Y.omega(sumN([ONE]+[C.bumpTerm(q,dd) for dd in C.ch(q) if dd<x])))
for i,j,c,vk in ch:
    u=C.v(i)
    if not Y.lt(V,u):
        bad=[g for g in comp(u,t1)+comp(u,S) if not Y.lt(g,X1)]
        print('u=v(%d)'%i,Y.tstr(u),'bad',[Y.tstr(g) for g in bad][:3],'in t1',[g in comp(u,t1) for g in bad][:3])
print('Lc',cl[:-1])
