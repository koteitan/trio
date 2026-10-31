import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA')
from probe_adn import *
from ytosk_eval import tstr
s=sys.argv[1];M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
C=Ctx(M);x=len(M)-1;r=C.e.par(1,x);q=C.e.par(0,x);T=Ctx(M[:x])
A=C.o(r);mu,br,_=A;seed=T.o(r);D=dependencies(C,x);d=lift_counts(C,x,A)
print('x',x,'r',r,'q',q,'o(r)=',tstr(A),' seed=',tstr(seed))
for i in range(x):
  tags=[k for k in (True,False) if (k,i) in D]
  print(i,M[i],'D',tags,'d',d[i],'o',tstr(C.o(i)),' v',tstr(C.v(i)), ' W',tstr(C.bumpW(i)) if C.e12(i) else '')
print('---TPLoW detail')
from probe_inv3_prefix import fsD
for i in range(x):
  if (True,i) in D:
    s_,y,_=C.o(i)
    if y==br or split(y,(succ(s_),Z,Z))[1]!=Z:continue
    l=last(y)
    if not l or l[1]!=Z:continue
    a=l[0]
    if isSucc(a) or not ohole(a) or cof(a)[0]!='omega':continue
    eta=gamS(mu,br,seed,max(1,d[i]))
    ok=not lt((fsD(a,eta),Z,Z),(succ(s_),Z,Z))
    print(i,'s=',tstr(s_),' y=',tstr(y),' a=',tstr(a),' d',d[i],' eta',tstr(eta),' a[eta]=',tstr(fsD(a,eta)),'OK' if ok else 'FAIL')
