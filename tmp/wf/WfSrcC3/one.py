import sys,re,subprocess
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from huac_structure_trio_codex import Ctx,Y,lt,le,summ,Z
from lhd_exact import lhd
W2=(Z,(Z,Z,(Z,Z,Z)),Z)
def B(v):return (v,(Y.add(v,(Z,Z,Z)),Z,Z),Z)
def smallB(C,V,c):
 vc=C.v(c)
 if lt(vc,V):return True
 if vc!=V:return False
 return all(smallB(C,V,d) for d in C.CL(c))
def chain1(E,m):
 out=[]
 while m is not None:out.append(m);m=E.par(1,m)
 return out
def check(s,verbose=False):
 M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
 std=subprocess.run(['/home/koteitan/proofs/trio/bms','-s',s],capture_output=True,text=True).stdout.strip()
 C=Ctx(M);E=C.e;x=len(M)-1;r=x-1
 out=dict(std=std,ok=C.ok)
 if not C.ok:return out
 if verbose:
  for i,c in enumerate(M):print(i,c,'P0',E.par(0,i),'P1',E.par(1,i),'upg',C.upg(i),'v',Y.tstr(C.v(i)),'CL',C.CL(i))
 out['ctx']=(E.par(2,x)==r,E.par(0,x)==r,E.par(1,x)==r,C.upg(r))
 p=E.par(0,r);i=E.par(0,p) if p is not None else None
 out['p,i']=(p,i)
 if i is None:return out
 out['bad2ish']=(M[p]==E.bump(i),C.e12(i))
 m=E.par(1,i);V=C.v(m);W=C.bumpW(i);vr=C.v(r)
 res=[]
 for q in summ(V):
  if lt(q,W2) or not lt(q,W) or lhd(q,W):continue
  for b in chain1(E,m):
   k=C.upg(b)
   if k is None or C.bumpW(k)!=q:continue
   for j in C.ch(k):
    if M[j]!=E.bump(k):continue
    for c in C.ch(j):res.append(dict(b=b,k=k,j=j,c=c,smallB=smallB(C,vr,c),oc_lt_B=lt(C.o(c),B(vr))))
 out['occ']=res
 return out
if __name__=='__main__':
 for s in sys.argv[1:]:print(s,check(s,'-v' in sys.argv))
def full(s):
 sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
 from bad2_exact_trio_codex import bad2
 M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
 C=Ctx(M);T=Ctx(M[:-1]);x=len(M)-1;r=x-1
 b,info=bad2(C,T)
 p=C.e.par(0,r);i=C.e.par(0,p)
 W=C.bumpW(i);WT=T.bumpW(i)
 df=[Y.tstr(q) for q in summ(C.vOpt1(i)) if not lt(q,W2) and not lt(q,WT) and lt(q,W) and not lhd(q,W)]
 return dict(bad2=b,info={k:v for k,v in info.items() if k!='W_candidates'},dropfail=df,srow=M[x][2])
