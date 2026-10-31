"""Data for WfExQ12.lean: the standard 39-column matrix (graftE) where AbsUWL fails (i = 34, k = 35, r = 37)."""
import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/claude')
sys.argv=['x']
import reach as R
import ytosk_eval as Y
from probe_inv3_prefix import Ctx,lt,fsD,ONE,summ,last,split,succ,holelev,ohole,isSucc,Z,cof,fs
from probe_trigs0 import lift_counts
S='(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)(6,2,1)(7,2,1)(8,2,0)(6,2,1)(7,2,1)(8,1,0)(9,2,1)(10,2,1)(11,2,0)(9,2,1)(10,2,1)(11,1,0)(12,0,0)(13,1,1)(10,2,0)(11,3,1)(12,3,1)(13,1,0)(14,2,1)(12,3,0)(11,3,1)(12,3,1)(13,1,0)(14,2,0)'
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',S)]
x=len(M)-1
p=R.reach(M);assert p is not None
def L(t):
 if not t:return 'z'
 return '(psi %s %s %s)'%(L(t[0]),L(t[1]),L(t[2]))
C=Ctx(M);r=C.e.par(1,x);A=C.o(r);mu,br,_=A
d=lift_counts(C,x,A)
# weighted derivation: edges as in lift_counts, with the Lean constructor names
br_=br
dist={(True,x):0};how={(True,x):('leaf',)}
def lo(i,c,idx):return int(C.o(c)==A and lt(C.pre(i,C.ch(i)[:idx]),br) and lt((C.v(i),Z,Z),A))
ch=True
while ch:
 ch=False
 for i,col in enumerate(M):
  # ov
  if (False,i) in dist and dist[(False,i)]<dist.get((True,i),9e9):dist[(True,i)]=dist[(False,i)];how[(True,i)]=('ov',i);ch=True
  for idx,c in enumerate(C.ch(i)):
   if C.counted(i,c) and (True,c) in dist:
    w=dist[(True,c)]+lo(i,c,idx)
    if w<dist.get((True,i),9e9):dist[(True,i)]=w;how[(True,i)]=('ochild',i,c,lo(i,c,idx));ch=True
  if col[1]==0:continue
  m=C.e.par(1,i)
  if m is not None and (False,m) in dist and dist[(False,m)]<dist.get((False,i),9e9):dist[(False,i)]=dist[(False,m)];how[(False,i)]=('vpar',i,m);ch=True
  if col[2]==0:
   k=C.upg(i)
   if k is not None and (False,k) in dist and dist[(False,k)]<dist.get((False,i),9e9):dist[(False,i)]=dist[(False,k)];how[(False,i)]=('vupg',i,k);ch=True
  else:
   for idx,j in enumerate(C.ch(i)):
    if M[j]!=C.e.bump(i):continue
    for k in C.ch(j):
     if (True,k) not in dist:continue
     lb=0
     if C.ch(j)==[k] and C.o(k)==A:
      from probe_inv3_prefix import sumN
      prior=sumN([C.bumpTerm(i,jj) for jj in C.ch(i)[:idx]]);lb=2 if prior==Z else 1
     w=dist[(True,k)]+lb
     if w<dist.get((False,i),9e9):dist[(False,i)]=w;how[(False,i)]=('vbump',i,j,k,lb);ch=True
assert dist[(False,34)]==d[34]==2,(dist.get((False,34)),d[34])
steps=[]
def deriv(key):
 h=how[key]
 if h[0]=='leaf':return 'DepL.leaf'
 if h[0]=='ov':return '(DepL.ov %s)'%deriv((False,h[1]))
 if h[0]=='ochild':steps.append(('lo',h[1],h[2],h[3]));return '(DepL.ochild (c := %d) (by decide) (by decide) (by decide) %s)'%(h[2],deriv((True,h[2])))
 if h[0]=='vpar':return '(DepL.vpar (m := %d) (by decide) (by decide) %s)'%(h[2],deriv((False,h[2])))
 if h[0]=='vupg':return '(DepL.vupg (k := %d) (by decide) (by decide) (by decide) %s)'%(h[2],deriv((False,h[2])))
 if h[0]=='vbump':steps.append(('lb',h[1],h[2],h[3],h[4]));return '(DepL.vbump (j := %d) (k := %d) (by decide) (by decide) (by decide) (by decide) (by decide) %s)'%(h[2],h[3],deriv((True,h[3])))
dl=deriv((False,34))
i=34;k=C.upg(i);W=last(C.v(k));V=C.vOpt1(i)
# b: br = b + Om_{mu+1}
from probe_inv3_prefix import app
bb=split(br,(succ(mu),Z,Z))  # not used
def initp(t):
 # t = psi a b c ; drop last summand
 if not t[2]:return Z
 return (t[0],t[1],initp(t[2]))
b0=initp(br);assert app(b0,(succ(mu),Z,Z))==br
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA'); from probe_adn import gamS
eta=gamS(mu,br,ONE,2);F=fsD(W,eta)
qs=[q for q in summ(V) if lt(q,W) and not lt(q,F)]
print('-- trace',len(p),'x',x,'r',r,'q',C.e.par(0,x),'i',i,'k',k,'d_i',d[i],'o r',Y.tstr(A))
print('-- W',Y.tstr(W),'q',Y.tstr(qs[0]),'eta',Y.tstr(eta),'fsD',Y.tstr(F),'cof',cof(W),'ohole',ohole(W))
print('-- steps',steps)
print('def N : Mat := ['+', '.join('(%d, %d, %d)'%c for c in M)+']')
print('def trace : List Nat := ['+', '.join(map(str,p))+']')
print('def ρO : List T := ['+', '.join(L(C.o(i)) for i in range(len(M)))+']')
print('def ρV : List T := ['+', '.join(L(C.v(i)) for i in range(len(M)))+']')
print('def Wl : T := '+L(W))
print('def q0 : T := '+L(qs[0]))
print('def μ0 : T := '+L(mu))
print('def b0 : T := '+L(b0))
print('def η0 : T := '+L(eta))
print('def depL34 := '+dl)
