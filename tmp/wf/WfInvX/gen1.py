"""Data for WfInvX1.lean: the 26-column standard matrix where AbsDS and TPLoS fail."""
import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/claude')
sys.argv=['x']
import reach as R
import ytosk_eval as Y
from probe_inv3_prefix import Ctx,lt,fsD,ONE,summ,last,split,succ,holelev,ohole,isSucc,Z
S='(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(4,1,1)(5,1,1)(6,0,0)(7,1,1)(8,1,1)(9,0,0)(10,1,1)(11,1,1)(11,1,0)(12,1,0)(13,0,0)(10,0,0)(2,1,0)(3,2,1)(4,2,1)(5,0,0)(6,1,1)(7,1,1)(8,1,0)'
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',S)]
x=len(M)-1
p=R.reach(M);assert p is not None
def L(t):
 if not t:return 'z'
 return '(psi %s %s %s)'%(L(t[0]),L(t[1]),L(t[2]))
C=Ctx(M);T=Ctx(M[:x]);r=C.e.par(1,x);seed=T.o(r)
# DepX closure with derivations
D={(True,x):('leaf',)}
ch=True
while ch:
 ch=False
 for i,col in enumerate(M):
  if (True,i) not in D:
   if (False,i) in D:D[(True,i)]=('ov',i);ch=True
   else:
    for c in C.CL(i):
     if (True,c) in D:D[(True,i)]=('ochild',i,c);ch=True;break
  if col[1]==0 or (False,i) in D:continue
  m=C.e.par(1,i)
  if m is not None and (False,m) in D:D[(False,i)]=('vpar',i,m);ch=True;continue
  if col[2]==0:
   k=C.upg(i)
   if k is not None and (False,k) in D:D[(False,i)]=('vupg',i,k);ch=True;continue
  else:
   for j in C.ch(i):
    if M[j]==C.e.bump(i):
     for k in C.ch(j):
      if (True,k) in D and (False,i) not in D:D[(False,i)]=('vbump',i,j,k);ch=True
def deriv(key):
 d=D[key]
 if d[0]=='leaf':return 'DepX.leaf'
 if d[0]=='ov':return '(DepX.ov %s)'%deriv((False,d[1]))
 if d[0]=='ochild':return '(DepX.ochild (c := %d) (by decide) (by decide) (by decide) %s)'%(d[2],deriv((True,d[2])))
 if d[0]=='vpar':return '(DepX.vpar (m := %d) (by decide) (by decide) %s)'%(d[2],deriv((False,d[2])))
 if d[0]=='vupg':return '(DepX.vupg (k := %d) (by decide) (by decide) (by decide) %s)'%(d[2],deriv((False,d[2])))
 if d[0]=='vbump':return '(DepX.vbump (j := %d) (k := %d) (by decide) (by decide) (by decide) (by decide) (by decide) %s)'%(d[2],d[3],deriv((True,d[3])))
i=20;W=C.bumpW(i);qs=[q for q in summ(C.vOpt1(i)) if lt(q,W) and not lt(q,fsD(W,seed))]
c=4;s,y,_=C.o(c);a=last(y)[0]
print('-- trace',len(p),'r',r,'q',C.e.par(0,x),'o r',Y.tstr(C.o(r)),'seed',Y.tstr(seed))
print('-- AbsDS i',i,'W',Y.tstr(W),'holelev',Y.tstr(holelev(W)),'q',Y.tstr(qs[0]),'fsD',Y.tstr(fsD(W,seed)))
print('-- TPLoS c',c,'s',Y.tstr(s),'y',Y.tstr(y),'a',Y.tstr(a),'holelev y',Y.tstr(holelev(y)),'fsD a seed',Y.tstr(fsD(a,seed)))
print('def N : Mat := ['+', '.join('(%d, %d, %d)'%c for c in M)+']')
print('def trace : List Nat := ['+', '.join(map(str,p))+']')
print('def ρO : List T := ['+', '.join(L(C.o(i)) for i in range(len(M)))+']')
print('def ρV : List T := ['+', '.join(L(C.v(i)) for i in range(len(M)))+']')
print('def σO : List T := ['+', '.join(L(T.o(i)) for i in range(x))+']')
print('def σV : List T := ['+', '.join(L(T.v(i)) for i in range(x))+']')
print('def Wl : T := '+L(W))
print('def q0 : T := '+L(qs[0]))
print('def μ0 : T := '+L(C.o(r)[0]))
print('def b0 : T := '+L(C.o(r)[1]))
print('def s4 : T := '+L(s))
print('def y4 : T := '+L(y))
print('def a4 : T := '+L(a))
print('theorem dep20 : DepX N 25 false 20 := '+deriv((False,20)))
print('theorem dep4 : DepX N 25 true 4 := '+deriv((True,4)))
