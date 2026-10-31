"""Exact Lean forms of two DropResHB fields (HDropU), on N with x = |N|-1, sigma = Ctx(N), sigma' = Ctx(N.take x):
 ua  (V3DropResHB): i = x-1, upg i = k, every decomposition v(k) = V + W (W != 0, V = vOpt(P1 i)):
     (all r in summands V, r < W -> Lhd 0 r W) or (WCSP N i (V+1) and all g in comps 0 (V+1), g < psi(V+1)).
     WCSP N i w = CS w or WCS (vOpt (P0 i)) w.   (codex UpgAbsXW0 additionally asks NBParX: stronger.)
 wsB (BumpWeakShapeSrcB): e1,e2 i != 0, j bump child of i, k child of j with o(k) = psi w y (w != 0),
     (k = x, ch j = [x], not v'(i) lhdE v(i)) or (k < x, o'(k) != o(k), not v'(k) lhdE v(k)),
     x child of i counted at i  ->  UpgBad(x-1) and BadPos."""
import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import probe_dropres as D
from probe_inv3_prefix import Ctx,Z,ONE,lt,le,app
from lhd_exact import lhd,lhdE,comps
import ytosk_eval as Y
def summ(t):
    out=[]
    while t:out.append((t[0],t[1],Z));t=t[2]
    return out
def decomps(V,vk):
    W=vk
    while W:
        if Y.add(V,W)==vk:yield W
        W=W[2]
def anc0(C,a,d):
    while d is not None:
        if d==a:return True
        d=C.e.par(0,d)
    return False
def upgbad(C,i):
    k=C.upg(i)
    if k is None:return False
    V=C.vOpt1(i)
    return any(any(lt(r,W) and not lhd(r,W) for r in summ(V)) for W in decomps(V,C.v(k)))
def badpos(C,x):
    p=C.e.par(0,x-1)
    if p is None:return False
    g=C.e.par(0,p)
    return g is not None and C.M[p]==C.e.bump(g) and anc0(C,g,x)
def ua(C):
    M=C.M;x=len(M)-1;i=x-1;res=[]
    if i<0:return res
    k=C.upg(i)
    if k is None:return res
    V=C.vOpt1(i);w=Y.add(V,ONE);p=C.e.par(0,i);vp=C.v(p) if p is not None else Z
    side=(D.CS(w) or D.WCS(vp,w)) and all(lt(g,(w,Z,Z)) for g in comps(Z,w))
    for W in decomps(V,C.v(k)):
        strong=all(not lt(r,W) or lhd(r,W) for r in summ(V))
        res.append(strong or side)
    return res
def wsB(C,T):
    M=C.M;x=len(M)-1;res=[]
    for i in range(len(M)):
        if not C.e12(i):continue
        if not (x in C.ch(i) and C.counted(i,x)):continue
        for j in C.ch(i):
            if M[j]!=C.e.bump(i):continue
            for k in C.ch(j):
                o=C.o(k)
                if not (o and o[0]!=Z and o[2]==Z):continue
                a1=k==x and C.ch(j)==[x] and not lhdE(T.v(i),C.v(i))
                a2=k<x and T.o(k)!=o and not lhdE(T.v(k),C.v(k))
                if a1 or a2:res.append(((i,j,k),upgbad(C,x-1) and badpos(C,x)))
    return res
def check(M):
    C=Ctx(M);T=Ctx(M[:-1]);return ua(C),wsB(C,T)
if __name__=='__main__':
    import re,json
    M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',sys.argv[1])]
    for j in range(2,len(M)+1):
        a,b=check(M[:j])
        if a or b:print(j,'ua',a,'wsB',b)
