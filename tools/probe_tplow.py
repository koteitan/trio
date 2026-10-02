"""TPLoW・AbsDW（V3QRKeep・V3QRLocV）の実測: 最後の列が t = 1・q = r の行列 M で、D = DepX M x の列の
使い所の条件を、旧形（η = ψ_μ(1)）と新形（η = gamS μ b_r 1 (max 1 dOf)）で評価する。

usage: python3 probe_tplow.py SEEDS.pkl MAXLEN
  SEEDS.pkl の各行列（長さ ≤ MAXLEN）の M[2]・M[3] の接頭辞（長さ ≤ 30、t = 1 のもの）を測る。
"""
import sys, pickle
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_inv3_prefix import *
import ytosk_eval2 as Y2
from collections import Counter
from multiprocessing import Pool
def S(M): return ''.join('(%d,%d,%d)'%t for t in M)
class Ctx:
    def __init__(s,M):
        s.M=M; s.e=Y2.Ev2(M); s.e.value()
    def o(s,i): return s.e.o(i)
    def v(s,i): return s.e.v(i)
    def ch(s,i): return s.e.children[i]
    def counted(s,i,d): return s.M[d]!=s.e.bump(i) and not (d in s.e.upgs and s.e.topped(d))
    def vOpt1(s,i):
        m=s.e.par(1,i); return s.v(m) if m is not None else Z
    def bumpTerm(s,i,j):
        return Y.omega(sumN([s.o(k) for k in s.ch(j)])) if s.M[j]==s.e.bump(i) else Z
    def bumpW(s,i): return Y.omega(sumN([ONE]+[s.bumpTerm(i,j) for j in s.ch(i)]))
def deps(C,b,i):
    M=C.M; e=C.e; out=[]
    if b=='o':
        out.append(('v',i))
        for c in e.children[i]:
            if C.counted(i,c): out.append(('o',c))
    else:
        if M[i][1]==0: return out
        p=e.par(1,i)
        if p is not None: out.append(('v',p))
        if M[i][2]==0:
            u=e._upg[i]
            if u is not None: out.append(('v',u))
        else:
            for j in e.children[i]:
                if M[j]==e.bump(i):
                    for k in e.children[j]: out.append(('o',k))
    return out
def depX(C,x):
    D={('o',x)}; ch=True
    while ch:
        ch=False
        for i in range(len(C.M)):
            for b in ('o','v'):
                if (b,i) not in D and any(d in D for d in deps(C,b,i)): D.add((b,i)); ch=True
    return D
import trio
INF=10**9
def pre(C,i,L):
    return spa(C.v(i), sumN([t for t in ((C.o(d) if C.counted(i,d) else Z) for d in L) if t!=Z]))
def dofs(C,x,A,br):
    M=C.M; e=C.e; n=len(M)
    d={('o',x):0}
    def g(k): return d.get(k,INF)
    ch=True
    while ch:
        ch=False
        for i in range(n):
            # o
            best=g(('v',i))
            for c in e.children[i]:
                if C.counted(i,c) and g(('o',c))<INF:
                    L=[t for t in e.children[i] if t<c]
                    lo=1 if (C.o(c)==A and lt(pre(C,i,L),br) and lt((C.v(i),Z,Z),A)) else 0
                    best=min(best,g(('o',c))+lo)
            if i==x: best=0
            if best<g(('o',i)): d[('o',i)]=best; ch=True
            # v
            if M[i][1]==0: continue
            best=INF
            p=e.par(1,i)
            if p is not None: best=min(best,g(('v',p)))
            if M[i][2]==0:
                u=e._upg[i]
                if u is not None: best=min(best,g(('v',u)))
            else:
                for j in e.children[i]:
                    if M[j]==e.bump(i):
                        for k in e.children[j]:
                            if g(('o',k))<INF:
                                lb=0
                                if e.children[j]==[k] and C.o(k)==A:
                                    bt=[C.bumpTerm(i,jj) for jj in e.children[i] if jj<j]
                                    lb=2 if sumN([t for t in bt if t!=Z])==Z else 1
                                best=min(best,g(('o',k))+lb)
            if best<g(('v',i)): d[('v',i)]=best; ch=True
    return d
def dOf(d,i):
    if ('v',i) in d: return d[('v',i)]
    return d.get(('o',i),0)
def G(mu,br,k):
    t=ONE
    for _ in range(k): t=(mu,fs(br,t),Z)
    return t
def one2(m):
    c=Counter(); ex={}
    def note(k,ok,info):
        c[(k,ok)]+=1
        if not ok and k not in ex: ex[k]=(m,info)
    M=list(m); x=len(M)-1
    if x<1 or M[x][2]!=0 or M[x][1]==0: return c,ex
    C=Ctx(M); e=C.e
    r=e.par(1,x); q=e.par(0,x)
    if r is None or q!=r: return c,ex
    A=C.o(r); mu=A[0]; br=A[1]
    if not br or cof(br)!=('big',mu) or last(br)!=(succ(mu),Z,Z): return c,ex
    dd=dofs(C,x,A,br)
    for i in range(x):
        k=max(1,dOf(dd,i)); eta=G(mu,br,k)
        if ('o',i) in dd:
            s,y,_=C.o(i)
            if y and y!=br and split(y,(succ(s),Z,Z))[1]==Z:
                l=last(y)
                if not l[1]:
                    a=l[0]
                    if not isSucc(a) and ohole(a) and cof(a)[0]=='omega':
                        th=(succ(s),Z,Z)
                        note('TPLoW.old',not lt((fsD(a,(mu,ONE,Z)),Z,Z),th),i)
                        note('TPLoW.d',not lt((fsD(a,eta),Z,Z),th),(i,k))
        if ('v',i) in dd and M[i][1] and M[i][2]:
            W=C.bumpW(i)
            if ohole(W) and cof(W)[0]=='omega':
                qs=[t for t in summ(C.vOpt1(i)) if lt(t,W)]
                note('AbsDW.old',all(lt(t,fsD(W,(mu,ONE,Z))) for t in qs),i)
                note('AbsDW.d',all(lt(t,fsD(W,eta)) for t in qs),(i,k))
    return c,ex
def work(m):
    M=list(m); c=Counter(); ex={}
    if not M or M[-1]==(0,0,0): return c,ex
    seen=set()
    for n in (2,3):
        N=trio.expand(M,n)
        for j in range(len(M),min(len(N),30)+1):
            P=tuple(N[:j])
            if P in seen: continue
            seen.add(P)
            if P[-1][2]!=0 or P[-1][1]==0: continue
            cc,ee=one2(P); c.update(cc)
            for k,v in ee.items(): ex.setdefault(k,v)
    return c,ex
if __name__=='__main__':
    mats=pickle.load(open(sys.argv[1],'rb'))
    mats=[m for m in mats if len(m)<=int(sys.argv[2])]
    tot=Counter(); exs={}
    with Pool(26) as p:
        for cc,ee in p.imap_unordered(work,mats,chunksize=50):
            tot.update(cc)
            for k,v in ee.items(): exs.setdefault(k,v)
    for k in sorted(tot,key=str): print(k,tot[k])
    for k,(M,i) in exs.items(): print(k,i,S(M))
