"""t = 1, q != r last-column frame: compare the true valuation of M[n] with the engine's glue
glueZ M x rho (shift rho_{M[n-1]}) (fun _ => gamS mu b seed (n-2)) and classify every deviation.
Bad shape (WfAbsW.BadAbsShape, structural part on M): m = P0 i = P1 i, CL i = [], CL m = Lc ++ [i], no j with upg j = i.
Claims checked per deviation:
  V1 v-deviation at i => i bump call (e1,e2 != 0), DepX false i, bad shape at i,
     true v(i) = sf(add(v(P1 i), fsD(bumpW i, zeta))), and some q in summands v(P1 i) with fsD(W,zeta) <= q < W.
  O1 o-deviation at c => c bad or c is a row-0 ancestor (P0-chain) of a bad column.
  LH  every D-o-call c < x: Lhd z (true o_N(c)) (o_M(c)) or equal; parent m of bad: Lhd z.
  TL  TPLoS low part: at D-o-calls c with o_M(c) = psi_s(y), y low part empty in M => low part of true o_N(c) empty."""
import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from probe_inv3_prefix import Ctx, Z, ONE, fs, fsD, holelev, lt, le, summ, ohole, split, succ, Y as YE
from probe_inv2 import dependencies
import ytosk_eval as YV
import lhd_exact as LX
import trio
from collections import Counter
ts=YE.tstr
def gamS(mu,b,seed,k):
    g=seed
    for _ in range(k): g=(mu,fs(b,g),Z)
    return g
def frame(M):
    C=Ctx(M)
    if not C.ok: return None
    x=len(M)-1
    if x<1 or M[x][2]!=0: return None
    r=C.e.par(1,x)
    if r is None or C.e.par(0,x)==r: return None
    o=C.o(r)
    if o==Z or o[2]!=Z: return None
    return C,x,r
def bad_shape(C,i):
    m=C.e.par(0,i)
    if m is None or C.e.par(1,i)!=m: return False
    if C.CL(i)!=[]: return False
    cl=C.CL(m)
    if not cl or cl[-1]!=i: return False
    if any(C.upg(j)==i for j in range(len(C.M))): return False
    return True
def anc0(C,c,b):
    while b is not None:
        if b==c: return True
        b=C.e.par(0,b)
    return False
def analyze(M, ns=(2,3,4), lhd=True, verbose=False):
    cnt=Counter(); ex={}
    f=frame(M)
    if f is None: return cnt,ex
    C,x,r=f; L=x-r
    T=Ctx(M[:x])
    if not T.ok: cnt['T_fail']+=1; return cnt,ex
    seed=T.o(r); mu,b,_=C.o(r)
    D=dependencies(C,x)
    cnt['frames']+=1
    prev=None
    for n in ns:
        E=[tuple(c) for c in trio.expand([list(c) for c in M],n)]
        CE=Ctx(E)
        if not CE.ok: cnt['exp_fail']+=1; continue
        zeta=gamS(mu,b,seed,n-2)
        badset=[]
        dev=False
        for i in range(x):
            for kind in ('v','o'):
                f0=C.v if kind=='v' else C.o
                g=CE.v(i) if kind=='v' else CE.o(i)
                dep=(kind=='o',i) in D
                glue=fsD(f0(i),zeta) if dep else f0(i)
                if glue==g: continue
                dev=True
                cnt['dev.'+kind]+=1
                if kind=='v':
                    ok = dep and C.e12(i) and bad_shape(C,i)
                    W=C.bumpW(i) if C.e12(i) else None
                    if ok:
                        V=C.vOpt1(i); W2=fsD(W,zeta)
                        ok = g==YV.sf(YV.add(V,W2)) and any(le(W2,q) and lt(q,W) for q in summ(V))
                        cnt['dev.v.WisA' if W==C.o(r) else 'dev.v.WnotA']+=1
                    cnt['V1.ok' if ok else 'V1.fail']+=1
                    if ok: badset.append(i)
                    elif 'V1' not in ex: ex['V1']=(M,n,i)
        for i in range(x):
            g=CE.o(i); dep=(True,i) in D
            glue=fsD(C.o(i),zeta) if dep else C.o(i)
            if glue!=g:
                ok=any(anc0(C,i,bb) for bb in badset)
                cnt['O1.ok' if ok else 'O1.fail']+=1
                if not ok and 'O1' not in ex: ex['O1']=(M,n,i)
        # columns from x on: shift of M[n-1]
        if prev is not None:
            for i in range(x,len(E)):
                if CE.o(i)!=prev.o(i-L) or CE.v(i)!=prev.v(i-L):
                    cnt['shift.fail']+=1; ex.setdefault('shift',(M,n,i))
        prev=CE
        if dev: cnt['dev.n%d'%n]+=1
        if lhd and dev:
            for i in range(x):
                if (True,i) not in D: continue
                a,bb=CE.o(i),C.o(i)
                ok = a==bb or LX.lhd(a,bb)
                cnt['LH.ok' if ok else 'LH.fail']+=1
                if not ok: ex.setdefault('LH',(M,n,i))
        # TL: low part of o
        for i in range(x):
            if (True,i) not in D: continue
            o=C.o(i)
            if o==Z or o[1]==Z: continue
            s,y=o[0],o[1]
            if split(y,(succ(s),Z,Z))[1]!=Z: continue
            on=CE.o(i)
            if on==Z or on[0]!=s: cnt['TL.shape']+=1; continue
            okt=split(on[1],(succ(s),Z,Z))[1]==Z or on[1]==Z
            cnt['TL.ok' if okt else 'TL.fail']+=1
            if not okt: ex.setdefault('TL',(M,n,i))
    return cnt,ex
if __name__=='__main__':
    N=[(0,0,0),(1,1,1),(2,1,1),(3,1,0),(1,1,1),(2,1,1),(3,0,0),(4,1,1),(5,1,1),(6,0,0),(7,1,1),(8,1,1),(9,0,0),(10,1,1),(11,1,1),(11,1,0),(12,1,0),(13,0,0),(10,0,0),(2,1,0),(3,2,1),(4,2,1),(5,0,0),(6,1,1),(7,1,1),(8,1,0)]
    print(analyze(N,(2,3,4,5)))

def fields(M):
    """Field-level checks on M only (no expansion).
    ADSX: AbsDS case (i, q) failing at the seed => bad shape at i.
    TPLX: TPLoS case at c failing => exists i with AbsDS failing at i, bad shape at i, c row-0 ancestor of P0 i,
          a = bumpW(i), and s <= v(P1 i)."""
    from probe_inv3_prefix import last, isSucc
    cnt=Counter(); ex={}
    f=frame(M)
    if f is None: return cnt,ex
    C,x,r=f
    T=Ctx(M[:x])
    if not T.ok: cnt['T_fail']+=1; return cnt,ex
    seed=T.o(r); mu,b,_=C.o(r)
    D=dependencies(C,x)
    cnt['frames']+=1
    badA=[]
    for i in range(x):
        if (False,i) not in D or not C.e12(i): continue
        W=C.bumpW(i)
        if not (ohole(W) and holelev(W)==mu): continue
        F=fsD(W,seed); fail=False
        for q in summ(C.vOpt1(i)):
            if lt(q,W):
                cnt['ADS.cases']+=1
                if not lt(q,F):
                    fail=True; cnt['ADS.fail']+=1
                    ok=bad_shape(C,i); cnt['ADSX.ok' if ok else 'ADSX.fail']+=1
                    cnt['ADS.fail.WisA' if W==C.o(r) else 'ADS.fail.WnotA']+=1
                    if not ok: ex.setdefault('ADSX',(M,i))
        if fail: badA.append(i)
    for c in range(x):
        if (True,c) not in D: continue
        o=C.o(c)
        if o==Z: continue
        s,y,_=o
        l=last(y)
        if (l and l[1]==Z and not isSucc(l[0]) and ohole(l[0]) and holelev(y)==mu and split(y,(succ(s),Z,Z))[1]==Z):
            cnt['TPL.cases']+=1
            if lt((fsD(l[0],seed),Z,Z),(succ(s),Z,Z)):
                cnt['TPL.fail']+=1
                ok=any(bad_shape(C,i) and anc0(C,c,C.e.par(0,i)) and l[0]==C.bumpW(i) and le(s,C.vOpt1(i)) for i in badA)
                cnt['TPLX.ok' if ok else 'TPLX.fail']+=1
                if not ok: ex.setdefault('TPLX',(M,c))
    return cnt,ex

def primary(M, ns=(2,3,4)):
    """Primary deviations: the call deviates although every input of its equation equals the glue.
    P.v.bad  : primary v deviation at a bump call with the bad shape, W = A = o(r), some q in [W[zeta], W)  (claim)
    P.v.other / P.o : anything else (should be 0)."""
    cnt=Counter(); ex={}
    f=frame(M)
    if f is None: return cnt,ex
    C,x,r=f
    T=Ctx(M[:x])
    if not T.ok: cnt['T_fail']+=1; return cnt,ex
    seed=T.o(r); mu,b,_=C.o(r); A_=C.o(r)
    D=dependencies(C,x)
    cnt['frames']+=1
    for n in ns:
        E=[tuple(c) for c in trio.expand([list(c) for c in M],n)]
        CE=Ctx(E)
        if not CE.ok: cnt['exp_fail']+=1; continue
        zeta=gamS(mu,b,seed,n-2)
        def gv(i): return (fsD(C.v(i),zeta) if (False,i) in D else C.v(i)) if i<x else CE.v(i)
        def go(i): return (fsD(C.o(i),zeta) if (True,i) in D else C.o(i)) if i<x else CE.o(i)
        anydev=False
        for i in range(x):
            if CE.v(i)!=gv(i):
                anydev=True
                p=CE.e.par(1,i)
                inV = (CE.v(p)==gv(p)) if p is not None else True
                if E[i][2]==0:
                    k=CE.upg(i); inK=(CE.v(k)==gv(k)) if k is not None else True
                    prim=inV and inK
                else:
                    prim=inV and all(CE.o(d)==go(d) for j in CE.ch(i) for d in CE.ch(j))
                if prim:
                    if C.e12(i):
                        W=C.bumpW(i); W2=fsD(W,zeta)
                        ok=bad_shape(C,i) and W==A_ and any(le(W2,q) and lt(q,W) for q in summ(C.vOpt1(i)))
                        cnt['P.v.bad' if ok else 'P.v.bumpother']+=1
                        if not ok: ex.setdefault('Pvb',(M,n,i))
                    else:
                        cnt['P.v.upg']+=1; ex.setdefault('Pvu',(M,n,i))
            if CE.o(i)!=go(i):
                anydev=True
                prim = CE.v(i)==gv(i) and all(CE.o(d)==go(d) for d in CE.ch(i))
                if prim: cnt['P.o']+=1; ex.setdefault('Po',(M,n,i))
        if anydev: cnt['dev.n%d'%n]+=1
    return cnt,ex

def closure(C, leaves, x):
    """DepX closure (V3Dep.lean constructors) below x from the given leaves."""
    D=set(leaves)
    while True:
        before=len(D)
        for i,col in enumerate(C.M[:x]):
            if (False,i) in D or any((True,c) in D for c in C.CL(i)): D.add((True,i))
            if col[1]==0: continue
            p=C.e.par(1,i); hit=p is not None and (False,p) in D
            if col[2]==0:
                k=C.upg(i); hit|= k is not None and (False,k) in D
            else:
                hit|=any(C.M[j]==C.e.bump(i) and any((True,k) in D for k in C.ch(j)) for j in C.ch(i))
            if hit: D.add((False,i))
        if len(D)==before: return D

def scope(M, ns=(2,3)):
    """With B = primary bad v-calls (bad shape, W = A, window nonempty) and DB = closure(B):
    SC.out : every deviation from the glue lies in DB                (claim)
    SC.ge  : at deviating calls, glue <= true                        (claim)
    SC.lt  : at deviating o-calls and v-calls, true < old M value    (claim)"""
    cnt=Counter(); ex={}
    f=frame(M)
    if f is None: return cnt,ex
    C,x,r=f
    T=Ctx(M[:x])
    if not T.ok: return cnt,ex
    seed=T.o(r); mu,b,_=C.o(r); A_=C.o(r)
    D=dependencies(C,x)
    Bc=[]
    for i in range(x):
        if (False,i) in D and C.e12(i) and bad_shape(C,i):
            W=C.bumpW(i)
            if W==A_ and ohole(W) and holelev(W)==mu: Bc.append(i)
    for n in ns:
        E=[tuple(c) for c in trio.expand([list(c) for c in M],n)]
        CE=Ctx(E)
        if not CE.ok: continue
        zeta=gamS(mu,b,seed,n-2)
        B=[i for i in Bc if any(le(fsD(A_,zeta),q) and lt(q,A_) for q in summ(C.vOpt1(i)))]
        DB=closure(C,{(False,i) for i in B},x)
        for i in range(x):
            for kind in (False,True):
                old=C.o(i) if kind else C.v(i)
                tru=CE.o(i) if kind else CE.v(i)
                glue=fsD(old,zeta) if (kind,i) in D else old
                if tru==glue: continue
                cnt['SC.dev']+=1
                ok=(kind,i) in DB; cnt['SC.out.ok' if ok else 'SC.out.fail']+=1
                if not ok: ex.setdefault('SCout',(M,n,i,kind))
                ok=le(glue,tru); cnt['SC.ge.ok' if ok else 'SC.ge.fail']+=1
                if not ok: ex.setdefault('SCge',(M,n,i,kind))
                ok=lt(tru,old); cnt['SC.lt.ok' if ok else 'SC.lt.fail']+=1
                if not ok: ex.setdefault('SClt',(M,n,i,kind))
        cnt['SC.B']+=len(B)
    return cnt,ex
