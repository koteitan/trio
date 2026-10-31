"""t = 2 expansions M[n] (n = 2, 3): which calls i < x lose Lhd z, and what holds there.
usage: probe_fail.py set.pkl [nproc] [limit]"""
import sys,re,pickle,collections,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from multiprocessing import Pool
from probe_inv3_prefix import Ctx,Z,lt,le,summ
import trio, ytosk_eval as Y
from lhd_exact import lhd, comps, tmax, indices, ex_K, succ
def lhd_eta(b,a,eta):
    if not lt(b,a): return False
    us=set(); indices(b,us); I=(succ(b),(a,True))
    for u in us:
        g=tmax(comps(u,b))
        if not g: continue
        H=tmax(comps(u,eta))
        if not lt(H,g): continue
        if ex_K(u,g)(I): return False
    return True
def mt(M): return ''.join('(%d,%d,%d)'%tuple(c) for c in M)
def anc0(E,a,d):
    while d is not None:
        if d==a: return True
        d=E.par(0,d)
    return False
def one(M):
    out=collections.Counter(); ex={}
    if len(M)<3 or M[-1][2]==0: return out,ex
    C=Ctx(M)
    if not C.ok: return out,ex
    x=len(M)-1; E=C.e
    for n in (2,3):
        N=trio.expand(M,n); CN=Ctx(N)
        if not CN.ok: out['N.noval']+=1; continue
        out['pairs']+=1
        bad=[]
        for i in range(x):
            for kind,a,b in (('o',C.o(i),CN.o(i)),('v',C.v(i),CN.v(i))):
                if a==b: continue
                if not lhd(b,a): bad.append((kind,i,a,b))
        if not bad: continue
        out['pairs.fail']+=1
        for kind,i,a,b in bad:
            q=E.par(0,x); r=E.par(2,x)
            tag=[kind,'i=q' if i==q else ('i=r' if i==r else ('i=x-1' if i==x-1 else 'i=other'))]
            p0=E.par(0,i); p1=E.par(1,i)
            V=C.v(p1) if p1 is not None else Z
            tag.append('lt' if lt(b,a) else 'NOTLT')
            tag.append('e12' if C.e12(i) else 'note12')
            tag.append('P0=P1' if p0==p1 else 'P0!=P1')
            tag.append('lhdV' if lhd_eta(b,a,V) else 'noLhdV')
            if kind=='o':
                tag.append('vsame' if C.v(i)==CN.v(i) else 'vchg')
            # recovery along P0
            d=p0; dist=1; rec=None
            while d is not None:
                aa,bb=C.o(d),CN.o(d)
                if aa==bb: rec='eq'; break
                if lhd(bb,aa): rec='lhd'; break
                d=E.par(0,d); dist+=1
            tag.append('rec=%s@%d'%(rec,dist))
            if p0 is not None:
                tag.append('cnt' if C.counted(p0,i) else 'notcnt')
                tag.append('lastcnt' if C.CL(p0) and C.CL(p0)[-1]==i else 'notlast')
                tag.append('vP0same' if C.v(p0)==CN.v(p0) else 'vP0chg')
            key=' '.join(tag)
            out[key]+=1
            if key not in ex: ex[key]=(mt(M),n,i)
    return out,ex
def run(batch):
    cnt=collections.Counter(); ex={}
    for M in batch:
        try: c,e=one([tuple(t) for t in M])
        except RecursionError: cnt['rec']+=1; continue
        cnt.update(c)
        for k,v in e.items(): ex.setdefault(k,v)
    return cnt,ex
if __name__=='__main__':
    d=pickle.load(open(sys.argv[1],'rb'))
    d=[m for m in d if len(m)>=3 and m[-1][2]!=0]
    np=int(sys.argv[2]) if len(sys.argv)>2 else 4
    lim=int(sys.argv[3]) if len(sys.argv)>3 else len(d)
    d=d[:lim]
    B=[d[k::np*8] for k in range(np*8)]
    cnt=collections.Counter(); ex={}
    with Pool(np) as P:
        for c,e in P.imap_unordered(run,B):
            cnt.update(c)
            for k,v in e.items(): ex.setdefault(k,v)
    print(sys.argv[1],len(d))
    for k,v in sorted(cnt.items()): print(' ',v,k)
    for k,v in ex.items(): print('EX',k,v)
