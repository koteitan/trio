"""(H1) p.2 < D なら convC(copies d0 W n) = copies d0 (convC W) n を検査。"""
import sys, collections
sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import core
from core import expand, show
from rows2 import convC, split, colOK, descOK
from resid_check import (blockok, argPatOK, argCtrOK, adjLev, hpOK, fOK, hlOK,
                         ladOf, par1, headCtrOK, gen_blocks)

def shiftr0(e,M): return [(a+e,b) for a,b in M]
def copies(e,blk,n):
    out=[]
    for k in range(n): out+=shiftr0(k*e,blk)
    return out
def ddOf(s,d,plev,first,force):
    if ladOf(s,d,plev,first,force): return d+1
    return s+1 if (s>0 and d<=s) else d

def main(maxlen=5,bdmax=2,plevmax=2,nmax=4,dextra=2):
    blocks=gen_blocks(maxlen,bdmax); stats=collections.Counter(); ex=collections.defaultdict(list)
    cnt=0
    for B in blocks:
        cnt+=1
        if cnt%2000==0: core._exp_memo.clear(); core._flat_memo.clear()
        bd=B[0][0]
        if not (blockok(bd,B) and colOK(B) and descOK(B)): continue
        if not argPatOK(B) or not adjLev(B) or not argCtrOK(B): continue
        p,r=B[0],B[1:]; A,T=split(p,list(r))
        if T or len(B)<2 or B[-1][1]==0: continue
        if par1(B)!=0: continue
        W=list(B[:-1]); R=list(A[:-1]); w0=p[1]
        lp=B[-1]; nu=lp[0]; d0=nu-p[0]
        for d in range(bd,bd+dextra+1):
            for plev in range(0,plevmax+1):
                if plev>d: continue
                for first in (False,True):
                    if first and d==bd and not (plev==0 or plev+1<bd): continue
                    for force in (False,True):
                        if not hpOK(B,d,plev,first,force): continue
                        if not fOK(B,d,plev,force): continue
                        if not hlOK(B,plev): continue
                        if first and not headCtrOK(B,plev): continue
                        lad0=ladOf(w0,d,plev,first,force)
                        CW=convC(W,d,plev,first,force)
                        h1=all(tuple(convC(copies(d0,W,n),d,plev,first,force))
                               ==tuple(copies(d0,CW,n)) for n in range(1,nmax+1))
                        # H2
                        h2=None
                        if lad0:
                            h2=all(tuple(convC(copies(d0,W,n),d,plev,first,force))
                                   ==[(d,plev)]+list(convC(copies(d0,W,n),d+1,plev,False,False))
                                   for n in range(1,nmax+1))
                        key=('lt=%s'%(w0<d),'lad=%s'%lad0,'H1=%s'%h1,'H2=%s'%h2)
                        stats[key]+=1
                        if len(ex[key])<2: ex[key].append((show(B),d,plev,first,force,d0))
    print('stats:')
    for k,v in sorted(stats.items(),key=lambda t:str(t)):
        print('   ',k,v)
        for e in ex[k][:2]: print('        ',e)
if __name__=='__main__':
    a=sys.argv[1:]
    main(int(a[0]) if a else 5, int(a[1]) if len(a)>1 else 2)
