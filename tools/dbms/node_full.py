"""RDnode の 3 つの regime を細かく測る。"""
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

def find_mn(C0, B, d, plev, first, force, nmax=4, mmax=16, dn=4):
    """各 n について (m, n') を探す。"""
    out=[]
    for n in range(1,nmax+1):
        found=None
        for np_ in range(n,n+dn+1):
            tgt=tuple(convC(list(expand(tuple(B),np_)),d,plev,first,force))
            for m in range(1,mmax+1):
                if tuple(expand(tuple(C0),m))==tgt: found=(m,np_); break
            if found: break
        out.append(found)
    return out

def main(maxlen=5,bdmax=2,plevmax=2,nmax=4):
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
        d0=B[-1][0]-p[0]
        for d in (bd,bd+1):
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
                        dd=ddOf(w0,d,plev,first,force)
                        levlt = (not R) or R[0][1] < dd+1
                        CB=convC(list(B),d,plev,first,force)
                        CW=convC(W,d,plev,first,force)
                        # regime
                        if lad0: reg='lad'
                        elif not levlt: reg='contr'
                        else: reg='reg'
                        pref = (CB[:len(CW)]==CW)
                        tail = CB[len(CW):] if pref else None
                        mn=find_mn(CB,B,d,plev,first,force,nmax)
                        okmn = all(x is not None for x in mn)
                        mlist = tuple(x[0]-nn-1 for nn,x in enumerate(mn)) if okmn else None
                        nlist = tuple(x[1]-nn-1 for nn,x in enumerate(mn)) if okmn else None
                        key=(reg,'pref=%s'%pref,'tlen=%s'%(len(tail) if tail is not None else '?'),
                             'ok=%s'%okmn,'m-n=%s'%(mlist,),'np-n=%s'%(nlist,))
                        stats[key]+=1
                        if len(ex[key])<3: ex[key].append((show(B),d,plev,first,force,d0,tail,CW[:2]))
    print('stats:')
    for k,v in sorted(stats.items(),key=lambda t:str(t)):
        print('   ',k,v)
        for e in ex[k][:2]: print('        ',e)
if __name__=='__main__':
    a=sys.argv[1:]
    main(int(a[0]) if a else 5, int(a[1]) if len(a)>1 else 2)
