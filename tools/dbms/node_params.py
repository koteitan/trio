"""convC_append_tail の (d',plev',first',force') を Python で再現し、
RDnode の正則 regime で「段 1 のフラグ」がどうなるかを見る。"""
import sys, collections
sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import core
from core import expand, show
from rows2 import convC, split, colOK, descOK
from resid_check import (blockok, argPatOK, argCtrOK, adjLev, hpOK, fOK, hlOK,
                         ladOf, par1, headCtrOK, gen_blocks)

def ddOf(s,d,plev,first,force):
    if ladOf(s,d,plev,first,force): return d+1
    return s+1 if (s>0 and d<=s) else d

def tail_params(M, nu, d, plev, first, force):
    """convC_append_tail の (d',plev',first',force') を再現（梯子なしの再帰）。"""
    while True:
        if not M: return (d,plev,first,force)
        c, r = M[0], M[1:]
        A, Bs = split(c, list(r))
        dd = ddOf(c[1], d, plev, first, force)
        if Bs:
            M, d, plev, first, force = Bs, d, c[1], False, False
        elif nu <= c[0]:
            return (d, c[1], False, False)
        else:
            M, d, plev, first, force = list(A), dd+1, c[1], True, (first and c[1]==plev)

def main(maxlen=5,bdmax=2,plevmax=2):
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
        W=list(B[:-1]); R=list(A[:-1]); w0=p[1]; lp=A[-1]; nu=lp[0]
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
                        if lad0 or not levlt: continue     # 正則 regime だけ
                        phi = first and (w0==plev)
                        d1,pl1,f1,fo1 = tail_params(R, nu, dd+1, w0, True, phi)
                        phi1 = f1 and (w0==pl1)
                        Rhead_eq = bool(R) and R[0][1]==w0+1
                        stats[('phi=%s'%phi,'first1=%s'%f1,'phi1=%s'%phi1,
                               'nu<=d1=%s'%(nu<=d1),'Rhd=%s'%Rhead_eq)]+=1
                        k=('phi1=%s'%phi1,'Rhd=%s'%Rhead_eq)
                        if len(ex[k])<2: ex[k].append((show(B),d,plev,first,force,(d1,pl1,f1,fo1)))
    print('stats:')
    for k,v in sorted(stats.items(),key=lambda t:str(t)): print('   ',k,v)
    print('examples:')
    for k,v in sorted(ex.items(),key=lambda t:str(t)): print('   ',k,v)
if __name__=='__main__':
    a=sys.argv[1:]
    main(int(a[0]) if a else 5, int(a[1]) if len(a)>1 else 2)
