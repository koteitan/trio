"""RDnodeCtr（根・末尾列の深さ 1）の形を確定する。"""
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

def main(maxlen=7,bdmax=1,plevmax=2,kmax=6,mmax=6):
    blocks=gen_blocks(maxlen,bdmax); stats=collections.Counter(); ex=collections.defaultdict(list)
    cnt=0
    for B in blocks:
        cnt+=1
        if cnt%2000==0: core._exp_memo.clear(); core._flat_memo.clear()
        bd=B[0][0]
        if bd!=0: continue
        if not (blockok(bd,B) and colOK(B) and descOK(B)): continue
        if not argPatOK(B) or not adjLev(B) or not argCtrOK(B): continue
        p,r=B[0],B[1:]; A,T=split(p,list(r))
        if T or len(B)<2 or B[-1][1]==0: continue
        if par1(B)!=0: continue
        if A[0][1]!=1: continue
        if B[-1][0]!=1: continue      # d0 = 1
        W=list(B[:-1])
        SW=shiftr0(1,W)
        for plev in range(0,plevmax+1):
            for first in (False,True):
                for force in (False,True):
                    if not hpOK(B,0,plev,first,force): continue
                    if not fOK(B,0,plev,force): continue
                    if not hlOK(B,plev): continue
                    if first and not headCtrOK(B,plev): continue
                    CB=convC(list(B),0,plev,first,force)
                    okA = (CB == [(0,0)]+shiftr0(1,list(B)))
                    okB = all(list(expand(tuple(CB),m))==[(0,0)]+copies(1,SW,m)
                              for m in range(1,mmax+1))
                    okC = all(convC(list(expand(tuple(B),k)),0,plev,first,force)
                              ==[(0,0)]+copies(1,SW,k-1) for k in range(3,kmax+1))
                    okC2 = all(convC(list(expand(tuple(B),k)),0,plev,first,force)
                              ==[(0,0)]+copies(1,SW,k-1) for k in range(1,kmax+1))
                    key=('A=%s'%okA,'B=%s'%okB,'C(k>=3)=%s'%okC,'C(k>=1)=%s'%okC2,
                         'Rnil=%s'%(len(W)==1))
                    stats[key]+=1
                    if len(ex[key])<3: ex[key].append((show(B),plev,first,force))
    print('stats:')
    for k,v in sorted(stats.items(),key=lambda t:str(t)):
        print('   ',k,v)
        for e in ex[k][:2]: print('        ',e)
if __name__=='__main__':
    a=sys.argv[1:]
    main(int(a[0]) if a else 7, int(a[1]) if len(a)>1 else 1)
