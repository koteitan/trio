"""RDnode の例外 2 つ（梯子・跳び）で convC B = [x] ++ shiftr0 1 B かを検査。"""
import sys, collections
sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import core
from core import expand, show
from rows2 import convC, split, colOK, descOK
from resid_check import (blockok, argPatOK, argCtrOK, adjLev, hpOK, fOK, hlOK,
                         ladOf, par1, headCtrOK, gen_blocks)

def shiftr0(e,M): return [(a+e,b) for a,b in M]
def ddOf(s,d,plev,first,force):
    if ladOf(s,d,plev,first,force): return d+1
    return s+1 if (s>0 and d<=s) else d

def main(maxlen=6,bdmax=2,plevmax=3,nmax=4):
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
        lp=B[-1]; d0=lp[0]-p[0]
        for d in range(bd,bd+3):
            for plev in range(0,plevmax+1):
                if plev>d: continue
                for first in (False,True):
                    if first and d==bd and not (plev==0 or plev+1<bd): continue
                    for force in (False,True):
                        if not hpOK(B,d,plev,first,force): continue
                        if not fOK(B,d,plev,force): continue
                        if not hlOK(B,plev): continue
                        if first and not headCtrOK(B,plev): continue
                        lad0=ladOf(p[1],d,plev,first,force)
                        dd=ddOf(p[1],d,plev,first,force)
                        exc = lad0 or not (A[0][1] < dd+1)
                        if not exc: continue
                        CB=convC(list(B),d,plev,first,force)
                        tgt1=[(d,plev)]+shiftr0(1,list(B))
                        tgt2=[p]+shiftr0(1,list(B))
                        ok = 'lad' if CB==tgt1 else ('jmp' if CB==tgt2 else 'NO')
                        # 展開後も同じか
                        okn=all(convC(list(expand(tuple(B),k)),d,plev,first,force)
                                ==([(d,plev)] if lad0 else [p])+shiftr0(1,list(expand(tuple(B),k)))
                                for k in range(1,nmax+1))
                        key=('lad=%s'%lad0,'form=%s'%ok,'oper=%s'%okn,'d0=%s'%('1' if d0==1 else '>=2'))
                        stats[key]+=1
                        if len(ex[key])<3: ex[key].append((show(B),d,plev,first,force,d0,CB))
    print('stats:')
    for k,v in sorted(stats.items(),key=lambda t:str(t)):
        print('   ',k,v)
        for e in ex[k][:2]: print('        ',e)
if __name__=='__main__':
    a=sys.argv[1:]
    main(int(a[0]) if a else 6, int(a[1]) if len(a)>1 else 2)
