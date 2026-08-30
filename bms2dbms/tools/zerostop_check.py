import sys, collections
sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import core
from core import expand, show, pim
from rows2 import split, colOK, descOK, units_split, contrPre, convC
from resid_check import blockok, argPatOK, gen_blocks, adjLev, argCtrOK, hpOK, fOK, ladOf, check

def contr(p, L, A):
    U, B2 = units_split(p, list(L))
    if not B2: return None
    q, r2 = B2[0], B2[1:]
    Aq, Bq = split(q, list(r2))
    if q[1]+1 != p[1] or q[0] != p[0]: return None
    pre = contrPre(p, U, list(A))
    if list(Aq[:len(pre)]) != pre: return None
    rest2 = list(Aq[len(pre):])
    if not rest2: return None
    if not (rest2[0][0]==p[0]+1 and rest2[0][1] < p[1]): return None
    return (list(U), q, pre, rest2, list(Bq))

def par0(B):
    S=tuple(B); x=len(S)-1
    P=pim(S); r=P[x][0]
    return None if r==-1 else r

def main(maxlen=7, bdmax=2, plevmax=3):
    blocks = gen_blocks(maxlen,bdmax)
    acc=collections.Counter(); ex=collections.defaultdict(list); cnt=0; bad=[]
    for B in blocks:
        cnt+=1
        if cnt%4000==0: core._exp_memo.clear(); core._flat_memo.clear()
        bd=B[0][0]
        if not (blockok(bd,B) and colOK(B) and descOK(B) and argPatOK(B)
                and adjLev(B) and argCtrOK(B)): continue
        if B[-1][1]!=0: continue
        p,r=B[0],B[1:]
        A,T=split(p,list(r))
        if not T: continue
        c0=contr(p,list(T),list(A))
        if c0 is None: continue
        U,q,pre,rest2,Bq=c0
        if Bq: continue
        j=par0(B)
        if j is None: continue
        G2=len(B)-len(rest2)
        if j>=G2: continue
        key='U=%d rest2=%d A=%d'%(len(U),len(rest2),len(A))
        acc[key]+=1
        if len(ex[key])<3: ex[key].append(B)
        # 目標の恒等式を確かめる
        for d in range(bd,bd+3):
            for plev in range(0,plevmax+1):
                for first in (False,True):
                    for force in (False,True):
                        if not hpOK(B,d,plev,first,force): continue
                        if not fOK(B,d,plev,force): continue
                        if not ladOf(p[1],d,plev,first,force): continue
                        res=check(B,d,plev,first,force)
                        if res is not None: bad.append((B,d,plev,first,force,res))
    for k,v in sorted(acc.items()):
        print(k,v,[show(x) for x in ex[k][:2]])
    print('BAD',len(bad))
    for x in bad[:6]: print('   ',show(x[0]),x[1:])

main(*[int(x) for x in sys.argv[1:]])
