import sys, collections
sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import core
from core import expand, show, pim
from rows2 import split, colOK, descOK, units_split, contrPre
from resid_check import blockok, gen_blocks

def contrS(p, L, A):
    U, B2 = units_split(p, list(L))
    if not B2: return None
    q, r2 = B2[0], B2[1:]
    Aq, Bq = split(q, list(r2))
    if q[1]+1 != p[1] or q[0] != p[0]: return None
    pre = contrPre(p, U, list(A))
    if list(Aq[:len(pre)]) != pre: return None
    rest2 = list(Aq[len(pre):])
    if not rest2: return None
    if rest2[0][0] != p[0]+1: return None
    return (list(U), pre, rest2)

def badpart(T):
    """(j0, j1, d0) for the expansion of T, or None."""
    S=tuple(T); j1=len(S)-1
    if j1==0: return None
    if S[j1][0]==0 and S[j1][1]==0: return None
    P=pim(S)
    i1 = 1 if S[j1][1]>0 else 0
    j0 = P[j1][i1]
    if j0==-1: return None
    d0 = (S[j1][0]-S[j0][0]) if i1>0 else 0
    return (j0,j1,d0)

def main(maxlen=7, bdmax=2, nmax=4):
    blocks = gen_blocks(maxlen,bdmax)
    cnt=0; acc=collections.Counter()
    for B in blocks:
        cnt+=1
        if cnt%4000==0: core._exp_memo.clear(); core._flat_memo.clear()
        bd=B[0][0]
        if not (blockok(bd,B) and colOK(B) and descOK(B)): continue
        p,r=B[0],B[1:]
        A,T=split(p,list(r))
        if contrS(p,list(T),list(A)) is not None: continue
        for n in range(1,nmax+1):
            Tn = list(expand(tuple(T),n)) if len(T)>1 else list(T)
            w = contrS(p,Tn,list(A))
            if w is None: continue
            U,pre,rest2 = w
            k=len(U); J = k+1+len(pre); W=len(T)-1
            if J <= W: break
            bp = badpart(list(T))
            j0,j1,d0 = bp if bp else (-1,-1,-1)
            z = rest2[0]
            key = ('L=%d'%(j1-j0), 'd0=%d'%d0, 'A=[]' if not A else 'A!=[]',
                   'z==S[J-1]:%s'%(z==Tn[J-1]), 'Ulast==p:%s'%(U[-1]==p if U else 'U=[]'),
                   'z.2==p.2:%s'%(z[1]==p[1]))
            acc[key]+=1
            break
    for k,v in sorted(acc.items()):
        print(v, k)

main(*[int(x) for x in sys.argv[1:]])
