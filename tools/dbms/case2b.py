import sys, collections
sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import core
from core import expand, show, pim
from rows2 import split, colOK, descOK, units_split, contrPre
from resid_check import blockok, gen_blocks, argPatOK, adjLev, argCtrOK

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
    return (len(U), pre, rest2)

def main(maxlen=7, bdmax=2, nmax=4):
    blocks = gen_blocks(maxlen,bdmax)
    cnt=0; acc=collections.Counter(); rows=[]
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
            k,pre,rest2 = w
            last_idx = k+1+len(pre)
            W = len(T)-1
            tag = '1' if last_idx < W else ('2a' if last_idx==W else '2b')
            acc[(tag, 'fires' if rest2[0][1] < p[1] else 'safe')]+=1
            if tag=='2b':
                rows.append((B,n,tuple(T),tuple(Tn),k,tuple(pre),tuple(rest2),last_idx,W,p,tuple(A)))
            break
    print('counts:',dict(acc))
    seen=set()
    for (B,n,T,Tn,k,pre,rest2,li,W,p,A) in rows:
        print('B=%-28s p=%s A=%s n=%d' % (show(B),p,show(A),n))
        print('   T   =%-28s |W|=%d' % (show(T),W))
        print('   Tn  =%-28s k=%d |pre|=%d J=%d' % (show(Tn),k,len(pre),li))
        print('   pre =%-20s rest2=%-20s rest2[0].2=%d p.2=%d  argPatOK(B)=%s argCtrOK(B)=%s'
              % (show(pre),show(rest2),rest2[0][1],p[1],argPatOK(list(B)),argCtrOK(list(B))))

main(*[int(x) for x in sys.argv[1:]])
