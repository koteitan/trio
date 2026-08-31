import sys, collections
sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import core
from core import expand, show
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
    return (len(U), pre, rest2)

def main(maxlen=7, bdmax=2, nmax=4):
    blocks = gen_blocks(maxlen,bdmax)
    cnt=0; acc=collections.Counter(); ex=collections.defaultdict(list)
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
            tag = '1(inside)' if last_idx < W else ('2a(=|W|)' if last_idx==W else '2b(beyond)')
            acc[tag]+=1
            if len(ex[tag])<5: ex[tag].append((B,n,tuple(Tn),last_idx,W))
            break
    print('counts:',dict(acc))
    for k,v in ex.items():
        for B,n,Tn,li,W in v[:5]:
            print('  %s %s n=%d Tn=%s last_idx=%d |W|=%d'%(k,show(B),n,show(Tn),li,W))

main(*[int(x) for x in sys.argv[1:]])
