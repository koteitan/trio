import sys, collections
sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import core
from core import expand, show, pim
from rows2 import split, colOK, descOK, units_split, contrPre
from resid_check import blockok, argPatOK, gen_blocks, adjLev, argCtrOK

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

def par(B, row):
    S=tuple(B); x=len(S)-1
    P=pim(S); r=P[x][row]
    return None if r==-1 else r

def main(maxlen=8, bdmax=2):
    blocks = gen_blocks(maxlen,bdmax)
    acc=collections.Counter(); ex=collections.defaultdict(list); cnt=0
    for B in blocks:
        cnt+=1
        if cnt%8000==0: core._exp_memo.clear(); core._flat_memo.clear()
        bd=B[0][0]
        if not (blockok(bd,B) and colOK(B) and descOK(B) and argPatOK(B)
                and adjLev(B) and argCtrOK(B)): continue
        p,r=B[0],B[1:]
        A,T=split(p,list(r))
        if not T: continue
        c0=contr(p,list(T),list(A))
        if c0 is None: continue
        U,q,pre,rest2,Bq=c0
        lev=B[-1][1]
        row = 1 if lev>0 else 0
        j=par(B,row)
        if j is None: acc['nopar lev%s'%('pos' if lev>0 else '0')]+=1; continue
        if Bq:
            G=len(B)-len(Bq); tgt='Bq'
        else:
            G=len(B)-len(rest2); tgt='rest2'
        key='lev%s %s parGE=%s'%('pos' if lev>0 else '0', tgt, j>=G)
        acc[key]+=1
        if len(ex[key])<4: ex[key].append((B,c0,j,G))
    for k,v in sorted(acc.items()):
        print(k,v)
        if 'parGE=False' in k:
            for B,c0,j,G in ex[k][:4]:
                print('     ',show(B),'j=%d G=%d'%(j,G),c0)

main(*[int(x) for x in sys.argv[1:]])
