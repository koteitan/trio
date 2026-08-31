import sys, collections
sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import core
from core import expand, show
from rows2 import split, colOK, descOK, units_split, contrPre
from resid_check import blockok, argPatOK, gen_blocks, adjLev, argCtrOK, ctrHead

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

def main(maxlen=7, bdmax=2, nmax=4, mode='ctr'):
    blocks = gen_blocks(maxlen,bdmax)
    cnt=0; tested=0; bad=[]
    for B in blocks:
        cnt+=1
        if cnt%4000==0: core._exp_memo.clear(); core._flat_memo.clear()
        bd=B[0][0]
        if not (blockok(bd,B) and colOK(B) and descOK(B)): continue
        p,r=B[0],B[1:]
        A,T=split(p,list(r))
        if mode in ('ctr','all') and not ctrHead(p,list(A),list(T)): continue
        if mode=='all' and not (argPatOK(B) and adjLev(B) and argCtrOK(B)): continue
        if contr(p,list(T),list(A)) is not None: continue
        tested+=1
        for n in range(1,nmax+1):
            Tn = list(expand(tuple(T),n)) if len(T)>1 else list(T)
            if contr(p,Tn,list(A)) is not None:
                bad.append((B,n,tuple(Tn),argPatOK(B),adjLev(B),argCtrOK(B)))
                break
    print('mode=%s maxlen=%d bdmax=%d: tested %d, BAD %d'%(mode,maxlen,bdmax,tested,len(bad)))
    for x in bad[:15]:
        print('   ',show(x[0]),'n=%d'%x[1],show(x[2]),'argPat=%s adjLev=%s argCtr=%s'%(x[3],x[4],x[5]))

main(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),sys.argv[4])
