import sys, collections, pickle
sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import core
from core import expand, show, pim
from rows2 import gen, convC, split, units_split, contrPre

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

def par(B):
    S=tuple(B); x=len(S)-1
    if all(v==0 for v in S[x]): return 'zero'
    t=max(y for y in range(2) if S[x][y]>0)
    P=pim(S); r=P[x][t]
    return None if r==-1 else (r,t)

def walk(M, d, plev, first, force, out):
    if not M: return
    p, r = M[0], M[1:]
    s = p[1]
    A, T = split(p, r)
    out.append((tuple(M), d, plev, first, force))
    lad = first and s == plev+1 and (d <= s or force)
    dd = d+1 if lad else (s+1 if (s>0 and d<=s) else d)
    if T: walk(list(T), d, s, False, False, out)
    elif A: walk(list(A), dd+1, s, True, (not lad) and first and s==plev, out)

def main(lim=9):
    Ms = gen('BMS', lim)
    nodes=set()
    for i,M in enumerate(Ms):
        if i%20000==0: core._exp_memo.clear(); core._flat_memo.clear()
        acc=[]; walk(list(M),0,0,True,False,acc); nodes.update(acc)
    print('std <=%d: %d nodes %d'%(lim,len(Ms),len(nodes)))
    acc=collections.Counter(); ex=collections.defaultdict(list)
    for B,d,plev,first,force in sorted(nodes):
        if len(B)<2: continue
        p=B[0]; A,T=split(p,list(B[1:]))
        if not T: continue
        lad = first and p[1]==plev+1 and (d<=p[1] or force)
        if not lad: continue
        lastlev = B[-1][1]
        c0 = contr(p,list(T),list(A))
        pr = par(B)
        tag = 'lev0' if lastlev==0 else 'levpos'
        if c0 is None:
            cn = [contr(p,list(expand(tuple(T),n)),list(A)) for n in (1,2,3)] if len(T)>1 else []
            acc[tag+' nofire'+(' Y!!' if any(x is not None for x in cn) else '')]+=1
            continue
        U,q,pre,rest2,Bq = c0
        LB=len(B)
        G = LB-len(Bq) if Bq else LB-len(rest2)
        tgt = 'Bq' if Bq else 'rest2'
        if pr is None: key=tag+' fire nopar'
        elif pr=='zero': key=tag+' fire zerocol'
        else: key='%s fire %s parGE=%s'%(tag,tgt,pr[0]>=G)
        acc[key]+=1
        if len(ex[key])<6: ex[key].append((B,d,plev,first,force,c0,pr,G))
    for k,v in sorted(acc.items()):
        print(k,v)
        if 'fire' in k:
            for B,d,plev,first,force,c0,pr,G in ex[k][:6]:
                print('     ',show(B),'d=%d plev=%d f=%s F=%s'%(d,plev,first,force),'par=%s G=%d'%(pr,G),c0)

main(int(sys.argv[1]) if len(sys.argv)>1 else 9)
