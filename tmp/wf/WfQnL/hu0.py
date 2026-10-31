"""hu0 (WfQnL8): t = 1, q != r frames: upg P r = some g -> g <= r, P = M[n-1] (n = 2..4).
Also hndN (WfQnL5) directly on N = M[n]: copy columns i >= x with par N 1 i = g < x or upg N i = g < x:
g must not be a v-call of D (checked via the structural DepX closure)."""
import sys, pickle
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import trio, ytosk_eval as Y
from collections import Counter

def depx(E, x):
    """structural DepX M x (set of (b,i)), fixpoint over the six rules."""
    M=E.M; n=E.n
    D={(True,x)}
    ch=E.children
    changed=True
    while changed:
        changed=False
        for i in range(n):
            # o calls
            if (True,i) not in D:
                if (False,i) in D or any((True,c) in D and M[c]!=E.bump(i) and not (c in E.upgs and E.topped(c)) for c in ch[i]):
                    D.add((True,i)); changed=True
            if (False,i) not in D and E.e(1,i)!=0:
                m=E.par(1,i); ok=False
                if m is not None and (False,m) in D: ok=True
                if E.e(2,i)==0 and E._upg[i] is not None and (False,E._upg[i]) in D: ok=True
                if E.e(2,i)!=0:
                    for j in ch[i]:
                        if M[j]==E.bump(i) and any((True,k) in D for k in ch[j]): ok=True
                if ok: D.add((False,i)); changed=True
    return D

def run(path, cnt, cap=None):
    data=pickle.load(open(path,'rb'))
    if isinstance(data,dict): data=list(data.values()) if not 'mats' in data else data['mats']
    for idx,M in enumerate(data):
        if cap and idx>=cap: break
        M=[tuple(c) for c in M]
        x=len(M)-1
        if x<1 or M[x][2]!=0: continue
        E=Y.Ev(M); r=E.par(1,x)
        if r is None or E.par(0,x)==r: continue
        cnt['frames']+=1
        D=None
        for n in (2,3,4):
            try:
                P=[tuple(c) for c in trio.expand([list(c) for c in M],n-1)]
                N=[tuple(c) for c in trio.expand([list(c) for c in M],n)]
            except Exception as ex:
                cnt['expand_err']+=1; continue
            EP=Y.Ev(P); g=EP._upg[r] if r<len(P) else None
            if g is not None:
                cnt['hu0_ante']+=1
                if g>r: cnt['hu0_FAIL']+=1; print('hu0 FAIL',path,idx,n,M,g)
            EN=Y.Ev(N)
            if D is None: D=depx(E,x)
            for i in range(x,len(N)):
                if EN.e(1,i)==0: continue
                for g in (EN.par(1,i), EN._upg[i]):
                    if g is not None and g<x:
                        cnt['hndN_ante']+=1
                        if (False,g) in D: cnt['hndN_FAIL']+=1; print('hndN FAIL',path,idx,n,M,i,g)

if __name__=='__main__':
    cnt=Counter()
    for p in sys.argv[1:]:
        run(p,cnt)
        print(p, dict(cnt), flush=True)
