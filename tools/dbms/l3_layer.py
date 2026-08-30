# (L-LAYER): 状態 A ++ 層 ++ 塔 で、親が「層の中」に落ちたとき何が減るか。
# 実際の展開 expand() を 2 段回して、生じた状態だけを見る（作り物の状態は使わない）。
import sys, itertools
sys.path.insert(0,'tools')
from trio import parent, expand
def srow(S,j):
    c=S[j]; return 2 if c[2]>0 else (1 if c[1]>0 else 0)
def gen_Q(maxlen,maxv):
    for L in range(2,maxlen+1):
        for cols in itertools.product([(a,b,c) for a in range(maxv+1) for b in range(a+1) for c in range(min(b,1)+1)],repeat=L):
            Q=list(cols); r0=Q[0][0]
            if any(q[0]<r0 for q in Q): continue
            yield Q
AS=[[(0,0,0)],[(0,0,0),(1,1,0)],[(1,1,0),(0,0,0)],[(0,0,0),(1,1,1)],[(0,0,0),(1,0,0),(2,0,0)]]
cnt={k:0 for k in ('inA','layer','tower')}
lay={'lt_Q':0,'eq_Q':0,'gt_Q':0,'lt_V1':0,'eq_V1':0,'gt_V1':0}
ex=[]
for Q in gen_Q(3,3):
    m=len(Q)
    for A in AS:
        if not any(a[0] < Q[0][0] for a in A): continue
        for n in (2,3):
            T0=A+Q*n
            for L1 in range(len(A)+1, len(T0)+1):          # snoc 鎖の各接頭辞
                P=T0[:L1]; t1=len(P)-1; c1=parent(P,srow(P,t1),t1)
                if c1 is None or c1 < len(A): continue      # 良い枝だけ（層ができる）
                V1=P[c1+1:t1]
                if not V1: continue
                for mm in (1,2):
                    S1=expand(P,mm)                         # = P[:c1] ++ 塔(V1)
                    if len(S1)<=c1: continue
                    for L2 in range(c1+1, len(S1)+1):
                        P2=S1[:L2]; t2=len(P2)-1
                        c2=parent(P2,srow(P2,t2),t2)
                        if c2 is None: continue
                        V2=P2[c2+1:t2]
                        if not V2: continue
                        if c2 < len(A): cnt['inA']+=1
                        elif c2 < c1:                       # ★ 親が「層の中」
                            cnt['layer']+=1
                            for k,a,b in (('Q',len(V2),m),('V1',len(V2),len(V1))):
                                lay[('lt_' if a<b else 'eq_' if a==b else 'gt_')+k]+=1
                            if len(V2)>=m and len(ex)<4:
                                ex.append((Q,A,n,L1,mm,L2,c1,c2,len(V1),len(V2)))
                        else: cnt['tower']+=1
print("親の位置:", cnt)
tot=cnt['layer']
print(f"★ 親が層の中 {tot} 件:")
for k in ('Q','V1'):
    print(f"   |V2| vs |{k}| :  < {lay['lt_'+k]} ({100*lay['lt_'+k]/max(1,tot):.4f}%)"
          f"   = {lay['eq_'+k]} ({100*lay['eq_'+k]/max(1,tot):.4f}%)"
          f"   > {lay['gt_'+k]} ({100*lay['gt_'+k]/max(1,tot):.4f}%)")
for e in ex: print("   ⛔ ex (Q,A,n,L1,m,L2,c1,c2,|V1|,|V2|) =",e)
