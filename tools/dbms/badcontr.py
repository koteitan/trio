"""dropLast の帰納で唯一壊れる場合を探す。

`convC` の縮約枝で `Bq = []` かつ `|rest2| = 1` のとき、末尾列を落とすと
`rest2` が空になって縮約が消え、像がかえって長くなる（`conC (A.dropLast)` が
`conC A` の接頭辞ですらなくなる）。それ以外の縮約は `Bq` または `rest2` を
1 列縮めるだけで生き残る（`lean/DbmsStd.lean` の `convC_dropLast_contr` /
`convC_dropLast_contr2`）。

実測（BMS 標準形、`convC` の再帰の右端の道）:

```
lim 9  ('BAD', 段0=True, 親='中'): 49    ← 壊れる場合はすべて段 0 で親が「中」
       ('ok', ...)                        それ以外の縮約
```

**壊れる場合は必ず段 0 で、親が「中」にある。** だから場合 (b)（親なし）と
場合 (d)（親が節点）では起きない。段 0 なら `q`（深さ `p.1`）が行 0 の親になるので、
親は必ず存在し、しかも `q` は節点より後ろなので「中」。

使い方: python3 badcontr.py [列数上限]
"""
import sys, collections
sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import core
from core import show, pim
from rows2 import gen, convC, split, units_split, contrPre
def par(S):
    X=len(S)
    if X<=1: return 'SHORT'
    x=X-1
    if S[x]==(0,0): return 'ZERO'
    t = 1 if S[x][1]>0 else 0
    P=pim(tuple(S)); r=P[x][t]
    return None if r==-1 else r
def info(p,A,B,s,lad):
    """縮約が発火するなら (rest2, Bq) を返す。"""
    if not lad: return None
    U,B2 = units_split(p,B)
    if not B2: return None
    q,r2 = B2[0],B2[1:]
    Aq,Bq = split(q,r2)
    if q[1]+1!=s or q[0]!=p[0]: return None
    pre = contrPre(p,U,A)
    if list(Aq[:len(pre)])!=pre: return None
    rest2 = list(Aq[len(pre):])
    if rest2 and rest2[0][0]==p[0]+1 and rest2[0][1]<s:
        return (rest2, list(Bq))
    return None
def walk(M,d,plev,first,force,acc,ex):
    if len(M)<=1: return
    p,r = M[0],M[1:]
    s=p[1]; A,B = split(p,r)
    lad = first and s==plev+1 and (d<=s or force)
    ci = info(p,A,B,s,lad)
    jB = par(list(M))
    cls = 'ZERO' if jB=='ZERO' else ('親なし' if jB is None else ('節点' if jB==0 else '中'))
    if ci is not None:
        rest2, Bq = ci
        bad = (not Bq) and len(rest2)==1
        if bad:
            acc[('BAD', M[-1][1]==0, cls)]+=1
            if len(ex)<5: ex.append((tuple(M),d,plev,first,force,rest2,cls))
        else:
            acc[('ok', bool(Bq), len(rest2))]+=1
        return
    dd = d+1 if lad else (s+1 if (s>0 and d<=s) else d)
    if B: walk(list(B),d,s,False,False,acc,ex)
    elif A: walk(list(A),dd+1,s,True,(not lad) and first and s==plev,acc,ex)
def main(lim=8):
    Ms=gen('BMS',lim); acc=collections.Counter(); ex=[]
    for i,M in enumerate(Ms):
        if i%20000==0: core._exp_memo.clear(); core._flat_memo.clear()
        walk(list(M),0,0,True,False,acc,ex)
    print("lim=%d %s" % (lim, dict(sorted(acc.items(), key=lambda x: str(x)))))
    for M,d,plev,f,g,rest2,cls in ex:
        print("   BAD:",show(M),(d,plev,f,g),"rest2=",show(tuple(rest2)),"親=",cls)


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 8)
