"""梯子の敷き直し (re-lay) がどの地点で必要かを総当たりでラベル付けする調査スクリプト。

各行について、敷き直しの候補地点すべての on/off の組合せを試し、
シートの真値と一致するマスクを求める。結果は relay_labels.json に保存。
"""
import sys, json
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_sheet import load
from core import isstd, show, pim
import rule as R
Y=3
def build(m, depth, firepred):
    P=pim(m); out=[]; img=[None]*len(m); sh={}; dep={}; sites=[]
    anchors=set(); realimg=[]
    def remap(f):
        for i in range(len(img)):
            if img[i] is not None: img[i]=f(img[i])
        for k in list(sh): sh[k]=f(sh[k])
        for i,z in enumerate(realimg): realimg[i]=f(z)
        a=set(f(z) for z in anchors); anchors.clear(); anchors.update(a)
    def absorb_tail():
        n=len(out)
        if n<2: return False
        j=n-1; Q=out[j]
        for i in range(j-1,-1,-1):
            Pc=out[i]
            if len(Pc)<2 or Pc[0]!=Q[0] or Q[1]<=Pc[1]: continue
            L=j-i-1
            if L<=0 or i-L<0: continue
            if out[i-L:i]==out[i+1:j]:
                del out[i:j]
                def g(z,i=i,j=j,L=L):
                    if z<i: return z
                    if z<j: return z-(L+1) if z>i else i-L
                    return z-(j-i)
                remap(g); return True
        return False
    def shadow(p,y):
        if y<=0: return img[p]
        k=(p,y)
        if k in sh: return sh[k]
        s=shadow(p,y-1)
        if out[s][y-1]>=1: r=s
        else:
            out.append(tuple(out[s][z]+1 if z<y else 0 for z in range(Y))); r=len(out)-1
        sh[k]=r; return r
    for x,c in enumerate(m):
        nz=[y for y in range(Y) if c[y]>0]
        if not nz:
            out.append(tuple([0]*Y)); img[x]=len(out)-1; realimg.append(len(out)-1)
        else:
            t=nz[-1]; d=depth(x,c); dep[x]=d; lvl=min(Y-1,t+d)
            p1=P[x][1] if t>=1 else -1
            cand = t>=1 and p1>0 and (p1,lvl) not in sh and dep.get(p1)==1 and img[p1] is not None and out[img[p1]][1]>=1
            done=False
            if cand:
                k=len(sites); sites.append(x)
                if firepred(k,x):
                    s=img[p1]; L=out[s][1]
                    tgt=[oi for oi in realimg if oi<s and oi not in anchors and out[oi][1]==L]
                    if tgt:
                        j=tgt[0]; chain=[]; kk=j
                        while kk>0:
                            pk=max([q for q in range(kk) if out[q][0]<out[kk][0]], default=None)
                            if pk is None: break
                            if out[pk][1]<out[j][1] and all(out[q][0]>out[pk][0] for q in range(pk+1,len(out))): break
                            chain.append(pk); kk=pk
                        for q in reversed(chain): out.append(out[q])
                        out.append(out[j]); base=len(out)-1
                        sh[(p1,lvl)]=base
                        out.append(tuple(out[base][y]+1 if y<=t else 0 for y in range(Y)))
                        img[x]=len(out)-1; realimg.append(len(out)-1); done=True
            if not done:
                base=shadow(P[x][t],lvl) if P[x][t]!=-1 else None
                T=[0]*Y
                for y in range(1,t+1):
                    p=P[x][y]; T[y]=out[shadow(p,y)][y]+1 if p!=-1 else 0
                p0=P[x][0]; T[0]=out[img[p0]][0]+1 if p0!=-1 else 0
                if base is not None:
                    for y in range(0,t+1): T[y]=max(T[y], out[base][y]+1)
                out.append(tuple(T)); img[x]=len(out)-1; realimg.append(len(out)-1)
            if c[0]==c[1] and c[0]>=1: anchors.add(img[x])
        while absorb_tail(): pass
    return tuple(out), sites
def conv(m, mask):
    prev=[None]
    def dp(x,c):
        if R.is_anchor1(c): prev[0]=0
        if not R.is_branching(c): return 0
        v=R.depth_rule(c, m[x+1] if x+1<len(m) else None, prev[0],
                       m[x-1] if x>0 else None, R.hi_block(m,x),
                       m[x-2] if x>1 else None, R.is_repeat(m,x),
                       R.spent_level(m,x,c[1]+1)); prev[0]=v
        return v
    o,s=build(m,dp,lambda k,x: bool(mask>>k & 1))
    return R.dedup(o), s
d=[x for x in load() if x[3]==3]
res=[]
for r,mb,md,_ in d:
    _,sites=conv(mb,0)
    n=len(sites)
    if n==0: continue
    if n>6: n=6
    good=[msk for msk in range(1<<n) if conv(mb,msk)[0]==md]
    res.append((r['row'], mb, md, sites[:n], good))
solvable=[x for x in res if x[4]]
print('候補地のある行:', len(res), '  どれかのマスクで正解:', len(solvable))
uniq=[x for x in solvable if len(x[4])==1]
print('マスクが一意:', len(uniq))
import collections
cnt=collections.Counter()
for rw,mb,md,sites,good in solvable:
    msk=min(good,key=lambda z:bin(z).count('1'))
    for k,x in enumerate(sites): cnt[(msk>>k)&1]+=1
print('最小マスクでの発火/非発火:', dict(cnt))
json.dump([[rw,[list(c) for c in mb],sites,good] for rw,mb,md,sites,good in res], open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'relay_labels.json'),'w'))
