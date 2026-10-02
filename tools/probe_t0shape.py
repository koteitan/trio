"""T0Shape（V3ExpT0）を Lean の文の通りに測る。
旧 (i): i < r、CL M i = Lc ++ [c]、c < r、c ∈ D_o（o が変わる）、ρ.o c = ψ_s(y)、σ.o c = ψ_s(y′)（同じ s）、y′ ≠ y
   → ClsABC B s y′ y (Trig a B s y)、B = spArg a 0 (sum Lc)。
新 (i): 同じ枠で y′・y の低い部分がどちらも 0 で古い枠が書き換えるなら B < y′。
新 (ii): 同じ枠で c の v が変わるとき、ψ_{v(c)}(0) ≥ Ω_{a+1} なら ψ_{v′(c)}(0) ≥ Ω_{a+1}。
新 (iii): g = P_0(r) で r が数えられるとき、g の引数の組の型（A・B0・C、ClsNode）。
(iv): g で中間の写しの根がどれも数えられない → 引数で ◁ かつ標準形。"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_t0inv import *
def clsABC(B,s,yN,yM,trigM):
    th=(succ(s),Z,Z)
    hN,lN=split(yN,th); hM,lM=split(yM,th)
    A = (hN==hM and lN!=Z)
    Bc = (lN==Z and lM==Z and ((not trigM) or lt(B,yN)))
    Cc = (yN==hM)
    return A or Bc or Cc, ('A' if A else 'B' if Bc else 'C' if Cc else 'X')
def chk(M):
    M=list(M); cnt=Counter(); ex={}
    def note(f, ok, info):
        cnt[(f,'cases')]+=1
        if not ok:
            cnt[(f,'FAIL')]+=1
            if len(ex.setdefault(f,[]))<3: ex[f].append((M,info))
    x=len(M)-1
    if x<1 or M[x][1]!=0 or M[x]==(0,0,0): return cnt,ex
    C=Ctx(M)
    if not C.ok: return cnt,ex
    r=C.e.par(0,x); g=C.e.par(0,r); L=x-r
    for n in (2,3,4):
        N=trio.expand(M,n); CN=Ctx(N)
        if not CN.ok: cnt['noval']+=1; continue
        for i in range(r):
            cl=C.CL(i)
            if not cl: continue
            c=cl[-1]
            if c>=r: continue
            if CN.o(c)==C.o(c): continue
            sM,yM,_=C.o(c); sN,yN,_=CN.o(c)
            if CN.v(c)!=C.v(c):
                tha=(succ(C.v(i)),Z,Z)
                note('T0Shape(ii) vchg', lt((C.v(c),Z,Z),tha) or not lt((CN.v(c),Z,Z),tha), (n,i,c))
            if sN!=sM or yN==yM: continue
            a=C.v(i); B=C.pre(i,cl[:-1])
            trigM=lt(B,yM) and lt((a,Z,Z),(sM,yM,Z))
            ok,k=clsABC(B,sM,yN,yM,trigM)
            cnt[('cls',k)]+=1
            note('T0Shape old(i)', ok, (n,i,c))
            th=(succ(sM),Z,Z)
            if split(yN,th)[1]==Z and split(yM,th)[1]==Z and trigM:
                note('T0Shape(i) B0 rewrite', lt(B,yN), (n,i,c))
        if g is not None and r in C.CL(g):
            tg=(succ(C.v(g)),Z,Z); XN=CN.o(g)[1]; XM=C.o(g)[1]
            hN,lN=split(XN,tg); hM,lM=split(XM,tg)
            note('T0Shape(iii) cls g', (hN==hM and lN!=Z) or (lN==Z and lM==Z) or XN==hM, (n,))
            mids=[r+k*L for k in range(n-1)]
            if not any(q in CN.CL(g) for q in mids):
                XN=CN.o(g)[1]; XM=C.o(g)[1]
                note('T0Shape(iv)', CN.o(g)[0]==C.o(g)[0] and lt(XN,XM) and lhd(XN,XM) and isOT(XN), (n,))
    return cnt,ex
if __name__=='__main__':
    mats=pickle.load(open(CP,'rb'))
    k=int(sys.argv[1]); random.seed(int(sys.argv[2]))
    if k<len(mats): mats=random.sample(mats,k)
    tot=Counter(); exs={}
    with Pool(8) as p:
        for c,e in p.imap_unordered(chk,mats,chunksize=300):
            tot.update(c)
            for f,l in e.items():
                if len(exs.setdefault(f,[]))<3: exs[f]+=l
    for k_,v in sorted(tot.items(),key=str): print(k_,v)
    for f,l in exs.items():
        print(f)
        for m,info in l[:3]: print('  ',''.join('(%d,%d,%d)'%c for c in m),info)
