"""Scan standard matrices (no frame) for bump grandchildren c of i (e1,e2(i)!=0,
P0 i=P1 i=m) with e1 c<=e1 m whose next column c+1 leaves m's subtree, and
c anc-of-later shapes. Purely structural. nice15."""
import sys,json,pickle,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from pathlib import Path
from multiprocessing import Pool
from t2src_a_trio_codex import *
def anc0(E,a,d):
    while d is not None:
        if d==a:return True
        d=E.par(0,d)
    return False
def run(batch):
    cnt=collections.Counter();ex={}
    for mm in batch:
        M=list(map(tuple,mm));n=len(M)
        E=Y.Ev(M)
        for i in range(n):
            if M[i][1]==0 or M[i][2]==0:continue
            m=E.par(0,i)
            if m is None or E.par(1,i)!=m:continue
            for j in E.children[i]:
                if M[j]!=E.bump(i):continue
                for c in E.children[j]:
                    if M[c][1]>M[m][1]:continue
                    cnt['low_gc']+=1
                    if c+1>=n:continue
                    inm=anc0(E,m,c+1)
                    key=('eq' if M[c][1]==M[m][1] else 'lt')+'.next_in_m.'+str(inm)+'.leaf.'+str(not E.children[c])
                    cnt[key]+=1
                    if not inm:
                        cnt[key+'.upgnext.'+str(E._upg[c]==c+1)]+=1
                        t=key+".upgnext."+str(E._upg[c]==c+1)
                        if t not in ex or n<len(ex[t]['matrix']):ex[t]=dict(matrix=M,text=mattext(M),i=i,j=j,c=c,m=m)
    return dict(cnt),ex
if __name__=='__main__':
    out=Path(sys.argv[1]);report={}
    with Pool(4) as pool:
        for src in sys.argv[2:]:
            p=Path(src)
            if not p.exists():p=SETD/(src+'.pkl')
            mats=pickle.load(p.open('rb'))
            if isinstance(mats,dict):mats=mats.get('seeds',[])+mats.get('ext',[])
            cnt=collections.Counter();ex={}
            for cc,ee in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200))):
                cnt.update(cc)
                for t,e in ee.items():
                    if t not in ex or len(e['matrix'])<len(ex[t]['matrix']):ex[t]=e
            report[src]=dict(n=len(mats),counts=dict(cnt),examples=ex)
            out.write_text(json.dumps(report,indent=1)+'\n')
            print(json.dumps(dict(set=src,counts=dict(sorted(cnt.items())))),flush=True)
