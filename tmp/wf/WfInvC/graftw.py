"""Grafting attack on the weaker qn path clause (S.OS: comps u S < B + Omega_S, and t1.lt).
Seeds: qn sources of the given pkls whose old clause S.lt fails (up to NSEED, smallest first), plus the two witnesses.
Mutations (keep bms -s = 1, < SRO, last column with row 2 > 0):
 (a) child (e0 c + 1, a, b) of any column c as first or last child, a in 0..e1 c + 3 (larger row 1);
 (b) a larger sibling: copy of column i with row 1 + d (d = 1..2) inserted right before i (i < x);
 (c) lift: row 1 + d (d = 1..4) on column i and its row-0 subtree (excluding x), giving row-1 values >= 4;
 (d) duplicate a column / subtree before x-1.
Gen 2 on a sample of gen-1 qn sources.  Output graftw1.pkl, graftw2.pkl."""
import sys,os,pickle,random,subprocess,itertools,collections
sys.path[:0]=['/home/koteitan/proofs/trio/tmp/wf/WfInvC']
from multiprocessing import Pool
import qnpw
BMS='/home/koteitan/proofs/trio/bms'
SRO=((0,0,0),(1,1,1),(2,1,1),(3,1,0),(2,0,0))
def ms(M):return ''.join('(%d,%d,%d)'%tuple(c) for c in M)
def std(M):return subprocess.run([BMS,'-s',ms(M)],capture_output=True,text=True).stdout.strip()=='1'
def subend(M,c):
    e=c+1
    while e<len(M) and M[e][0]>M[c][0]:e+=1
    return e
def muts(M):
    x=len(M)-1
    for c in range(x):
        for a in range(0,M[c][1]+4):
            for b in (0,1):
                col=(M[c][0]+1,a,b)
                for pos in sorted({c+1,subend(M,c)}):
                    if pos<=x: yield M[:pos]+[col]+M[pos:]
    for i in range(1,x):
        for d in (1,2):
            yield M[:i]+[(M[i][0],M[i][1]+d,M[i][2])]+M[i:]
        for d in (1,2,3,4):
            e=min(subend(M,i),x)
            yield M[:i]+[(c0,c1+d,c2) for (c0,c1,c2) in M[i:e]]+M[e:]
        e=min(subend(M,i),x)
        yield M[:e]+M[i:e]+M[e:]
def keep(N):
    N=[tuple(c) for c in N]
    return len(N)>=4 and N[-1][2]>0 and tuple(N)<SRO and qnpw.pre(N) and std(N)
def gen(M):
    M=[tuple(c) for c in M];out=set()
    for N in muts(M):
        if keep(N): out.add(tuple(N))
    return list(out)
def isfail(M):
    c,e=qnpw.go(M); return c.get('S.lt.fail',0)>0, c.get('qn.sources',0)>0
if __name__=='__main__':
    W='/home/koteitan/proofs/trio/tmp/wf/'
    NSEED=int(os.environ.get('NSEED','60'))
    srcs=[W+'WfReM/graftM36.pkl',W+'WfB2S/graft4.pkl',W+'WfH7W2/graft2.pkl',W+'WfB2L/lift1.pkl',W+'WfReM/graftM36x.pkl']
    seeds=set(map(tuple,pickle.load(open(W+'WfInvC/wit.pkl','rb'))))
    with Pool(3) as p:
        for f in srcs:
            mats=[M for M in map(qnpw.norm,pickle.load(open(f,'rb'))) if qnpw.pre(M)]
            fl=[tuple(M) for M,(a,b) in zip(mats,p.map(isfail,mats,chunksize=32)) if a]
            fl.sort(key=len); seeds.update(fl[:NSEED]); print(f,len(fl),flush=True)
        seeds=sorted(seeds,key=len);print('seeds',len(seeds),flush=True)
        g1=set()
        for o in p.imap_unordered(gen,seeds,chunksize=1): g1.update(o)
        g1-=set(seeds);g1=sorted(g1);pickle.dump(g1,open('graftw1.pkl','wb'));print('gen1',len(g1),flush=True)
        st=p.map(isfail,g1,chunksize=32)
        qn=[M for M,(a,b) in zip(g1,st) if b];fl=[M for M,(a,b) in zip(g1,st) if a]
        print('gen1 qn',len(qn),'oldfail',len(fl),flush=True)
        random.seed(7);s2=fl[:300]+random.sample(qn,min(300,len(qn)))
        g2=set()
        for o in p.imap_unordered(gen,s2,chunksize=1): g2.update(o)
        g2-=set(g1);g2=sorted(g2);pickle.dump(g2,open('graftw2.pkl','wb'));print('gen2',len(g2),flush=True)
