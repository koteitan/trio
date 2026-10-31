"""Grafts aimed at AbsDN0 (WfInvA, 2026-10-31).
Seeds: frame matrices (t = 1, q = r last column) with AbsDN0 cases, from frames/*.pkl (sample), plus the 38-column N
(all prefixes) and the 37-column M37. Ops on a seed M (last column kept last):
 (i)  insert a child (e0 c + 1, a, b) under any column c, as first or last child, a in 0..e1 c + 3, b in {0,1}
      (larger sibling / child with larger row 1);
 (ii) one-column mutations (+-1 per entry, delete, duplicate);
 (iii) lift: row 1 of one column + 2 or + 3 (row-1 values b >= 4);
 (iv) replace the last column by (a, b, 0), b >= 1 (new t = 1 frames).
Keep: < SRO, last column (., >0, 0), bms-standard. Then M[2], M[3] of a sample, prefixes ending in a t = 1 column.
usage: nice -n 15 python3 graft_adn.py NPROC NSEEDS OUT.pkl"""
import os,sys,pickle,random,subprocess,itertools,glob,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA')
from multiprocessing import Pool
import trio
import probe_adn as P
BMS='/home/koteitan/proofs/trio/bms'
SRO=((0,0,0),(1,1,1),(2,1,1),(3,1,0),(2,0,0))
def ms(M):return ''.join('(%d,%d,%d)'%tuple(c) for c in M)
def std(M):return subprocess.run([BMS,'-s',ms(M)],capture_output=True,text=True).stdout.strip()=='1'
def frame_ok(N):return len(N)>=4 and tuple(N)<SRO and N[-1][1]>0 and N[-1][2]==0
def subend(M,c):
    e=c+1
    while e<len(M) and M[e][0]>M[c][0]:e+=1
    return e
def ops(M):
    L=len(M)
    for c in range(L-1):
        for a in range(0,M[c][1]+4):
            for b in (0,1):
                col=(M[c][0]+1,a,b)
                for pos in sorted({c+1,subend(M,c)}):
                    if pos<L:yield M[:pos]+[col]+M[pos:]
    for i in range(1,L):
        for d in itertools.product((-1,0,1),repeat=3):
            if d==(0,0,0):continue
            col=tuple(M[i][j]+d[j] for j in range(3))
            if min(col)<0 or col[2]>1:continue
            yield M[:i]+[col]+M[i+1:]
        for k in (2,3):yield M[:i]+[(M[i][0],M[i][1]+k,M[i][2])]+M[i+1:]
        if i<L-1:
            yield M[:i]+M[i+1:]
            yield M[:i]+[M[i]]+M[i:]
    for a in range(1,M[-1][0]+2):
        for b in range(1,5):yield M[:-1]+[(a,b,0)]
def gen(M):
    M=[tuple(c) for c in M];out=set()
    for N in ops(M):
        if frame_ok(N) and tuple(N)!=tuple(M) and std(N):out.add(tuple(N))
    return out
def ex(M):
    M=[tuple(c) for c in M];out=set()
    for n in (2,3):
        try:N=[tuple(c) for c in trio.expand([list(c) for c in M],n)]
        except Exception:continue
        for j in range(4,len(N)+1):
            Q=tuple(N[:j])
            if frame_ok(Q):out.add(Q)
    return out
def has_case(M):
    import collections
    cnt=collections.Counter();ex_={}
    try:P.measure([tuple(c) for c in M],cnt,ex_)
    except Exception:return False
    return cnt['AbsDN0.cases']>0
if __name__=='__main__':
    npr=int(sys.argv[1]);ns=int(sys.argv[2]);out=sys.argv[3]
    P.FR=[]
    cand=[]
    for f in sorted(glob.glob(os.environ.get('SEEDGLOB','/home/koteitan/proofs/trio/tmp/wf/WfInvA/frames/*.pkl'))):
        cand+= [tuple(tuple(c) for c in M) for M in pickle.load(open(f,'rb'))]
    cand=sorted(set(cand));random.seed(17);random.shuffle(cand)
    with Pool(npr) as pool:
        P.FR=[]
        flags=pool.map(has_case,cand[:min(len(cand),20*ns)],chunksize=50)
        seeds=[M for M,f in zip(cand,flags) if f][:ns]
        s38=open('/home/koteitan/proofs/trio/tmp/wf/WfReM/adn38.txt').read()
        N38=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s38)]
        M37=pickle.load(open('/home/koteitan/proofs/trio/tmp/wf/WfInvA/m37.pkl','rb'))[0]
        extra=[tuple(N38[:j]) for j in range(6,len(N38)+1) if frame_ok(N38[:j])]+[tuple(M37)]
        seeds=seeds+extra
        print('candidates',len(cand),'seeds',len(seeds),flush=True)
        g1=set()
        for o in pool.imap_unordered(gen,seeds,chunksize=2):g1|=o
        print('gen1',len(g1),flush=True)
        g1l=sorted(g1);random.seed(19);sx=random.sample(g1l,min(len(g1l),3000))+extra
        gx=set()
        for o in pool.imap_unordered(ex,sx,chunksize=10):gx|=o
        gx-=g1
        print('expansion prefixes',len(gx),flush=True)
    pickle.dump([list(N) for N in sorted(g1|gx)],open(out,'wb'))
