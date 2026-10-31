"""Grafts around the AbsDS/TPLoS witnesses (t = 1, q != r).  Ops from WfInvA/graft_adn.py (inserted children /
larger siblings, row-1 values +2/+3 (b >= 4), +-1 mutations, delete/duplicate, new last column), then M[2], M[3]
prefixes.  Keep: standard, < SRO, t = 1 q != r last column.  Measure analyze.fields and analyze.primary (n = 2, 3).
usage: nice -n 15 python3 graft.py SEEDS.pkl OUT.pkl LOG.json NPROC"""
import sys,pickle,json,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQnE');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA')
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import graft_adn as G
import analyze as A
from multiprocessing import Pool
def isqn(M):
    try: return A.frame(list(M)) is not None
    except Exception: return False
def grow(M):
    out=set()
    try:
        for N in G.gen(M):
            if isqn(N): out.add(N)
        for N in G.ex(M):
            if isqn(N) and G.std(list(N)): out.add(N)
    except Exception as e: pass
    return out
def meas(M):
    c=collections.Counter();e={}
    try:
        c1,e1=A.fields(list(M));c.update(c1);e.update(e1)
        c2,e2=A.primary(list(M),(2,3));c.update(c2);e.update(e2)
    except Exception as ex:
        c['exception']+=1;e['exc']=(M,repr(ex))
    return c,e
if __name__=='__main__':
    seeds,out,log,npr=sys.argv[1],sys.argv[2],sys.argv[3],int(sys.argv[4])
    S=[tuple(tuple(c) for c in M) for M in pickle.load(open(seeds,'rb'))]
    with Pool(npr) as pool:
        allg=set()
        for g in pool.imap_unordered(grow,S,chunksize=1): allg|=g
        allg-=set(S)
        allg=sorted(allg,key=lambda N:(len(N),N))
        pickle.dump(allg,open(out,'wb'))
        print('grafts',len(allg),flush=True)
        tot=collections.Counter();ex={}
        for c,e in pool.imap_unordered(meas,allg,chunksize=20):
            tot.update(c)
            for k,v in e.items(): ex.setdefault(k,v)
    res={'n':len(allg),'cnt':dict(sorted(tot.items())),'ex':{k:G.ms(v[0])+' '+str(v[1:]) for k,v in ex.items()}}
    json.dump(res,open(log,'w'),indent=1)
    print(json.dumps(res['cnt']))
