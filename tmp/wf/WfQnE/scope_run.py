"""Run analyze.scope (n = 2, 3) and analyze.fields over a pkl of matrices (only t = 1, q != r frames count).
usage: nice -n 15 python3 scope_run.py IN.pkl OUT.json NPROC [SAMPLE]"""
import sys,pickle,json,collections,random
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQnE')
import analyze as A
from multiprocessing import Pool
def ms(M):return ''.join('(%d,%d,%d)'%tuple(c) for c in M)
def meas(M):
    c=collections.Counter();e={}
    try:
        if A.frame(list(M)) is None: return c,e
        c1,e1=A.fields(list(M));c.update(c1);e.update(e1)
        if c1['ADS.fail']+c1['TPL.fail']>0 or random.random()<0.02:
            c2,e2=A.scope(list(M),(2,3));c.update(c2);e.update(e2)
            c3,e3=A.primary(list(M),(2,3));c.update(c3);e.update(e3)
    except Exception as ex:
        c['exception']+=1;e['exc']=(M,repr(ex))
    return c,e
if __name__=='__main__':
    inp,out,npr=sys.argv[1],sys.argv[2],int(sys.argv[3])
    S=[tuple(tuple(c) for c in M) for M in pickle.load(open(inp,'rb'))]
    S=[M for M in S if len(M)>=3]
    if len(sys.argv)>4:
        random.seed(5);random.shuffle(S);S=S[:int(sys.argv[4])]
    tot=collections.Counter();ex={}
    with Pool(npr) as p:
        for c,e in p.imap_unordered(meas,S,chunksize=50):
            tot.update(c)
            for k,v in e.items(): ex.setdefault(k,v)
    res={'n':len(S),'cnt':dict(sorted(tot.items())),'ex':{k:ms(v[0])+' '+str(v[1:]) for k,v in ex.items()}}
    json.dump(res,open(out,'w'),indent=1);print(inp,json.dumps(res['cnt']),flush=True)
