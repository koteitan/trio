"""Audit the derived family set: every prefix (len >= 2) of every family member M and of M[2], M[3] (tools/trio.expand),
deduplicated (incremental prefix digests), streamed. Shards of 10000 maximal matrices; resumable (OUT.jsonl).
usage: nice -n 15 python3 fam_run.py OUT.jsonl NPROC"""
import sys,os,json,pickle,collections,time,hashlib
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvX');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import audit as A
import trio
from fam import FAMS,W
from multiprocessing import Pool
def maximal():
    mem=set()
    for f in FAMS:
        for M in pickle.load(open(W+f,'rb')):mem.add(tuple(tuple(c) for c in M))
    out=set(mem)
    for M in mem:
        for n in (2,3):out.add(tuple(tuple(c) for c in trio.expand([list(c) for c in M],n)))
    return sorted(out,key=lambda N:(len(N),N))
def prefixes(N,seen):
    h=hashlib.blake2b(digest_size=16)
    for j,c in enumerate(N):
        h.update(bytes(c) if max(c)<256 else repr(c).encode()); d=h.copy().digest()
        if j>=1 and d not in seen:
            seen.add(d); yield N[:j+1]
SH=10000
if __name__=='__main__':
    out=sys.argv[1];npr=int(sys.argv[2])
    done=set()
    if os.path.exists(out):
        for l in open(out):done.add(json.loads(l)['shard'])
    mx=maximal();print('maximal',len(mx),flush=True)
    seen=set()
    with Pool(npr) as pool:
        for sh in range(0,len(mx),SH):
            part=mx[sh:sh+SH]
            if sh in done:
                for N in part:
                    for _ in prefixes(N,seen):pass
                continue
            t=time.time();jobs=[];b=[]
            for N in part:
                for P in prefixes(N,seen):
                    b.append(P)
                    if len(b)>=40:jobs.append(b);b=[]
            if b:jobs.append(b)
            n=sum(len(b) for b in jobs);cnt=collections.Counter();ex={}
            for c,e in pool.imap_unordered(A.work,jobs):cnt.update(c);A.merge(ex,e)
            rec={'set':'family_prefixes','shard':sh,'maximal':len(part),'n':n,'sec':round(time.time()-t),'cnt':dict(sorted(cnt.items())),
                 'ex':{k:[(w[0],A.ms(w[1]),w[2]) for w in L] for k,L in ex.items()}}
            with open(out,'a') as fo:fo.write(json.dumps(rec)+'\n')
            print(json.dumps({'shard':sh,'n':n,'sec':rec['sec'],'fails':{k:v for k,v in cnt.items() if k.endswith('.fail') or 'exception' in k or 'internal' in k or 'eval_failed' in k}}),flush=True)
