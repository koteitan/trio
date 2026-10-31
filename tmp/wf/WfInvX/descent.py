"""(4) Evaluator descent on the new families: for every family member M (and every prefix of M), with
v = tools/ytosk_eval.Ev(.).value(), check v(M[n]) < v(M) for n = 1, 2, 3 (tools/trio.expand).
usage: nice -n 15 python3 descent.py OUT.json NPROC [--prefixes]"""
import sys,json,pickle,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvX')
import ytosk_eval as Y, trio
from fam import FAMS,W
from multiprocessing import Pool
def ms(M):return ''.join('(%d,%d,%d)'%tuple(c) for c in M)
def one(M):
    c=collections.Counter();bad=[]
    v=Y.Ev([tuple(x) for x in M]).value()
    if v is None:c['eval_none']+=1;return c,[(len(M),ms(M),'M eval None')]
    for n in (1,2,3):
        N=[tuple(x) for x in trio.expand([list(x) for x in M],n)]
        w=Y.Ev(N).value();c['pairs']+=1
        if w is None:c['eval_none_exp']+=1;bad.append((len(M),ms(M),n,'None'));continue
        if Y.lt(w,v):c['desc']+=1
        else:c['FAIL']+=1;bad.append((len(M),ms(M),n))
    return c,bad
def work(b):
    C=collections.Counter();B=[]
    for M in b:c,bb=one(M);C.update(c);B+=bb
    return C,B
if __name__=='__main__':
    mem=set()
    for f in FAMS:
        for M in pickle.load(open(W+f,'rb')):
            M=tuple(tuple(c) for c in M);mem.add(M)
            if '--prefixes' in sys.argv:
                for j in range(2,len(M)):mem.add(M[:j])
    mem=sorted(mem,key=lambda M:(len(M),M));C=collections.Counter();B=[]
    with Pool(int(sys.argv[2])) as p:
        for c,b in p.imap_unordered(work,(mem[i:i+100] for i in range(0,len(mem),100))):C.update(c);B+=b
    B.sort();r={'matrices':len(mem),'prefixes':'--prefixes' in sys.argv,'cnt':dict(C),'bad':B[:50]}
    json.dump(r,open(sys.argv[1],'w'),indent=1);print(json.dumps({k:v for k,v in r.items() if k!='bad'}),B[:3])
