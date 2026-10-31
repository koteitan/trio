"""Check a matrix for the StepCtxT2 premises (all prefixes), Bad2, T2CBad, and print the t2 audit failures."""
import sys,json,re,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfReM')
import ctx36 as K
from graft import std,ms
import residual_extension_t2_trio_codex as T2
def parse(s):return [tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
if __name__=='__main__':
    M=parse(sys.argv[1]);print('len',len(M),'std',std(M))
    rep=[]
    for j in range(2,len(M)+1):K.one(M[:j],'take%d'%j,rep)
    bad=[r for r in rep if r['local_fail'] or r['struct'] or r['frame'] or r['inv_new']]
    print('last',json.dumps(rep[-1]))
    print('prefix failures',[(r['tag'],r['bad2'],list(r['local_fail'])+list(r['inv_new'])+list(r['frame'])+list(r['struct'])) for r in bad])
    cc,ee=T2.run([bytes(v for c in M for v in c)])
    print({k:v for k,v in cc.items() if 'fail' in k})
    for k,v in ee.items():
        if 'SeedCl' in k or 'T2' in k:print(k,{a:b for a,b in v.items() if a!='matrix'})
