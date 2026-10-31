"""All matrices of a pkl where the qn seed path clause (SeedCl.qn.path of residual_extension_t2 = third conjunct of
T2SeedQNBaseR, a field of T2SeedClV2R = hClR) fails. Output qnpath_<set>.json sorted by length."""
import sys,pickle,json,os
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from multiprocessing import Pool
def go(mm):
    import residual_extension_t2_trio_codex as T2
    M=[tuple(c) for c in mm]
    if not M[-1][2]:return None
    cc,ee=T2.run([bytes(v for c in M for v in c)])
    if cc.get('SeedCl.qn.path.failures'):
        e=ee['SeedCl.qn.path'];return (len(M),''.join('(%d,%d,%d)'%c for c in M),e.get('u'),e.get('g'),cc['SeedCl.qn.path.failures'])
    return None
if __name__=='__main__':
    f=sys.argv[1];mats=pickle.load(open(f,'rb'))
    with Pool(4) as p:res=[r for r in p.imap_unordered(go,mats,chunksize=50) if r]
    res.sort();json.dump(res,open('qnpath_%s.json'%os.path.basename(f)[:-4],'w'),indent=0)
    print(len(res),res[:3])
