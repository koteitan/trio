"""WfDrE: collect every matrix of a pkl on which invd.probe reports PV.FAIL or qrSeedC.FAIL (with info).
usage: nice -n 15 python3 collect.py OUT.json PKL..."""
import sys,pickle,json,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvD')
import invd
from multiprocessing import Pool
def w(b):
    out=[]
    for M in b:
        try:c,e=invd.probe(M)
        except Exception as er:continue
        for k,v in e.items():
            if k.startswith('PV.FAIL') or k.startswith('qrSeedC.FAIL'):out.append((k,v[1],v[2]))
    return out
if __name__=='__main__':
    res=[]
    for f in sys.argv[2:]:
        mats=pickle.load(open(f,'rb'))
        if isinstance(mats,dict):mats=mats['seeds']+mats['ext'] if 'seeds' in mats else list(mats.values())
        with Pool(4) as p:
            for o in p.imap_unordered(w,(mats[i:i+50] for i in range(0,len(mats),50))):res+=o
    json.dump(res,open(sys.argv[1],'w'))
    print(collections.Counter(r[0] for r in res))
