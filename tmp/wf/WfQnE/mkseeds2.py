import sys,pickle
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQnE')
import analyze as A
from multiprocessing import Pool
def f(M):
    c,_=A.fields(list(M)); return M if c['ADS.fail']+c['TPL.fail']>0 else None
if __name__=='__main__':
    G=pickle.load(open(sys.argv[1],'rb'))
    with Pool(4) as p: S=[M for M in p.map(f,G,chunksize=20) if M]
    print(len(S)); pickle.dump(S,open(sys.argv[2],'wb'))
