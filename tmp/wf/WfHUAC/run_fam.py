"""Run deep_exist.run on the targeted family deepfam.pkl, with periodic progress."""
import sys,json,pickle,collections,time
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from multiprocessing import Pool
from deep_exist import run
if __name__=='__main__':
 mats=pickle.load(open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC/deepfam.pkl','rb'))
 cnt=collections.Counter();ex={};t0=time.time();done=0
 with Pool(4) as pool:
  for cc,ee in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200)),chunksize=1):
   cnt.update(cc);done+=200
   for t,e in ee.items():
    if t not in ex or len(e['M'])<len(ex[t]['M']):ex[t]=e
   if done%100000==0:
    json.dump({'done':done,'total':len(mats),'sec':time.time()-t0,'counts':dict(cnt),'ex':ex},open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC/deepfam_result.json','w'),indent=1)
    print(done,time.time()-t0,{k:v for k,v in cnt.items() if 'dangerTrue' in k or 'FAIL' in k},flush=True)
 json.dump({'done':done,'total':len(mats),'sec':time.time()-t0,'counts':dict(cnt),'ex':ex,'final':True},open('/home/koteitan/proofs/trio/tmp/wf/WfHUAC/deepfam_result.json','w'),indent=1)
 print('final',dict(cnt),flush=True)
