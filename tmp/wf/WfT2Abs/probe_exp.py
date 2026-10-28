"""T2AbsNExp on the necessary-Bad2 superset (no drop-failure filter):
x last, row2(x)!=0, upg(x-1) exists, p=P0(x-1), g=P0(p), col p = bump g, r=P2(x)=x-1 (L=1), e1 g, e2 g != 0.
Check B(v_M(r)) <= W_N(g) and v_N(r)=v_M(r) for n=2,3."""
import sys,json,collections,pickle,time
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfT2Abs')
from probe_sets import *
def run2(batch):
 cnt=collections.Counter();bad=[]
 for mm in batch:
  M=[tuple(t) for t in mm];cnt['input']+=1
  if len(M)<3 or not M[-1][2]:continue
  try:E=Y.Ev(M)
  except Exception:continue
  x=len(M)-1
  if E._upg[x-1] is None:continue
  p=E.par(0,x-1);g=E.par(0,p) if p is not None else None
  if g is None or M[p]!=E.bump(g):continue
  if E.par(2,x)!=x-1 or M[g][1]==0 or M[g][2]==0:continue
  C=Ctx(M)
  if not C.ok:cnt['eval_FAIL']+=1;continue
  cnt['ante']+=1;r=x-1;vr=C.v(r)
  for n in (2,3):
   N=trio.expand(M,n);CN=Ctx(N)
   if not CN.ok:cnt['N_FAIL']+=1;continue
   WN=CN.bumpW(g)
   a=le(B(vr),WN);b=CN.v(r)==vr
   cnt['BleWN.'+str(a)]+=1;cnt['vrN.'+str(b)]+=1
   if not a or not b:bad.append((mt(M),n,a,b))
 return dict(cnt),bad
if __name__=='__main__':
 out={}
 for nm in sys.argv[1:]:
  t=time.time()
  mats=grow() if nm=='grow' else pickle.load(open('/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets/%s.pkl'%nm,'rb'))
  cnt=collections.Counter();bad=[]
  with Pool(4) as pool:
   for c,b in pool.imap_unordered(run2,(mats[i:i+200] for i in range(0,len(mats),200))):cnt.update(c);bad+=b
  del mats
  out[nm]={'counts':dict(cnt),'bad':bad[:20],'nbad':len(bad),'sec':round(time.time()-t,1)}
  print(nm,json.dumps(out[nm]),flush=True)
  json.dump(out,open('/home/koteitan/proofs/trio/tmp/wf/WfT2Abs/probe_exp_%s.json'%'_'.join(sys.argv[1:])[:60],'w'),indent=1)
