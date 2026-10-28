"""T2AbsNBad decomposition audit on more sets.  For every failed-drop column (no L / i filter):
 shape  : L = 1 and i = P0(P0 r)
 srcB   : every failing summand q < B(v_M(r)),  B(v) = psi_v(Omega_{v+1})
 vrN    : v_N(r) = v_M(r)  (n = 2,3)
 BleWN  : B(v_N(r)) <= bumpW_N(i)  (n = 2,3)
 goal   : q < bumpW_N(i)  (n = 2,3)
Usage: probe_sets.py SET [SET...]   (set name in tmp/ytosk-handoff/sets, or 'grow')."""
import sys,json,collections,pickle,time
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from multiprocessing import Pool
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Ctx,Y,lt,le,summ,Z
from lhd_exact import lhd
import trio
ONE=(Z,Z,Z);W2=(Z,(Z,Z,(Z,Z,Z)),Z)
def B(v):return (v,(Y.add(v,ONE),Z,Z),Z)
def mt(M):return ''.join('(%d,%d,%d)'%tuple(t) for t in M)
def run(batch):
 cnt=collections.Counter();bad=[];cases=[]
 for mm in batch:
  M=[tuple(t) for t in mm];cnt['input']+=1
  if len(M)<3 or not M[-1][2]:continue
  try:E=Y.Ev(M)
  except Exception:cnt['ev_exc']+=1;continue
  x=len(M)-1
  if E._upg[x-1] is None:continue
  p=E.par(0,x-1);g=E.par(0,p) if p is not None else None
  if g is None or M[p]!=E.bump(g):continue
  cnt['shape_pre']+=1
  C=Ctx(M);T=Ctx(M[:-1])
  if not C.ok or not T.ok:cnt['eval_FAIL']+=1;continue
  r=C.e.par(2,x)
  if r is None:continue
  for i in range(x):
   if not C.e12(i):continue
   V=C.vOpt1(i);W=C.bumpW(i);WT=T.bumpW(i)
   qs=[q for q in summ(V) if not lt(q,W2) and not lt(q,WT) and lt(q,W) and not lhd(q,W)]
   if not qs:continue
   cnt['fail_cols']+=1;cases.append(mt(M)+':%d'%i)
   pr=C.e.par(0,r);gg=C.e.par(0,pr) if pr is not None else None
   sh=(x-r==1 and i==gg);cnt['shape.'+str(sh)]+=1
   vrM=C.v(r);sb=all(lt(q,B(vrM)) for q in qs);cnt['srcB.'+str(sb)]+=1
   if not sh or not sb:bad.append(('src',mt(M),i,r,sh,sb))
   for n in (2,3):
    N=trio.expand(M,n);CN=Ctx(N)
    if not CN.ok:cnt['N_FAIL']+=1;continue
    vrN=CN.v(r);WN=CN.bumpW(i)
    for tag,ok in (('vrN',vrN==vrM),('BleWN',le(B(vrN),WN)),('goal',all(lt(q,WN) for q in qs))):
     cnt[tag+'.'+str(ok)]+=1
     if not ok:bad.append((tag,mt(M),i,r,n))
 return dict(cnt),bad,cases
def grow(depth=3,maxlen=130):
 d=json.load(open('/home/koteitan/proofs/trio/tmp/codex/t2_absn_growth_trio_codex.json'))
 seeds=set()
 for s in d['sets'].values():
  for e in s['cases'].values():seeds.add(tuple(map(tuple,e['matrix'])))
 fam=set(seeds);front=set(seeds)
 for _ in range(depth):
  new=set()
  for M in front:
   for n in range(1,5):
    N=tuple(map(tuple,trio.expand(list(M),n)))
    if len(N)>maxlen:continue
    for k in range(3,len(N)+1):new.add(N[:k])
  front=new-fam;fam|=new;print('grow',len(front),len(fam),flush=True)
 return [list(M) for M in fam]
if __name__=='__main__':
 out={}
 for nm in sys.argv[1:]:
  t=time.time()
  mats=grow() if nm=='grow' else pickle.load(open('/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets/%s.pkl'%nm,'rb'))
  cnt=collections.Counter();bad=[];cases=set()
  with Pool(4) as pool:
   for c,b,cs in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200))):cnt.update(c);bad+=b;cases.update(cs)
  del mats
  out[nm]={'counts':dict(cnt),'bad':bad[:20],'nbad':len(bad),'distinct_cases':len(cases),'sec':round(time.time()-t,1)}
  print(nm,json.dumps(out[nm]),flush=True)
  json.dump(out,open('/home/koteitan/proofs/trio/tmp/wf/WfT2Abs/probe_sets_%s.json'%'_'.join(sys.argv[1:])[:60],'w'),indent=1)
