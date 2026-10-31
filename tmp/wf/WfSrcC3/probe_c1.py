"""SrcC3Res context (shape frames, --all like probe_d4): relations of v(m'), v(m), v(c) vs v(r).
m = P1 i, b on P1-chain of m, k = upg b, m' = P0 k = P1 k, s = bumpW k summand of v(m) not absorbed."""
import sys,json,collections,pickle,time
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from multiprocessing import Pool
from huac_structure_trio_codex import Ctx,Y,lt,le,summ,Z
W2=(Z,(Z,Z,(Z,Z,Z)),Z)
def mt(M):return ''.join('(%d,%d,%d)'%tuple(t) for t in M)
def rel(a,b):return 'lt' if lt(a,b) else ('eq' if a==b else 'gt')
def chain1(E,m):
 out=[]
 while m is not None:out.append(m);m=E.par(1,m)
 return out
def anc(E,a,d):
 while d is not None:
  if d==a:return True
  d=E.par(0,d)
 return False
def run(batch):
 cnt=collections.Counter();ex=[]
 for mm in batch:
  M=[tuple(t) for t in mm]
  if len(M)<3 or not M[-1][2]:continue
  try:C=Ctx(M)
  except Exception:continue
  if not C.ok:continue
  E=C.e;x=len(M)-1;r=x-1
  if E.par(2,x)!=r or E.par(0,x)!=r or E.par(1,x)!=r:continue
  if E._upg[r] is None:continue
  p=E.par(0,r);i=E.par(0,p) if p is not None else None
  if i is None or not C.e12(i):continue
  g=i
  if M[p]!=E.bump(g):continue
  m=E.par(1,i)
  if m is None:continue
  V=C.v(m);W=C.bumpW(i);vr=C.v(r)
  for q in summ(V):
   if lt(q,W2) or not lt(q,W):continue
   from lhd_exact import lhd
   if lhd(q,W):continue
   for b in chain1(E,m):
    k=C.upg(b)
    if k is None or C.bumpW(k)!=q:continue
    mp=E.par(0,k)
    cnt['occ']+=1
    cnt['P0k_eq_P1k.'+str(mp==E.par(1,k))]+=1
    cnt['vmp_vr.'+rel(C.v(mp),vr)]+=1
    cnt['vm_vr.'+rel(V,vr)]+=1
    cnt['b_eq_m.'+str(b==m)]+=1
    cnt['mp_anc_r.'+str(anc(E,mp,r))]+=1
    cnt['k_anc_r.'+str(anc(E,k,r))]+=1
    for j in C.ch(k):
     if M[j]!=E.bump(k):continue
     for c in C.ch(j):
      rc=rel(C.v(c),vr)
      cnt['vc_vr.'+rc]+=1
      cnt['c_anc_r.'+str(anc(E,c,r))+'.'+rc]+=1
      if rc=='eq':
       cnt['eq.vmp_vr.'+rel(C.v(mp),vr)]+=1
       cnt['eq.cl_e1_lt.'+str(all(M[d][1]<M[c][1] for d in C.CL(c)))]+=1
       cnt['eq.e1c_e1r.'+rel(M[c][1],M[r][1]) if False else 'eq.e1c_vs_e1r.%s'%('lt' if M[c][1]<M[r][1] else 'eq' if M[c][1]==M[r][1] else 'gt')]+=1
       cnt['eq.e1c_vs_e1mp.%s'%('lt' if M[c][1]<M[mp][1] else 'eq' if M[c][1]==M[mp][1] else 'gt')]+=1
       if len(ex)<5:ex.append(dict(M=mt(M),r=r,i=i,m=m,b=b,k=k,mp=mp,j=j,c=c,vr=Y.tstr(vr),vmp=Y.tstr(C.v(mp))))
 return dict(cnt),ex
if __name__=='__main__':
 for nm in sys.argv[1:]:
  t=time.time()
  mats=pickle.load(open('/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets/%s.pkl'%nm,'rb'))
  cnt=collections.Counter();ex=[]
  with Pool(3) as pool:
   for c,b in pool.imap_unordered(run,(mats[i:i+300] for i in range(0,len(mats),300))):cnt.update(c);ex+=b
  print(nm,len(mats),round(time.time()-t),json.dumps(dict(sorted(cnt.items()))),json.dumps(ex[:3]),flush=True)
