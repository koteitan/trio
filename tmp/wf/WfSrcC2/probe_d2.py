"""SrcCRes (c): origins of non-absorbed summands at DropFail frames in the shape.
Usage: probe_d1.py SET...  ('grow' = cached grow.pkl of WfSrcC)"""
import sys,json,collections,pickle,time,os
ALL='--all' in sys.argv
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from multiprocessing import Pool
from huac_structure_trio_codex import Ctx,Y,lt,le,summ,Z
from lhd_exact import lhd
ONE=(Z,Z,Z);W2=(Z,(Z,Z,(Z,Z,Z)),Z)
def B(v):return (v,(Y.add(v,ONE),Z,Z),Z)
def Om(v):return (v,Z,Z)
def mt(M):return ''.join('(%d,%d,%d)'%tuple(t) for t in M)
def chain1(C,m):
 out=[]
 while m is not None:out.append(m);m=C.e.par(1,m)
 return out
def run(batch):
 cnt=collections.Counter();ex=[]
 for mm in batch:
  M=[tuple(t) for t in mm]
  if len(M)<3 or not M[-1][2]:continue
  try:E=Y.Ev(M)
  except Exception:continue
  x=len(M)-1
  if E._upg[x-1] is None:continue
  p=E.par(0,x-1);g=E.par(0,p) if p is not None else None
  if g is None or M[p]!=E.bump(g):continue
  C=Ctx(M);T=Ctx(M[:-1])
  if not C.ok or not T.ok:continue
  r=C.e.par(2,x)
  if r is None or r!=x-1:continue
  pr=C.e.par(0,r);i=C.e.par(0,pr)
  if i is None or not C.e12(i):continue
  V=C.vOpt1(i);W=C.bumpW(i);WT=T.bumpW(i)
  qs=[q for q in summ(V) if not lt(q,W2) and not lt(q,WT) and lt(q,W) and not lhd(q,W)]
  if not qs and not ALL:continue
  cnt['fail.'+str(bool(qs))]+=1
  vr=C.v(r);m=C.e.par(1,i)
  nl=[q for q in summ(V) if not lt(q,W2) and lt(q,W) and not lhd(q,W)]
  ch=chain1(C,m)
  for q in nl:
   cnt['nl']+=1
   cnt['sub_eq_vr.'+str(q[0]==vr)]+=1
   oall=[(b,C.upg(b)) for b in ch if C.upg(b) is not None and C.bumpW(C.upg(b))==q]
   cnt['n_oall.'+str(len(oall))]+=1
   for b,k in oall:
    okR=all(lt(C.o(c),B(vr)) for j in C.ch(k) if M[j]==C.e.bump(k) for c in C.ch(j))
    cnt['R_oc_lt_B.'+str(okR)]+=1
    okD=all(le(C.v(c),vr) and (C.v(c)!=vr or all(le(C.v(d),vr) for d in C.CL(c))) for j in C.ch(k) if M[j]==C.e.bump(k) for c in C.ch(j))
    cnt['D_v_le.'+str(okD)]+=1
    cnt['k_P0eqP1.'+str(C.e.par(0,k)==C.e.par(1,k))]+=1
    cnt['q_lt_B.'+str(lt(q,B(vr)))]+=1
    if not okR and len(ex)<6:ex.append(dict(bad='R',M=mt(M),r=r,i=i,k=k,q=Y.tstr(q),vr=Y.tstr(vr)))
   if q[0]!=vr:continue
   orig=[(b,C.upg(b)) for b in ch if C.upg(b) is not None and C.bumpW(C.upg(b))==q]
   cnt['n_orig.'+str(len(orig))]+=1
   for b,k in orig:
    bch=[j for j in C.ch(k) if M[j]==C.e.bump(k)]
    cnt['k_nbump.'+str(len(bch))]+=1
    if not bch:continue
    j0=bch[0];cs=C.ch(j0)
    if not cs:cnt['j0_nochild']+=1;continue
    c1=cs[0]
    cnt['q_eq_oc1.'+str(q==C.o(c1))]+=1
    cnt['v_c1_eq_vr.'+str(C.v(c1)==vr)]+=1
    cnt['c1_rows12_eq_r.'+str(M[c1][1:]==M[r][1:])]+=1
    cnt['c1_upg_eq_r.'+str(C.upg(c1)==C.upg(r))]+=1
    cnt['k_is_i.'+str(k==i)]+=1
    cnt['b_is_m.'+str(b==m)]+=1
    cl=C.CL(c1)
    cnt['c1_cl_e1_lt.'+str(all(M[d][1]<M[c1][1] for d in cl))]+=1
    cnt['c1_cl_v_le.'+str(all(le(C.v(d),C.v(c1)) for d in cl))]+=1
    cnt['c1_ch_v_le.'+str(all(le(C.v(d),C.v(c1)) for d in C.ch(c1)))]+=1
    cnt['k_upg_target_of_r.'+str(C.upg(r)==k)]+=1
    if False:ex.append(dict(M=mt(M),x=x,r=r,p=pr,i=i,m=m,b=b,k=k,j0=j0,c1=c1,q=Y.tstr(q),vr=Y.tstr(vr),upgr=C.upg(r),chain=ch))
 return dict(cnt),ex
def grow():
 return pickle.load(open('/home/koteitan/proofs/trio/tmp/wf/WfSrcC/grow.pkl','rb'))
if __name__=='__main__':
 out={}
 for nm in [a for a in sys.argv[1:] if a!='--all']:
  t=time.time()
  mats=grow() if nm=='grow' else pickle.load(open('/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets/%s.pkl'%nm,'rb'))
  cnt=collections.Counter();ex=[]
  with Pool(4) as pool:
   for c,b in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200))):cnt.update(c);ex+=b
  out[nm]={'counts':dict(sorted(cnt.items())),'ex':ex[:4],'sec':round(time.time()-t,1)}
  print(nm,json.dumps(out[nm],indent=0),flush=True)
 json.dump(out,open('/home/koteitan/proofs/trio/tmp/wf/WfSrcC2/probe_d2_%s.json'%'_'.join(sys.argv[1:]).replace('--','')[:60],'w'),indent=1)
