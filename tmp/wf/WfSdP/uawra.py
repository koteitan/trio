"""WfSdP uawra: UAwRA = WCS2(v(x-1), V+1) at every level u (not only u <= v(x-1)) = the VrDomQ form. Copied from uawr: WCS2(v(x-1), V+1) in the weak absorption case (UAwR), and domV. Copied from WfDrE: the absorption hypothesis hX1 of drop_all_hardW2 (UAw2), exact Lean form (2026-10-31):
for i = x - 1, upg M i = some k, v(k) = V + W (V = vOpt v (P1 i), W != 0):
  (forall r in summands V, r < W -> Lhd z r W)  or  WCSP2 M v i (V + 1).
Also UAw (WCSP in place of WCSP2) for comparison. usage: nice -n 15 python3 uaw2.py NPROC PKL..."""
import sys,os,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvD')
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfDrE');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfSdP')
from probe_inv3_prefix import Ctx,Z,ONE,lt,le,isOT
from lhd_exact import lhd,comps
import probe_dropres as D, ytosk_eval as Y, invd
from pv2 import WCS2, load
from seedp import domV
def WCS2A(a,w):
    W=(w,Z,Z);us={Z,a};D.indices(a,us);D.indices(w,us)
    for u in us:
        mx=D.tmax(comps(u,a))
        for g in comps(u,w):
            if not (le(g,W) or (mx is not None and le(g,mx))):return False
    return True
def probe(M):
    M=[tuple(c) for c in M];cnt=collections.Counter();ex={}
    if not M<invd.SRO or len(M)<3:return cnt,ex
    x=len(M)-1;C=Ctx(M)
    if not C.ok:return cnt,ex
    k1=C.upg(x-1)
    if k1 is None:return cnt,ex
    i=x-1;p1=C.e.par(1,i);V=C.v(p1) if p1 is not None else Z;w=Y.add(V,ONE)
    p0=C.e.par(0,i);a=C.v(p0) if p0 is not None else Z
    cs=D.CS(w);w1=cs or D.WCS(a,w);w2=cs or WCS2(a,w)
    for W in invd.decomps(V,C.v(k1)):
        cnt['cases']+=1
        if all(not lt(r,W) or lhd(r,W) for r in invd.summ(V)):cnt['strong']+=1;continue
        cnt['weak']+=1
        vi=C.v(i);wr=WCS2A(vi,w);dv=domV(V,vi)
        cnt['weak.UAwRA=%d.domV=%d.UAw2=%d'%(wr,dv,w2)]+=1
        if not wr:
            cnt['UAwRA.FAIL']+=1
            if 'UAwRA.FAIL' not in ex or len(M)<ex['UAwRA.FAIL'][0]:ex['UAwRA.FAIL']=(len(M),invd.ms(M),Y.tstr(W)[:100])
    return cnt,ex
def work(b):
    cnt=collections.Counter();ex={}
    for M in b:
        try:c,e=probe(M)
        except Exception as er:c=collections.Counter({'exc':1});e={'exc':(len(M),invd.ms(M),repr(er)[:200])}
        cnt.update(c)
        for k,v in e.items():
            if k not in ex or v[0]<ex[k][0]:ex[k]=v
    return cnt,ex
if __name__=='__main__':
    npr=int(sys.argv[1]);lim=int(os.environ.get('LIMIT','0'))
    for f in sys.argv[2:]:
        t0=time.time();mats=load(f)
        if lim and len(mats)>lim:
            import random;random.seed(5);mats=random.sample(mats,lim)
        cnt=collections.Counter();ex={}
        with Pool(npr) as p:
            for c,e in p.imap_unordered(work,(mats[i:i+100] for i in range(0,len(mats),100))):
                cnt.update(c)
                for k,v in e.items():
                    if k not in ex or v[0]<ex[k][0]:ex[k]=v
        print(json.dumps({'set':f.split('/')[-1],'n':len(mats),'sec':round(time.time()-t0),'cnt':dict(sorted(cnt.items())),'ex':ex}),flush=True)
