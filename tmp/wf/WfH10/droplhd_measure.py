"""In the H10 case (frame + upg(r-1)=r, topped take): does the drop at r satisfy o_{M.take x}(r) lhd o_M(r)?"""
import sys,json,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Y,lt
import t0_h8_f3_trio_codex as F
from lhd_exact import lhd
from multiprocessing import Pool
def work(batch):
 cnt=collections.Counter();bad=[]
 for mm in batch:
  M=[tuple(t) for t in mm];E=Y.Ev(M);x=len(M)-1;r=E.par(0,x);g=E.par(0,r)
  if E._upg[r-1]!=r:continue
  C=H.Ctx(M);T=H.Ctx(M[:-1])
  p=E.par(0,x-1);b=E.par(0,p) if p is not None else None
  bad2=E._upg[x-1] is not None and b is not None and M[p]==E.bump(b) and F.anc(C,b,x) and not F.strong(C,x)
  tag=('Bad2' if bad2 else 'notBad2')+'.e1g'+str(M[g][1])
  ok=lhd(T.o(r),C.o(r));cnt[tag+'.dropLhd.'+str(ok)]+=1
  cnt[tag+'.vr_le_vg.'+str(not lt(C.v(g),C.v(r)))]+=1
  if not ok:bad.append(''.join('(%d,%d,%d)'%t for t in M))
 return cnt,bad
if __name__=='__main__':
 mats=[]
 for f in sys.argv[1:]:
  d=json.load(open(f))
  if isinstance(d,list):mats+=d
  else:mats+=[[tuple(map(int,t.split(','))) for t in c['matrix'].strip('()').split(')(')] for c in d['cases']]
 cnt=collections.Counter();bad=[]
 with Pool(3) as pool:
  for c,b in pool.imap_unordered(work,(mats[i:i+20] for i in range(0,len(mats),20))):cnt.update(c);bad+=b
 for k in sorted(cnt):print(k,cnt[k])
 print(sorted(bad,key=len)[:3])
