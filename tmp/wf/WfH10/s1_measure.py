"""S1 seed fact in the H10 case: o_N(g) = psi_{v g}(X') lhd o(g) = psi_{v g}(X), N = M[n], n=2,3,4.
Input: json list of matrices (H10 antecedent structure: frame + upg(r-1)=r). Counts Bad2 separately."""
import sys,json,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfH10')
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Y,lt
import t0_h8_f3_trio_codex as F
from lhd_exact import lhd
from h10_u3_trio_codex import trio
from multiprocessing import Pool
def work(batch):
 cnt=collections.Counter();bad=[]
 for mm in batch:
  M=[tuple(t) for t in mm];E=Y.Ev(M);x=len(M)-1;r=E.par(0,x);g=E.par(0,r)
  if E._upg[r-1]!=r:continue
  C=H.Ctx(M)
  if not C.ok:cnt['evalfail']+=1;continue
  p=E.par(0,x-1);b=E.par(0,p) if p is not None else None
  bad2=E._upg[x-1] is not None and b is not None and M[p]==E.bump(b) and F.anc(C,b,x) and not F.strong(C,x)
  tag='Bad2' if bad2 else 'notBad2'
  for n in (2,3,4):
   N=trio.expand(M,n);D=H.Ctx(N)
   if not D.ok:cnt[tag+'.evalfailN']+=1;continue
   oN,o=D.o(g),C.o(g);ok=D.v(g)==C.v(g) and oN[0]==o[0] and not oN[2] and lhd(oN,o)
   cnt[tag+'.S1.'+str(ok)]+=1;cnt[tag+'.countedN.'+str(D.counted(g,r))]+=1
   if not ok:bad.append(''.join('(%d,%d,%d)'%t for t in M))
 return cnt,bad
if __name__=='__main__':
 mats=[]
 for f in sys.argv[1:]:
  d=json.load(open(f))
  if isinstance(d,list):mats+=d
  elif 'cases' in d and isinstance(d['cases'],list):mats+=[[tuple(map(int,t.split(','))) for t in c['matrix'].strip('()').split(')(')] for c in d['cases']]
 cnt=collections.Counter();bad=[]
 with Pool(3) as pool:
  for c,b in pool.imap_unordered(work,(mats[i:i+20] for i in range(0,len(mats),20))):cnt.update(c);bad+=b
 print(dict(cnt));print(bad[:3])
