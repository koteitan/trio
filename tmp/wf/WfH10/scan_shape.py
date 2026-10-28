"""H10Big antecedent scan: frame + upg(r-1)=r + upg(x-1)=k + Bad2 shape (b = P0(P0(x-1)) bump parent, Anc0 b x).
Counts how often the full structural antecedent of H10Big occurs, and on it: entry1(g), parent value finite, strong.
Usage: nice -n 15 python3 scan_shape.py OUT.json set1 set2 ...   (set names in sets/, or 'graft' for codex graft family json cases)
"""
import sys,json,pickle,time,collections
from pathlib import Path
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Y
import t0_h8_f3_trio_codex as F

def anc(E,a,b):
 while b is not None:
  if a==b:return True
  b=E.par(0,b)
 return False

def run(batch):
 cnt=collections.Counter();cases={}
 for mm in batch:
  M=list(map(tuple,mm));cnt['input']+=1
  if len(M)<3 or M[-1][1] or not any(M[-1]):continue
  try:E=Y.Ev(M)
  except Exception:cnt['ev_fail']+=1;continue
  x=len(M)-1;r=E.par(0,x)
  if r is None or r==x-1:continue
  g=E.par(0,r)
  if g is None or r-1==g or M[r]==E.bump(g) or (r in E.upgs and E.topped(r)):continue
  if not Y.Ev(M[:-1]).topped(r):continue
  cnt['frame']+=1
  U=E._upg[r-1]==r;k=E._upg[x-1];K=k is not None
  p=E.par(0,x-1);b=E.par(0,p) if p is not None else None
  bp=p is not None and b is not None and M[p]==E.bump(b)
  sh=bp and anc(E,b,x)
  cnt['U.'+str(U)]+=1;cnt['K.'+str(K)]+=1
  if U and K:cnt['UK']+=1
  if K and sh:
   cnt['K_shape']+=1
   cnt['K_shape.b_eq_r.'+str(b==r)]+=1
  if U and K and bp:cnt['UK_bumpparent']+=1
  if not(U and K and sh):continue
  cnt['ANTECEDENT']+=1
  C=H.Ctx(M)
  if not C.ok:cnt['ctx_fail']+=1;continue
  V=C.vOpt1(x-1);fin=all(q==H.ONE for q in H.summ(V))
  st=F.strong(C,x)
  cnt['e1g.'+str(M[g][1])]+=1;cnt['finite.'+str(fin)]+=1;cnt['strong.'+str(st)]+=1
  text=''.join('(%d,%d,%d)'%t for t in M)
  cases[text]={'matrix':M,'r':r,'g':g,'x':x,'k':k,'p':p,'b':b,'e1g':M[g][1],'V':Y.tstr(V),'finite':fin,'strong':st}
 return dict(cnt),cases

if __name__=='__main__':
 out=Path(sys.argv[1]);names=sys.argv[2:];report={'sets':{}};start=time.time()
 with Pool(4) as pool:
  for nm in names:
   if nm=='graft':
    d=json.load(open('/home/koteitan/proofs/trio/tmp/codex/h10_u3_graft_trio_codex.json'))
    mats=[e['matrix'] for s in d['sets'].values() for e in s['cases'].values()]
   elif nm.endswith('.json'):
    mats=json.load(open(nm))
   else:mats=pickle.load(open(H.SETD/(nm+'.pkl'),'rb'))
   cnt=collections.Counter();cases={}
   for cc,ee in pool.imap_unordered(run,(mats[i:i+200] for i in range(0,len(mats),200)),chunksize=1):cnt.update(cc);cases.update(ee)
   report['sets'][nm]={'counts':dict(cnt),'cases':cases};report['seconds']=round(time.time()-start,2)
   out.write_text(json.dumps(report,indent=1)+'\n');print(nm,dict(cnt),round(time.time()-start),flush=True)
