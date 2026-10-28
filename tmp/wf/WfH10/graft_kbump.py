"""Graft a bump child (and small subtrees) under k = upg(x-1) in H10Big antecedents, to test KNoBump.
Inserted right after k (first child) or right before h (k's last child).
Usage: nice -n 15 python3 graft_kbump.py IN.json(list of matrices) OUT.json
"""
import sys,json,collections,subprocess
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfH10')
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Y,lt,summ,Z
import t0_h8_f3_trio_codex as F
from gen_shape import antecedent,SRO
from multiprocessing import Pool

def kinfo(M):
 E=Y.Ev(list(M));x=len(M)-1;return E,x,E._upg[x-1]

def cands(M):
 E,x,k=kinfo(M);e0,a,_=M[k];h=E.children[k][-1]
 subs=[[(e0+1,a,1)]]
 for c1 in range(0,a+1):
  for z in (0,1):
   subs.append([(e0+1,a,1),(e0+2,c1,z)])
   subs.append([(e0+1,a,1),(e0+2,c1,z),(e0+3,c1,0)])
   subs.append([(e0+1,a,1),(e0+2,c1,z),(e0+2,c1,0)])
 out=[]
 for s in subs:
  for pos in (k+1,h):
   out.append(tuple(M[:pos])+tuple(s)+tuple(M[pos:]))
 return out

def work(batch):
 res=[]
 for M in batch:
  M=tuple(map(tuple,M))
  for N in cands(M):
   if N>=SRO or len(N)>160:continue
   a=antecedent(N)
   if a is None or a[2]<2:continue
   E=Y.Ev(list(N));x=len(N)-1;k=E._upg[x-1]
   nb=[j for j in E.children[k] if N[j]==E.bump(k)]
   if not nb:continue
   res.append(N)
 return res

if __name__=='__main__':
 mats=json.load(open(sys.argv[1]));cand=set()
 with Pool(3) as pool:
  for r in pool.imap_unordered(work,(mats[i:i+20] for i in range(0,len(mats),20))):cand|=set(r)
 print('structural KNoBump-violating antecedents',len(cand),flush=True)
 cnt=collections.Counter();bad=[]
 for N in sorted(cand,key=lambda N:(len(N),N)):
  text=''.join('(%d,%d,%d)'%t for t in N)
  o=subprocess.run(['/home/koteitan/proofs/trio/bms','-s',text],text=True,capture_output=True,check=True).stdout.strip()
  cnt['std.'+o]+=1
  if o=='1':
   C=H.Ctx(list(N));x=len(N)-1;st=C.ok and F.strong(C,x);cnt['strong.'+str(st)]+=1
   bad.append({'matrix':text,'strong':st,'V':Y.tstr(C.vOpt1(x-1)) if C.ok else None,'W':Y.tstr(C.bumpW(C.upg(x-1))) if C.ok else None})
 print(dict(cnt));json.dump({'counts':dict(cnt),'cases':bad},open(sys.argv[2],'w'),indent=1)
