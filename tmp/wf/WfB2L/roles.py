import sys,pickle,random,collections
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfB2S');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfB2L')
from multiprocessing import Pool
import fr6,strc,adc,gen_ns
from stepfacts3_core_trio_codex import Ctx
def anc(C,a,b):
 while b is not None and b>a:b=C.e.par(0,b)
 return b==a
def work(M):
 M=[tuple(c) for c in M];res=collections.Counter()
 for N in gen_ns.targeted(M):
  try:
   if not all(strc.check(N).values()):continue
   C=Ctx(N)
  except Exception:continue
  for n in range(len(N)-1):
   k=C.upg(n)
   if k is None or k>=n:continue
   p=C.e.par(0,n);g=C.e.par(0,p) if p is not None else None
   if g is None or N[p]!=C.e.bump(g):continue
   m=C.e.par(0,k);bj=[j for j in C.ch(k) if N[j]==C.e.bump(k)]
   if all(N[c][1]==0 for j in bj for c in C.ch(j)):continue
   js=[j for j in bj if C.ch(j)];c=C.ch(js[-1])[0]
   if N[m][1]<=N[c][1]+1:continue
   h=[d for d in C.ch(k) if anc(C,d,n)][0]
   V=adc.viol(N)
   nm={m:'m',k:'k',h:'h',g:'g',p:'p',n:'n'}
   roles=set((nm.get(P,'?'),nm.get(Q,'?')) for P,Q in V)
   res['k=m+1' if k==m+1 else 'k>m+1']+=1
   res['mh' if ('m','h') in roles else 'no-mh']+=1
   res['any' if V else 'NONE']+=1
   for r in roles:res['role '+'%s%s'%r]+=1
   break
 return res
if __name__=='__main__':
 mats=pickle.load(open(sys.argv[1],'rb'));random.seed(3);sd=random.sample(mats,min(int(sys.argv[2]),len(mats)))
 cnt=collections.Counter()
 with Pool(2) as pool:
  for r in pool.imap_unordered(work,sd,chunksize=2):cnt.update(r)
 print(dict(sorted(cnt.items())))
