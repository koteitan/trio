"""Real B-frames (nonzero case): ArgDomCore instances (P,Q) with Q an ancestor of n (n in B) where B agrees with H
up to n's position (exclusive). Record the source column of H at n's position, relative to the frame."""
import sys,pickle,random,collections,json
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfB2L')
from multiprocessing import Pool
from stepfacts3_core_trio_codex import Ctx,SRO
import adc
def hsI(w1,e,f,M):  # M list of (col,idx)
 if not M:return []
 (p,i)=M[0];rest=M[1:];tw=[];
 for q in rest:
  if p[0]<q[0][0]:tw.append(q)
  else:break
 dw=rest[len(tw):]
 if w1<p[1]:return [((p[0]+e,p[1]+f,p[2]),i)]+hsI(w1,e,f,tw)+hsI(w1,e,f,dw)
 return [((p[0]+e,p[1],p[2]),i)]+[((q[0]+e,q[1],q[2]),ii) for q,ii in tw]+hsI(w1,e,f,dw)
def anc(C,a,b):
 while b is not None and b>a:b=C.e.par(0,b)
 return b==a
def s(M):return ''.join('(%d,%d,%d)'%t for t in M)
def run(batch):
 cnt=collections.Counter();ex={}
 for mm in batch:
  M=[tuple(c) for c in mm]
  if len(M)<3 or tuple(M)>=SRO:continue
  C=Ctx(M)
  if not C.ok:continue
  L=len(M)
  for n in range(L-1):
   k=C.upg(n)
   if k is None or k>=n:continue
   p=C.e.par(0,n);g=C.e.par(0,p) if p is not None else None
   if g is None or M[p]!=C.e.bump(g):continue
   m=C.e.par(0,k);bj=[j for j in C.ch(k) if M[j]==C.e.bump(k)]
   if all(M[c][1]==0 for j in bj for c in C.ch(j)):continue
   js=[j for j in bj if C.ch(j)];j=js[-1];c=C.ch(j)[0]
   i=M[m][1]-M[c][1]
   h=[d for d in C.ch(k) if anc(C,d,n)][0]
   nm={m:'m',k:'k',h:'h',g:'g',p:'p',n:'n',j:'j',c:'c'}
   found=[]
   for P in range(n):
    u,w1,z=M[P]
    if not anc(C,P,n) or P==n:continue
    end=P+1
    while end<L and M[end][0]>u:end+=1
    for Q in range(P+1,n):
     if not anc(C,Q,n) or M[Q][2]!=z:continue
     e=M[Q][0]-u;f=M[Q][1]-w1
     if e<=0 or f<0 or not(f==0 or z==0):continue
     A1=M[P+1:Q]
     if not adc.spineok(A1,u+e,w1+1):continue
     be=Q+1
     while be<end and M[be][0]>u+e:be+=1
     B=M[Q+1:be]
     H=hsI(w1,e,f,[(M[t],t) for t in range(P+1,end)])
     pos=n-(Q+1)
     if pos>=len(H):continue
     if all(B[t]==H[t][0] for t in range(pos)):
      src=H[pos][1]
      found.append((nm.get(P,'?'),nm.get(Q,'?'),nm.get(src,'?' if src not in C.ch(j) else 'cj'),B[pos]<=H[pos][0]))
   tag='i%d '%i+('tightc' if any(x[2]=='c' for x in found) else ('tight' if found else 'none'))
   cnt[tag]+=1
   for x in set(found):cnt['  %s%s->%s'%x[:3]]+=1
   if 'none' in tag and len(ex)<3:ex[tag+str(len(ex))]=s(M)+' n=%d k=%d m=%d j=%d c=%d h=%d g=%d'%(n,k,m,j,c,h,g)
 return cnt,ex
if __name__=='__main__':
 mats=pickle.load(open(sys.argv[1],'rb'));random.seed(1);random.shuffle(mats);mats=mats[:int(sys.argv[2])]
 cnt=collections.Counter();ex={}
 with Pool(2) as pool:
  for c,e in pool.imap_unordered(run,(mats[i:i+50] for i in range(0,len(mats),50)),chunksize=1):
   cnt.update(c);ex.update(e)
 print(json.dumps(dict(sorted(cnt.items())),indent=0));print(json.dumps(ex,indent=0))
