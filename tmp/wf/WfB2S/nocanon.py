import sys,pickle
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from stepfacts3_core_trio_codex import *
from bad2_exact_trio_codex import bad2
def s(M):return ''.join('(%d,%d,%d)'%t for t in M)
for src in sys.argv[1:]:
 mats=pickle.load(open(src,'rb'))
 for mm in mats:
  M=[tuple(c) for c in mm]
  if len(M)<3 or tuple(M)>=SRO:continue
  C=Ctx(M)
  if not C.ok:continue
  for n in range(len(M)):
   k=C.upg(n)
   if k is None or k>=n:continue
   p=C.e.par(0,n);g=C.e.par(0,p) if p is not None else None
   if g is None or M[p]!=C.e.bump(g):continue
   if C.bumpW(k)[0]==Z: continue
   js=[j for j in C.ch(k) if M[j]==C.e.bump(k)]
   if not js or not C.ch(js[-1]):
    print(s(M),'n',n,'k',k,'js',js,'x-1?',n==len(M)-2,'kids',[(j,C.ch(j)) for j in js]); 
