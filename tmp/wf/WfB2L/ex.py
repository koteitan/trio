import sys,pickle,random
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from stepfacts3_core_trio_codex import *
def s(M):return ''.join('(%d,%d,%d)'%t for t in M)
mats=pickle.load(open(sys.argv[1],'rb'));random.seed(int(sys.argv[2]))
random.shuffle(mats);shown=0
for M in mats:
 M=[tuple(c) for c in M]
 if tuple(M)>=SRO:continue
 C=Ctx(M)
 if not C.ok:continue
 n=len(M)-2;k=C.upg(n)
 if k is None or k>=n:continue
 p=C.e.par(0,n);g=C.e.par(0,p) if p is not None else None
 if g is None or M[p]!=C.e.bump(g):continue
 m=C.e.par(0,k);bj=[j for j in C.ch(k) if M[j]==C.e.bump(k)]
 js=[j for j in bj if C.ch(j)]
 if not js or all(M[c][1]==0 for j in bj for c in C.ch(j)):continue
 c=C.ch(js[-1])[0]
 print(s(M));print(' n',n,'k',k,'m',m,'p',p,'g',g,'bj',bj,'js',js,'c',c,'M[c]',M[c],'M[m]',M[m],'chk',C.ch(k),'chc',[ (j,C.ch(j)) for j in bj])
 shown+=1
 if shown>=int(sys.argv[3]):break
