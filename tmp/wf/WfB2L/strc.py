import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from stepfacts3_core_trio_codex import Ctx
def parse(s):return [tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
def colLe(a,b):return a<=b  # lexicographic
def check(M):
 C=Ctx(M);L=len(M);P0=lambda i:C.e.par(0,i);P1=lambda i:C.e.par(1,i);ch=C.ch
 bump=C.e.bump;f={}
 f['R0P']=all(P0(c) is None or M[c][0]==M[P0(c)][0]+1 for c in range(L))
 f['R1S']=all(P0(c) is None or M[c][1]<=M[P0(c)][1]+1 for c in range(L))
 f['Z2']=all(c[2]<=1 for c in M);f['R12']=all(c[2]==0 for c in M if c[1]==0);f['R01']=all(c[1]==0 for c in M if c[0]==0)
 f['SibDec']=all(colLe(M[b],M[a]) for p in range(L) for a,b in zip(ch(p),ch(p)[1:]))
 f['Z1C']=all(M[c][1]<=M[p][1] for p in range(L) if M[p][2]==1 for c in ch(p))
 f['BumpE2']=all(M[p][2]==1 for p in range(L) for c in ch(p) if M[c]==bump(p))
 ok=True
 for k in range(L):
  for j in ch(k):
   if M[j]!=bump(k):continue
   for c in ch(j):
    if M[k][1]<=M[c][1]:
     ok&= M[c][2]==0 and ch(c)==[] and ch(j)[-1]==c and ch(k)[-1]==j
 f['BumpLeaf']=ok
 f['RowJ']=all(M[c][2]==0 or P0(c) is None or M[P0(c)][1]<=M[c][1] for c in range(L))
 ua=True;ub=True
 for i in range(L):
  c=C.upg(i)
  if c is None or c==i+1:continue
  chs=ch(c);ua&= not(chs==[] or M[chs[-1]]==bump(c))
  for j in chs:
   if M[j]==bump(c):
    q=i
    while q is not None and q>j:q=P0(q)
    ub&= q!=j
 f['UAT']=ua;f['UAB']=ub
 return f
if __name__=='__main__':
 for s in sys.argv[1:]:print(check(parse(s)))
