"""ArgDomCoreOn checker (TRIO/lean/Core.lean) on a matrix: returns list of violating (P,Q)."""
def collt(a,b):return a<b
def seqlex(M,N):
 for p,q in zip(M,N):
  if p!=q:return p<q
 return len(M)<len(N)
def sle(M,N):return M==N or seqlex(M,N)
def shiftr01(d0,d1,M):return [(p[0]+d0,p[1]+d1,p[2]) for p in M]
def takeW(rest,a):
 out=[]
 for q in rest:
  if a<q[0]:out.append(q)
  else:break
 return out
def hshift(w1,e,f,M):
 if not M:return []
 p=M[0];rest=M[1:];tw=takeW(rest,p[0]);dw=rest[len(tw):]
 if w1<p[1]:return [(p[0]+e,p[1]+f,p[2])]+hshift(w1,e,f,tw)+hshift(w1,e,f,dw)
 return [(p[0]+e,p[1],p[2])]+shiftr01(e,0,tw)+hshift(w1,e,f,dw)
def spineok(A,L,w):
 for i,x in enumerate(A):
  if x[0]<L and all(x[0]<y[0] for y in A[i+1:]) and not w<=x[1]:return False
 return True
def viol(M,first=False):
 out=[];n=len(M)
 for P in range(n):
  u,w1,z=M[P]
  # P's subtree end
  end=P+1
  while end<n and M[end][0]>u:end+=1
  for Q in range(P+1,end):
   if M[Q][2]!=z or M[Q][0]<=u:continue
   e=M[Q][0]-u;f=M[Q][1]-w1
   if f<0 or not(f==0 or z==0):continue
   A1=M[P+1:Q]
   if not spineok(A1,u+e,w1+1):continue
   be=Q+1
   while be<end and M[be][0]>u+e:be+=1
   B=M[Q+1:be];A2=M[be:end]
   if not sle(B,hshift(w1,e,f,A1+[M[Q]]+B+A2)):
    out.append((P,Q))
    if first:return out
 return out
