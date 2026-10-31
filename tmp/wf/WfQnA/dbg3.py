import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQnA')
from meas import *
s=sys.argv[1]
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
C,x,r=A.frame(M)
def P(t):
    if not t: return '0'
    a,b,c=t; h='p_{%s}(%s)'%(P(a),P(b)); return h+('+'+P(c) if c else '')
for j in (43,44,45,46,47,48,49):
    print(j,M[j],'o=',P(C.o(j)),' v=',P(C.v(j)))
print('bumpW44',P(C.bumpW(44)),'A',P(C.o(r)))
