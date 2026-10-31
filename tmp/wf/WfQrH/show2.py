import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQrH');sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA')
import oframe as O, trio
from probe_adn import Ctx, dependencies
from ytosk_eval import tstr
s=sys.argv[1];i=int(sys.argv[2])
M=[tuple(map(int,c.split(','))) for c in s.strip('()').split(')(')]
C=Ctx(M);x=len(M)-1;r=C.e.par(1,x)
c=C.CL(i)[-1];L=C.ch(i)[:C.ch(i).index(c)]
print('x',x,'r',r,'i',i,'c',c,'o(r)',tstr(C.o(r)),'o(x)',tstr(C.o(x)),'seed',tstr(Ctx(M[:x]).o(r)))
print('v',tstr(C.v(i)),' pre',tstr(C.pre(i,L)),' oc',tstr(C.o(c)))
for n in (2,3,4):
    N=[tuple(c) for c in trio.expand([list(c) for c in M],n)];CN=Ctx(N)
    print(n,'oN(c)',tstr(CN.o(c)),' oN(r)',tstr(CN.o(r)))
