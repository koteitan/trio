import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQrH');sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA')
import oframe as O, trio
from probe_adn import Ctx, dependencies
import ytosk_eval as YE
s=sys.argv[1];n=int(sys.argv[2]);i=int(sys.argv[3])
M=[tuple(map(int,c.split(','))) for c in s.strip('()').split(')(')]
C=Ctx(M);N=[tuple(c) for c in trio.expand([list(c) for c in M],n)];CN=Ctx(N)
c=C.CL(i)[-1];L=C.ch(i)[:C.ch(i).index(c)]
pp=getattr(YE,'show',None) or getattr(YE,'pp',None) or repr
print('v',pp(C.v(i)));print('pre',pp(C.pre(i,L)));print('oc',pp(C.o(c)));print('oN',pp(CN.o(c)))
print('init y',pp(O.mk(O.summ(C.o(c)[1])[:-1])))
