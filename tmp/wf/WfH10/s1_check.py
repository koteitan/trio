import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex');sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import huac_structure_trio_codex as H
from huac_structure_trio_codex import Y,lt
from lhd_exact import lhd
from h10_u3_trio_codex import trio
s=sys.argv[1];r=int(sys.argv[2]);g=int(sys.argv[3])
M=[tuple(map(int,t.split(','))) for t in s.strip('()').split(')(')]
C=H.Ctx(M);print('o(g)',Y.tstr(C.o(g)),'v(g)',Y.tstr(C.v(g)))
for n in (2,3,4):
 N=trio.expand(M,n);D=H.Ctx(N)
 print(n,'o_N(g)',Y.tstr(D.o(g)),'v_N(g)',Y.tstr(D.v(g)),'o_N<o',lt(D.o(g),C.o(g)),'lhd',lhd(D.o(g),C.o(g)),'counted_N(g,r)',D.counted(g,r))
