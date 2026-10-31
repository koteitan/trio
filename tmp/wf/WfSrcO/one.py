import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/codex')
from t2src_a_trio_codex import *
def parse(s):
    return [tuple(int(t) for t in p.split(',')) for p in s.strip('()').split(')(')]
M=parse(sys.argv[1]);x=len(M)-1
E=Y.Ev(M);C=Ctx(M);T=Ctx(M[:x])
print('ok',C.ok,T.ok)
for k in range(x):
    print(k,M[k],'P0',E.par(0,k),'P1',E.par(1,k),'upg',E._upg[k],'oM',C.o(k),'oT',T.o(k), 'chg', C.o(k)!=T.o(k))
