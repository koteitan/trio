import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfDrE')
from seedc import *
M=[tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',sys.argv[1])]
C=Ctx(M);T=Ctx(M[:-1]);x=len(M)-1;r=C.e.par(0,x);seed=T.o(r);o=C.o(r);mu=C.v(r);b=strip_last(o[1]);br=o[1]
print('r',r,'mu',Y.tstr(mu));print('b',Y.tstr(b));print('seed',Y.tstr(seed))
for i in range(x):
    for nm,t in (('o',C.o(i)),('v',C.v(i))):
        s=set();diag(t,br,mu,s)
        for a in s:print(' DP from',nm,i,M[i],Y.tstr(a),seedok(a,b,mu,seed))
