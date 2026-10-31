import sys,re
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
from probe_inv3_prefix import Ctx,Z,lt,le,summ
import trio, ytosk_eval as Y
from lhd_exact import lhd, comps
def parse(s): return [tuple(map(int,t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)',s)]
def depx(C,x):
    M=C.M;D=set([('o',x)]);ch=True
    while ch:
        ch=False
        for i in range(len(M)):
            new=[]
            for c in C.ch(i):
                if M[c]!=C.e.bump(i) and not (c in C.e.upgs and C.e.topped(c)) and ('o',c) in D: new.append(('o',i))
            if ('v',i) in D: new.append(('o',i))
            if M[i][1]!=0:
                p=C.e.par(1,i)
                if p is not None and ('v',p) in D: new.append(('v',i))
                if M[i][2]==0:
                    k=C.upg(i)
                    if k is not None and ('v',k) in D: new.append(('v',i))
                else:
                    for j in C.ch(i):
                        if M[j]==C.e.bump(i):
                            for k in C.ch(j):
                                if ('o',k) in D: new.append(('v',i))
            for n in new:
                if n not in D: D.add(n); ch=True
    return D
def run(s,ns=(2,3)):
    M=parse(s);C=Ctx(M);x=len(M)-1
    D=depx(C,x)
    for n in ns:
        N=trio.expand(M,n);CN=Ctx(N)
        print('n=',n,'len',len(N))
        for i in range(x):
            for kind,a,b in (('o',C.o(i),CN.o(i)),('v',C.v(i),CN.v(i))):
                if a==b: continue
                print(' ',kind,i,M[i],'dep' if (kind,i) in D else 'NODEP','lt',lt(b,a),'lhd',lhd(b,a))
                print('    M :',Y.tstr(a)); print('    N :',Y.tstr(b))
if __name__=='__main__':
    run(open(sys.argv[1]).read().strip())
