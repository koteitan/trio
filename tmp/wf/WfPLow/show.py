import sys,json
sys.path[:0]=['tmp/codex','tools']
from t2src_a_trio_codex import *
def show(mt,x,i,j,c,m):
    M=[tuple(map(int,s.split(','))) for s in mt.strip('()').split(')(')]
    C=Ctx(M);T=Ctx(M[:x])
    print(mt)
    def chain1(k):
        r=[]
        while k is not None:r.append(k);k=C.e.par(1,k)
        return r
    def chain0(k):
        r=[]
        while k is not None:r.append(k);k=C.e.par(0,k)
        return r
    print('x',x,'i',i,'j',j,'c',c,'m',m)
    print('row0 anc of x-1',chain0(x-1))
    print('row1 chain m',[(k,M[k]) for k in chain1(m)])
    print('row1 chain c',[(k,M[k]) for k in chain1(c)])
    for k in sorted(set(chain1(m)+chain1(c)+[i,j,c])):
        print(k,M[k],'v=',Y.tstr(C.v(k)),' o=',Y.tstr(C.o(k)), ' oT=',Y.tstr(T.o(k)) if k<x else '')
    print('W',Y.tstr(C.bumpW(i)),'WT',Y.tstr(T.bumpW(i)))
if __name__=='__main__':
    d=json.load(open('tmp/wf/WfSrcP/p7.json'))
    for s,r in d['sets'].items():
        for t,e in r['examples'].items():
            if t.endswith(sys.argv[1]) and s.endswith(sys.argv[2]):
                print('==',s,t);show(e['matrix_text'],e['x'],e['i'],e['j'],e['c'],e['m'])
