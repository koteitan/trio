"""WfQrO: print triggered-arg o frames where PreB fails, with DQ path and first difference of pre vs y."""
import sys
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQrH');sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA')
import oframe as O, trio
from probe_adn import Ctx, dependencies, gamS, lift_counts
from probe_inv3_prefix import Z, lt, isOT, split, succ, isSucc, fsD
from ytosk_eval import tstr
def path(t,tN,eta,k=False):
    """DQ path: list of steps. k=True: t is a sum (true kind)."""
    if t==tN: return [('same',)]
    if k:
        sy=O.summ(t);sN=O.summ(tN)
        B=sy[:-1];l=sy[-1]
        assert sN[:len(B)]==B,(tstr(t),tstr(tN))
        Q=sN[len(B):-1];lN=sN[-1] if len(sN)>len(B) else Z
        return [('mk',len(B),tstr(O.mk(Q)))]+path(l,lN,eta)
    s,y,_=t;s2,y2,_=tN
    if s==s2 and y!=Z and y2!=y: return [('arg',tstr(s))]+path(y,y2,eta,True)
    if y==Z and y2==Z and s!=s2:
        try: return [('sub',)]+path(s,s2,eta,True)
        except AssertionError: pass
    return [('base',tstr(t),'fsD=' + str(fsD(t,eta)==tN))]
if __name__=='__main__':
    s=sys.argv[1];n=int(sys.argv[2])
    M=[tuple(map(int,c.split(','))) for c in s.strip('()').split(')(')]
    C=Ctx(M);x=len(M)-1;r=C.e.par(1,x)
    D=dependencies(C,x);A=C.o(r);mu,br,_=A;seed=Ctx(M[:x]).o(r);dl=lift_counts(C,x,A)
    N=[tuple(c) for c in trio.expand([list(c) for c in M],n)];CN=Ctx(N)
    print('M',s,'x',x,'r',r,'o(r)',tstr(A),'seed',tstr(seed))
    for i in range(x):
        if (True,i) not in D or (False,i) in D:continue
        CLi=C.CL(i)
        if not CLi or (True,CLi[-1]) not in D:continue
        c=CLi[-1];L=C.ch(i)[:C.ch(i).index(c)]
        pre=C.pre(i,L);v=C.v(i);oc=C.o(c);oN=CN.o(c)
        eta=gamS(mu,br,seed,n-2+dl[c])
        print('i',i,'c',c,'L',L,'v',tstr(v),'pre',tstr(pre));print('  oc',tstr(oc));print('  oN',tstr(oN));print('  eta',tstr(eta),'trigM',O.trig(v,pre,oc[0],oc[1]) if oc else None)
        print('  path',path(oc,oN,eta))
