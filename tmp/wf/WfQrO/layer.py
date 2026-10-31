"""WfQrO: single-layer fields of OmSide1 (WfQrO2.omSide1_of) at the bump frames of the q = r engine (oframe.py layers),
n = 2, 3.  Layer Y -> YN (both >= E0, Y single); eta ranges over gamS(mu, b_r, seed, k), k = 0..4, with DQ eta true Y YN.
 YNsingle : YN is a single summand          (hQ0)
 Arg      : YN = psi_a(bN) (same a), b != 0 -> DQ eta true b bN   (hArg)
 LoNot1   : last(b) != 1
 LoG      : lo(b) = 0 -> every decomposition has a DQG witness lc >= Om_{a+1}, lN single   (hLo via lo_keep_G)
 HB       : YN = fsD(Y, eta) -> fsD(omega Y) = omega(fsD Y) and < omega Y                       (hB)
usage: CAP=2000 NPR=3 nice -n 15 python3 layer.py OUT.jsonl PKL..."""
import sys,os,pickle,json,collections,time,random
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQrO')
from og import *
from probe_inv3_prefix import sumN, ONE
import ytosk_eval as YE
E0=(Z,(ONE1,Z,Z),Z)
def check(M,cnt,ex):
    x=len(M)-1
    if x<1 or M[x][1]==0 or M[x][2]!=0:return
    C=Ctx(M)
    if not C.ok:return
    r=C.e.par(1,x)
    if r is None or C.e.par(0,x)!=r:return
    D=dependencies(C,x);C1=Ctx(M[:x])
    A=C.o(r);mu,br,_=A;seed=C1.o(r)
    def note(f,b,key):
        cnt[f+('.ok' if b else '.FAIL')]+=1
        if not b and (f not in ex or key[0]<ex[f][0]):ex[f]=key
    etas=[gamS(mu,br,seed,k) for k in range(5)]
    for n in (2,3):
        N=[tuple(c) for c in trio.expand([list(c) for c in M],n)];CN=Ctx(N)
        if not CN.ok:continue
        for i in range(x):
            if not((False,i) in D and M[i][1] and M[i][2]):continue
            for j in [j for j in C.ch(i) if M[j]==C.e.bump(i)]:
                if not C.ch(j):continue
                G_=sumN([C.o(e) for e in C.ch(j)]);GN=sumN([CN.o(e) for e in C.ch(j)])
                S=sumN([ONE]+[C.bumpTerm(i,jj) for jj in C.ch(i)]);SN=sumN([ONE]+[CN.bumpTerm(i,jj) for jj in C.ch(i)])
                for lay,(Y,YN) in (('1',(G_,GN)),('2',(S,SN))):
                    if Y==YN or lt(Y,E0) or lt(YN,E0) or Y[2]!=Z:continue
                    key=(len(M),ms(M),n,i,lay)
                    cnt['layers']+=1
                    note('YNsingle',YN[2]==Z,key)
                    a,b,_=Y
                    node=b!=Z and O.summ(b)[-1]==(succ(a),Z,Z)
                    if node:cnt['node']+=1;continue
                    for eta in etas:
                        g=G(eta)
                        if not g.sumG(Z,Y,YN,True):continue
                        cnt['layer.eta']+=1
                        if YN[2]==Z and YN[0]==a and b!=Z:
                            bN=YN[1]
                            ar=g.sumG(Z,b,bN,True);note('Arg',ar,key)
                            if ar:
                                note('LoNot1',O.summ(b)[-1]!=ONE1,key)
                                th=(succ(a),Z,Z)
                                if split(b,th)[1]==Z:
                                    for B_,l_,lN,_ in g.splits(b,bN):
                                        if not g.oneG(Z,l_,lN,True):continue
                                        note('LoG',lN[2]==Z and g.oneG(th,l_,lN),key)
                        if YN==fsD(Y,eta):
                            oY=YE.omega(Y);f=fsD(oY,eta)
                            note('HB',f==YE.omega(fsD(Y,eta)) and lt(f,oY),key)
def work(batch):
    cnt=collections.Counter();ex={}
    for mm in batch:
        M=[tuple(c) for c in mm]
        try:check(M,cnt,ex);cnt['mats']+=1
        except Exception as e:
            cnt['exc.'+type(e).__name__]+=1
            if 'exc' not in ex:ex['exc']=(len(M),ms(M),repr(e)[:200])
    return cnt,ex
if __name__=='__main__':
    from multiprocessing import Pool
    out=open(sys.argv[1],'a');npr=int(os.environ.get('NPR','3'))
    for f in sys.argv[2:]:
        t=time.time();mats=pickle.load(open(f,'rb'))
        CAP=int(os.environ.get('CAP','0'))
        if CAP and len(mats)>CAP:random.seed(1);mats=random.sample(list(mats),CAP)
        cnt=collections.Counter();ex={}
        with Pool(npr) as pool:
            for c,e in pool.imap_unordered(work,(mats[i:i+50] for i in range(0,len(mats),50))):
                cnt.update(c)
                for k,v in e.items():
                    if k not in ex or v[0]<ex[k][0]:ex[k]=v
        out.write(json.dumps({'set':os.path.basename(f),'n':len(mats),'sec':round(time.time()-t),'cnt':dict(sorted(cnt.items())),'ex':ex},default=str)+'\n');out.flush()
