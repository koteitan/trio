"""WfQrH: M-side facts of qr_chainF (WfQrH1) on q = r last-column frames.
 OX  : o(x) = psi(a+1, 0, 0)  (hOx)
 RX  : o(r) <= o(x)           (hrx)
 S1  : seed = o_{M.take x}(r) < o(x) and seed != 0  (hr1, hr1z)
 V1  : v_{M.take x}(r) <= v(r)  (hv1 of WfQrH7.qr_chainH3)
 CHn : (n = 2, 3 if EXP) true o_{M[n]}(x) == o_{M[n-1]}(r) (sanity of the copy), o_{M[n]}(r) < o(r)
usage: nice -n 15 python3 mside.py NPROC EXP OUT.jsonl PKL..."""
import sys,os,pickle,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import trio
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx, Z, isSucc, lt
def ms(M):return ''.join('(%d,%d,%d)'%tuple(c) for c in M)
EXP=0
def check(M,cnt,ex):
    def note(f,ok):
        cnt[f+'.ok' if ok else f+'.FAIL']+=1
        if not ok and (f not in ex or len(M)<ex[f][0]):ex[f]=(len(M),ms(M))
    if not M<SRO:cnt['outside_SRO']+=1;return
    x=len(M)-1
    if x<1 or M[x][1]==0 or M[x][2]!=0:return
    C=Ctx(M)
    if not C.ok:cnt['evalfail']+=1;return
    r=C.e.par(1,x)
    if r is None or C.e.par(0,x)!=r:return
    cnt['frames']+=1
    ox=C.o(x);orr=C.o(r)
    note('OX',ox[1]==Z and ox[2]==Z and ox[0]!=Z and isSucc(ox[0]))
    note('RX',orr==ox or lt(orr,ox))
    T=Ctx(M[:x])
    if not T.ok:cnt['evalfail1']+=1;return
    sd=T.o(r)
    note('S1',sd!=Z and lt(sd,ox))
    note('V1',T.v(r)==C.v(r) or lt(T.v(r),C.v(r)))
    if EXP:
        prev=T
        for n in (2,3):
            N=[tuple(c) for c in trio.expand([list(c) for c in M],n)];CN=Ctx(N)
            if not CN.ok:cnt['Nevalfail']+=1;break
            note('CHcopy',CN.o(x)==prev.o(r))
            note('CHdrop',lt(CN.o(r),orr) and CN.o(r)!=Z)
            prev=CN
def work(batch):
    cnt=collections.Counter();ex={}
    for mm in batch:
        M=[tuple(c) for c in mm]
        try:check(M,cnt,ex);cnt['mats']+=1
        except Exception as e:
            cnt['exc.'+type(e).__name__]+=1;ex.setdefault('exc',(len(M),ms(M),repr(e)[:200]))
    return cnt,ex
if __name__=='__main__':
    npr=int(sys.argv[1]);EXP=int(sys.argv[2]);out=open(sys.argv[3],'a')
    for f in sys.argv[4:]:
        t=time.time();mats=pickle.load(open(f,'rb'))
        cnt=collections.Counter();ex={}
        with Pool(npr,initializer=globals().__setitem__,initargs=('EXP',EXP)) as pool:
            for c,e in pool.imap_unordered(work,(mats[i:i+200] for i in range(0,len(mats),200))):
                cnt.update(c)
                for k,v in e.items():
                    if k not in ex or v[0]<ex[k][0]:ex[k]=v
        out.write(json.dumps({'set':os.path.basename(f),'n':len(mats),'sec':round(time.time()-t),'cnt':dict(sorted(cnt.items())),'ex':ex},default=str)+'\n');out.flush()
