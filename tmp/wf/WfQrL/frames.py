"""WfQrL: measure the frame hypotheses of qr_engineDQ (WfQrL10) on the true values of N = M[n] (n = 2..NMAX).
For each D call of a q = r frame (t = 1: P1 x = P0 x = r, row 2 of x = 0):
  o, last counted child c in D (OShape case 2): hTrig (same trigger in M and N; trigger case: same s, DQ y -> yN,
     no low part in y, yN), hPre (isOT pre), frame equation sanity;
  v upgrade (k = U i): hUpgL (last v(k), last vN(k) single; DQ false lasts at eta = Zf k);
  v bump: hBW (bumpW, bumpW_N single; DQ false at eta in {Zf i, Zf k});
  hSo / hSv: N values on D standard, o values single.
usage: nice -n 15 python3 frames.py NPROC NMAX OUT.jsonl PKL..."""
import sys,os,pickle,json,collections,time
from multiprocessing import Pool
sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQrL')
import trio
from probe_inv3_prefix import Z, lt, isOT, split, succ, last, spa
from probe_adn import gamS, dependencies, lift_counts, Ctx, ms
from compq import dq, dq1
from probe_inv3_prefix import ONE, fsD, sumN
import ytosk_eval as YE
E0=(Z,(ONE,Z,Z),Z)
def lo_(b,a):return split(b,(succ(a),Z,Z))
def omside(eta,Y,YN):
    r={}
    if lt(Y,E0)!=lt(YN,E0):
        return {'cross.E0toSmall':(Y==E0 and lt(YN,E0))}
    r['ot']=isOT(Y) and isOT(YN)
    r['e0']=lt(Y,E0)==lt(YN,E0)
    r['q0']=not(Y and not Y[2]) or (YN and not YN[2])
    ok=True
    if Y and YN and not Y[2] and not YN[2] and Y[0]==YN[0] and Y[1]:
        a=Y[0];h,l=lo_(Y[1],a);hN,lN=lo_(YN[1],a)
        ok=(lN==Z) if l==Z else (hN==h and lN!=Z)
        if not ok and l==Z and last(Y[1])==(succ(a),Z,Z) and hN==init_(Y[1]) and lt(YN,(succ(a),Z,Z)):
            return {'node':True}
    r['lo']=ok
    r['B']=(YN!=fsD(Y,eta)) or (fsD(YE.omega(Y),eta)==YE.omega(YN) and lt(fsD(YE.omega(Y),eta),YE.omega(Y)))
    return r
NMAX=3
def init_(t):
    if not t or not t[2]:return Z
    return (t[0],t[1],init_(t[2]))
def summ_(t):
    r=[]
    while t:r.append((t[0],t[1],Z));t=t[2]
    return r
def single(t):return bool(t) and not t[2]
def lo0(y,s):return split(y,(succ(s),Z,Z))[1]==Z
def bad(cnt,ex,name,key):
    cnt[name+'.FAIL']+=1
    if name not in ex or key[0]<ex[name][0]:ex[name]=key
def check(M,cnt,ex):
    C=Ctx(M)
    if not C.ok:return
    x=len(M)-1;r=C.e.par(1,x)
    if r is None or C.e.par(0,x)!=r or M[x][2]!=0:return
    T=Ctx(M[:x]);A=C.o(r);mu,br,_=A;seed=T.o(r);D=dependencies(C,x);d=lift_counts(C,x,A)
    cnt['frames']+=1
    for n in range(2,NMAX+1):
        m=n-2
        N=[tuple(c) for c in trio.expand([list(c) for c in M],n)];CN=Ctx(N)
        if not CN.ok:cnt['Nevalfail']+=1;continue
        Zf=lambda i:gamS(mu,br,seed,m+d[i])
        for i in range(x):
            key=(len(M),ms(M),n,i)
            if (True,i) in D:
                oN=CN.o(i)
                if not (single(oN) and isOT(oN)):bad(cnt,ex,'hSo',key)
                else:cnt['hSo.ok']+=1
                CLi=C.CL(i)
                if (False,i) not in D and CLi and (True,CLi[-1]) in D:
                    c=CLi[-1];L=C.ch(i)[:C.ch(i).index(c)]
                    pre=C.pre(i,L);v=C.v(i)
                    if not isOT(pre):bad(cnt,ex,'hPre',key)
                    else:cnt['hPre.ok']+=1
                    s,y,_=C.o(c);oc=CN.o(c) if c<len(N) else None
                    if oN!=(v,spa(v,oc) if False else oN[1],Z):pass
                    trM=lt(pre,y) and lt((v,Z,Z),(s,y,Z))
                    s2,y2,_=oc
                    trN=lt(pre,y2) and lt((v,Z,Z),(s2,y2,Z))
                    isdq=dq1(C.o(i),oN,Zf(i),1) is not None or any(dq1(C.o(i),oN,e,1) is not None for e in (oc,))
                    if not trM and not trN:cnt['hTrig.add']+=1
                    elif trM and trN and s2==s and lo0(y,s) and lo0(y2,s) and dq(y,y2,Zf(c)) is not None:cnt['hTrig.trig']+=1
                    elif trM and trN and s2==s and lo0(y,s) and not lo0(y2,s) and y and last(y)==(succ(s),Z,Z) and split(y2,(succ(s),Z,Z))[0]==init_(y) and lt((s,y2,Z),(succ(s),Z,Z)):cnt['hTrig.node']+=1
                    elif trM and trN and s2==s and not lo0(y,s) and not lo0(y2,s) and split(y2,(succ(s),Z,Z))[0]==split(y,(succ(s),Z,Z))[0] and dq(y,y2,Zf(c)) is not None:cnt['hTrig.triglo']+=1
                    elif c==x:
                        cnt['hTrig.leafpar.%s%s.%s'%('M' if trM else '-','N' if trN else '-','DQ' if isdq else 'noDQ')]+=1
                        okL=False
                        ox=C.o(c)
                        if y==Z and ox[0] and YE.isSucc(ox[0]) if hasattr(YE,'isSucc') else False:pass
                        from probe_inv3_prefix import isSucc as isS
                        if y==Z and ox[0] and isS(ox[0]) and trN and not lo0(y2,s2) and lt(oc,ox):
                            ad=summ_(YE.add(pre,ox));Bl=ad[:-1]
                            hi_=summ_(split(y2,(succ(s2),Z,Z))[0])
                            if ad[-1]==(ox[0],ox[1],Z) and hi_[:len(Bl)]==Bl:
                                Ql=hi_[len(Bl):]
                                okL=all(not lt(q,(s2,y2,Z)) and lt(q,ox) for q in Ql)
                        if okL:cnt['hTrig.leafpar.lemma.ok']+=1
                        else:bad(cnt,ex,'hTrig.leafpar.lemma',key)
                        if not isdq:bad(cnt,ex,'hTrig.leafpar.noDQ',key)
                    else:
                        bad(cnt,ex,'hTrig.%s%s.%s'%('M' if trM else '-','N' if trN else '-','DQ' if isdq else 'noDQ'),key)
            if (False,i) in D and M[i][1]:
                vN=CN.v(i)
                if not isOT(vN):bad(cnt,ex,'hSv',key)
                else:cnt['hSv.ok']+=1
                if M[i][2]==0:
                    k=C.upg(i)
                    if k is None:cnt['upg.none']+=1;continue
                    l=last(C.v(k));lN=last(CN.v(k))
                    if not(single(l) and single(lN)):bad(cnt,ex,'hUpgL.single',key);continue
                    if dq1(l,lN,Zf(k),1) is None:bad(cnt,ex,'hUpgL.dq',key)
                    else:cnt['hUpgL.ok']+=1
                else:
                    W=C.bumpW(i);WN=CN.bumpW(i)
                    if not(single(W) and single(WN)):bad(cnt,ex,'hBW.single',key);continue
                    js=[j for j in C.ch(i) if M[j]==C.e.bump(i)]
                    ks=[C.ch(j)[-1] for j in js if C.ch(j)]
                    etas=[Zf(i)]+[Zf(k) for k in ks]
                    for j in js:
                        if not C.ch(j):continue
                        k=C.ch(j)[-1]
                        G=sumN([C.o(e) for e in C.ch(j)]);GN=sumN([CN.o(e) for e in C.ch(j)])
                        S=sumN([ONE]+[C.bumpTerm(i,jj) for jj in C.ch(i)]);SN=sumN([ONE]+[CN.bumpTerm(i,jj) for jj in C.ch(i)])
                        for lay,(Y_,YN_) in (('1',(G,GN)),('2',(S,SN))):
                            if Y_==YN_:cnt['om%s.same'%lay]+=1;continue
                            for nm,v in omside(Zf(k),Y_,YN_).items():
                                if v:cnt['om%s.%s.ok'%(lay,nm)]+=1
                                else:bad(cnt,ex,'om%s.%s'%(lay,nm),key)
                    if W==WN:cnt['hBW.same']+=1
                    elif any(dq1(W,WN,e,1) is not None for e in etas):cnt['hBW.ok']+=1
                    else:bad(cnt,ex,'hBW.dq',key)
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
    npr=int(sys.argv[1]);NMAX=int(sys.argv[2]);out=open(sys.argv[3],'a')
    for f in sys.argv[4:]:
        t=time.time();mats=pickle.load(open(f,'rb'))
        cnt=collections.Counter();ex={}
        with Pool(npr,initializer=globals().__setitem__,initargs=('NMAX',NMAX)) as pool:
            for c,e in pool.imap_unordered(work,(mats[i:i+100] for i in range(0,len(mats),100))):
                cnt.update(c)
                for k,v in e.items():
                    if k not in ex or v[0]<ex[k][0]:ex[k]=v
        out.write(json.dumps({'set':os.path.basename(f),'n':len(mats),'sec':round(time.time()-t),'cnt':dict(sorted(cnt.items())),'ex':ex},default=str)+'\n');out.flush()
