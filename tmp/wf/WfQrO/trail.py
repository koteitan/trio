"""WfQrO: the trail of pre < y along the DQ path y -> yN (Bachmann-type lower bound).
trail_sum(p, t, tN): p < t (sums), t = B ++ l, tN = B ++ Q ++ lN.
  p <= B                       -> 'offB'   (p < tN since Q ++ lN != 0)
  p = B ++ p', head p' = h < l -> trail_one(h, l, lN)   (sufficient: h < lN)
trail_one(h, l, lN): single h < l.
  base (lN = fsD(l, eta))      -> ('base', h, l)   needs h < lN
  sub  (l = Om_s, lN = Om_sN)  -> h = psi_a(b), a < s -> trail_sum(a, s, sN)
  arg  (l = psi_s(y), lN = psi_s(yN)): a < s -> 'offSub'; a = s, b < y -> trail_sum(b, y, yN)
usage: nice -n 15 python3 trail.py OUT.jsonl PKL...   (CAP env as oframe)"""
import sys,os,pickle,json,collections,time,random
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQrH');sys.path.insert(0,'/home/koteitan/proofs/trio/tools');sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfInvA')
import oframe as O, trio
from probe_adn import Ctx, dependencies, gamS, lift_counts, ms
from probe_inv3_prefix import Z, lt, split, succ, isSucc, fsD
from ytosk_eval import tstr
def le(a,b):return a==b or lt(a,b)
def sub_terms(t,acc):
    while t:
        acc.add((t[0],t[1],Z));sub_terms(t[0],acc);sub_terms(t[1],acc);t=t[2]
    return acc
def trail_sum(p,t,tN,eta,dep=0):
    assert lt(p,t)
    sy=O.summ(t);sN=O.summ(tN);B=sy[:-1];l=sy[-1]
    assert sN[:len(B)]==B
    lN=sN[-1] if len(sN)>len(B) else Z
    sp=O.summ(p)
    if le(p,O.mk(B)):return ('offB',dep)
    assert sp[:len(B)]==B,'prefix'
    h=sp[len(B)]
    assert lt(h,l)
    r=trail_one(h,l,lN,eta,dep+1)
    if r[0]=='fail' and lt(p[len(B)] if False else O.mk(sp[len(B):]),O.mk(sN[len(B):])):
        return ('failQ',)+r[1:]  # sufficient condition too strong, but p < tN holds
    return r
def trail_one(h,l,lN,eta,dep):
    if lN==Z:return ('fail','lN0',dep)
    s,y,_=l;s2,y2,_=lN;a,b,_=h
    if s==s2 and y!=Z and y2!=y:
        if lt(a,s):return ('offSub',dep)
        try:return trail_sum(b,y,y2,eta,dep)
        except AssertionError:pass
    if y==Z and y2==Z and s!=s2:
        try:return trail_sum(a,s,s2,eta,dep)
        except AssertionError:pass
    assert fsD(l,eta)==lN,'notbase'
    kind='succ' if (y==Z) else 'big'
    return ('base',dep,h,l,kind) if lt(h,lN) else ('fail','base.'+kind,dep,h,l)
def check(M,cnt,ex,n_list=(2,3)):
    x=len(M)-1
    if x<1 or M[x][1]==0 or M[x][2]!=0:return
    C=Ctx(M)
    if not C.ok:return
    r=C.e.par(1,x)
    if r is None or C.e.par(0,x)!=r:return
    D=dependencies(C,x)
    A=C.o(r);mu,br,_=A;seed=Ctx(M[:x]).o(r);dl=lift_counts(C,x,A)
    for n in n_list:
        N=[tuple(c) for c in trio.expand([list(c) for c in M],n)];CN=Ctx(N)
        if not CN.ok:continue
        for i in range(x):
            if (True,i) not in D or (False,i) in D:continue
            CLi=C.CL(i)
            if not CLi or (True,CLi[-1]) not in D:continue
            c=CLi[-1];L=C.ch(i)[:C.ch(i).index(c)]
            pre=C.pre(i,L);v=C.v(i);oc=C.o(c);oN=CN.o(c)
            if oN==oc:continue
            s,y,_=oc;s2,y2,_=oN
            if not(s2==s and y2!=y and y!=Z):continue
            if not O.trig(v,pre,s,y):continue
            eta=gamS(mu,br,seed,n-2+dl[c])
            key=(len(M),ms(M),n,i,c)
            cnt['trigArg']+=1
            try:res=trail_sum(pre,y,y2,eta)
            except AssertionError as e:
                cnt['assert.'+str(e)]+=1;ex.setdefault('assert.'+str(e),key);continue
            tag=res[0]
            if tag=='base':tag='base.ok'
            cnt[tag]+=1
            if tag in('fail','failQ'):
                k=tag+'.'+res[1]
                if k not in ex or key[0]<ex[k][0]:ex[k]=key
            if res[0]=='base':
                h,l=res[2],res[3]
                if os.environ.get('SHOW') and cnt['shown']<int(os.environ['SHOW']):
                    cnt['shown']+=1;print(key[1],n,i,c,'\n pre',tstr(pre),'\n y',tstr(y),'\n yN',tstr(y2),'\n eta',tstr(eta),'\n h',tstr(h),'\n l',tstr(l),'\n lN',tstr(fsD(l,eta)),'dep',res[1])
                cnt['base.'+res[4]+('.h<eta' if lt(h,eta) else '.h>=eta')]+=1
                if not lt(h,eta):
                    if 'base.h>=eta' not in ex or key[0]<ex['base.h>=eta'][0]:ex['base.h>=eta']=key
            # SubOK: no single subterm of pre in the base gap [fsD(lb), lb)
            lb=base_node(oc,oN,eta)
            if lb is not None:
                lbN=fsD(lb,eta);bad=[g for g in sub_terms(pre,set()) if le(lbN,g) and lt(g,lb)]
                cnt['SubOK.ok' if not bad else 'SubOK.FAIL']+=1
                if bad and ('SubOK' not in ex or key[0]<ex['SubOK'][0]):ex['SubOK']=key
def base_node(t,tN,eta,k=False):
    if t==tN:return None
    if k:
        sy=O.summ(t);sN=O.summ(tN);B=sy[:-1];lN=sN[-1] if len(sN)>len(B) else Z
        return base_node(sy[-1],lN,eta)
    if tN==Z:return t
    s,y,_=t;s2,y2,_=tN
    if s==s2 and y!=Z and y2!=y:return base_node(y,y2,eta,True)
    if y==Z and y2==Z and s!=s2 and fsD(t,eta)!=tN:return base_node(s,s2,eta,True)
    return t
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
