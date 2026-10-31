"""WfQnH measurements (t = 1, q != r frames, zeta = gamS(n-2), n = 2,3[,4]).
B_zeta = Lean WfBad.BadSet (i < x, DepX false i, bad shape, e1,e2 != 0, bumpW = o(r), some q in summands v(P1 i)
         with q < W and not q < W[zeta]);  DB = DepXB closure of B_zeta.
TZ.fail / TZ.inDB : TPLoS comparison failing at zeta at an o-call c of D  =>  (true,c) in DB      (claim 1)
TZ.chInDB         : ... and every parent i with c a counted child, i in D, has (true,i) in DB (automatic)
NEST.*            : bad call i whose last bump grandchild k has (true,k) in DB (nested), and what holds there
E3.ge/E3.lt       : at every (b,i) in DB: fsD(old,zeta) <= true, true < old                         (claim 2)
E3.single         : at every (true,i) in DB: true o value is a single term                          (Single)
E3.rootsingle     : at roots of M in DB
VP.inDB           : bad call i with (false, P1 i) in DB
usage: nice -n 15 python3 meas.py IN.pkl OUT.json NPROC [SAMPLE] [NS]"""
import sys,pickle,json,collections,random
sys.path.insert(0,'/home/koteitan/proofs/trio/tmp/wf/WfQnE')
sys.path.insert(0,'/home/koteitan/proofs/trio/tools')
import analyze as A
from probe_inv3_prefix import Ctx, Z, fsD, holelev, lt, le, summ, ohole, split, succ, last, isSucc
from probe_inv2 import dependencies
import ytosk_eval as YV
import trio
NS=(2,3)
def ms(M):return ''.join('(%d,%d,%d)'%tuple(c) for c in M)
def single(t): return t!=Z and t[2]==Z
def meas(M):
    c=collections.Counter();e={}
    try:
        M=list(M)
        f=A.frame(M)
        if f is None: return c,e
        C,x,r=f
        T=Ctx(M[:x])
        if not T.ok: return c,e
        seed=T.o(r); mu,b,_=C.o(r); A_=C.o(r)
        D=dependencies(C,x)
        c['frames']+=1
        cand=[i for i in range(x) if (False,i) in D and C.e12(i) and A.bad_shape(C,i) and C.bumpW(i)==A_]
        tcases=[]
        for cc in range(x):
            if (True,cc) not in D: continue
            o=C.o(cc)
            if o==Z: continue
            s,y,_=o; l=last(y)
            if (l and l[1]==Z and not isSucc(l[0]) and ohole(l[0]) and holelev(y)==mu and split(y,(succ(s),Z,Z))[1]==Z):
                tcases.append((cc,s,l[0]))
        if not cand and not any(lt((fsD(a,seed),Z,Z),(succ(s),Z,Z)) for (cc,s,a) in tcases):
            return c,e
        c['frames.hit']+=1
        roots=[i for i in range(x) if C.e.par(0,i) is None]
        for n in NS:
            zeta=A.gamS(mu,b,seed,n-2)
            Az=fsD(A_,zeta)
            B=[i for i in cand if any(lt(q,A_) and not lt(q,Az) for q in summ(C.vOpt1(i)))]
            DB=A.closure(C,{(False,i) for i in B},x)
            c['B']+=len(B)
            for (cc,s,a) in tcases:
                if lt((fsD(a,zeta),Z,Z),(succ(s),Z,Z)):
                    c['TZ.fail']+=1
                    ok=(True,cc) in DB
                    c['TZ.inDB' if ok else 'TZ.outDB']+=1
                    if not ok: e.setdefault('TZout',(M,n,cc))
            for i in B:
                p=C.e.par(1,i)
                if p is not None and (False,p) in DB: c['VP.inDB']+=1; e.setdefault('VPin',(M,n,i))
                js=[j for j in C.ch(i) if C.M[j]==C.e.bump(i)]
                ks=[k for j in js for k in C.ch(j) if (True,k) in D]
                if any((True,k) in DB for k in ks):
                    c['NEST']+=1; e.setdefault('NEST',(M,n,i))
                else: c['NEST.no']+=1
            if not DB: continue
            E=[tuple(cl) for cl in trio.expand([list(cl) for cl in M],n)]
            CE=Ctx(E)
            if not CE.ok: c['exp_fail']+=1; continue
            for i in B:
                js=[j for j in C.ch(i) if C.M[j]==C.e.bump(i)]
                ks=[k for j in js for k in C.ch(j) if (True,k) in D]
                nest=any((True,k) in DB for k in ks)
                tv=CE.v(i); V=C.vOpt1(i)
                fv=YV.sf(YV.add(V,Az))
                tag='NEST.' if nest else 'LEAF.'
                c[tag+('eqform' if tv==fv else 'neform')]+=1
                if tv!=fv: e.setdefault(tag+'ne',(M,n,i))
                c[tag+('ltA' if lt(tv,A_) else 'geA')]+=1
                c[tag+('geAz' if le(fsD(C.v(i),zeta),tv) else 'ltAz')]+=1
            for (bb,i) in DB:
                old=C.o(i) if bb else C.v(i)
                tru=CE.o(i) if bb else CE.v(i)
                c['E3.ge' if le(fsD(old,zeta),tru) else 'E3.geFAIL']+=1
                c['E3.lt' if lt(tru,old) else 'E3.ltFAIL']+=1
                if not le(fsD(old,zeta),tru): e.setdefault('E3ge',(M,n,i,bb))
                if not lt(tru,old): e.setdefault('E3lt',(M,n,i,bb))
                if bb:
                    c['E3.single' if single(tru) else 'E3.notsingle']+=1
                    if i in roots: c['E3.rootsingle' if single(tru) else 'E3.rootNOTsingle']+=1
    except Exception as ex:
        c['exception']+=1;e['exc']=(M,repr(ex))
    return c,e
if __name__=='__main__':
    from multiprocessing import Pool
    inp,out,npr=sys.argv[1],sys.argv[2],int(sys.argv[3])
    S=pickle.load(open(inp,'rb'))
    if isinstance(S,dict): S=S['mats'] if 'mats' in S else list(S.values())
    S=[tuple(tuple(cl) for cl in M) for M in S]
    S=[M for M in S if len(M)>=3 and M[-1][2]==0]
    if len(sys.argv)>4 and int(sys.argv[4])>0:
        random.seed(5);random.shuffle(S);S=S[:int(sys.argv[4])]
    tot=collections.Counter();ex={}
    with Pool(npr) as p:
        for cn,e in p.imap_unordered(meas,S,chunksize=50):
            tot.update(cn)
            for k,v in e.items(): ex.setdefault(k,v)
    res={'n':len(S),'cnt':dict(sorted(tot.items())),'ex':{k:ms(v[0])+' '+str(v[1:]) for k,v in ex.items()}}
    json.dump(res,open(out,'w'),indent=1);print(inp,json.dumps(res['cnt']),flush=True)
