"""WfQnA measurements (WfQnH meas.py + restricted engine residuals ABS.cl/ABS.leaf/VSN.cl/HARD.pre)
WfQnH measurements (t = 1, q != r frames, zeta = gamS(n-2), n = 2,3[,4]).
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
from probe_inv3_prefix import Ctx, Z, ONE, comps, spa, sumN, W2, fsD, holelev, lt, le, summ, ohole, split, succ, last, isSucc
from probe_inv2 import dependencies
import ytosk_eval as YV
import trio
import lhd_exact as LX
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
            for i in B:
                c['B.Vlt' if lt(C.vOpt1(i),A_) else 'B.VgeA']+=1
                if C.v(i)!=A_: c['B.vneA']+=1; e.setdefault('vneA',(M,n,i))
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
                c['B.gtr' if i>r else 'B.ltr']+=1
                kall=[k for j in js for k in C.ch(j)]
                c['B.kr' if (js and C.ch(js[-1]) and C.ch(js[-1])[-1]==r) else 'B.knotr']+=1
                if not (js and C.ch(js[-1]) and C.ch(js[-1])[-1]==r): e.setdefault('Bknotr',(M,n,i))
                if any((True,k) in DB for k in ks):
                    c['NEST']+=1; e.setdefault('NEST',(M,n,i))
                else: c['NEST.no']+=1
            if not DB: continue
            c['R.inDB' if (True,r) in DB else 'R.outDB']+=1
            if (True,r) in DB: e.setdefault('RinDB',(M,n))
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
            for (bb,i) in D:
                if i>=x: continue
                old=C.o(i) if bb else C.v(i)
                tru=CE.o(i) if bb else CE.v(i)
                if (bb,i) in DB:
                    ok=LX.lhd(tru,old); c['LZ.cl.ok' if ok else 'LZ.cl.FAIL']+=1
                    if not ok: e.setdefault('LZcl',(M,n,i,bb))
                else:
                    g=fsD(old,zeta)
                    ok=LX.lhd(g,old); c['LZ.glue.ok' if ok else 'LZ.glue.FAIL']+=1
                    if not ok: e.setdefault('LZglue',(M,n,i,bb))

            # restricted engine residuals at closure calls
            for (bb,i) in DB:
                if bb or i>=x or not C.e12(i): continue
                W=C.bumpW(i)
                for q in summ(C.vOpt1(i)):
                    if not lt(q,W2) and lt(q,W):
                        ok=LX.lhd(q,W); c['ABS.cl.ok' if ok else 'ABS.cl.FAIL']+=1
                        if not ok: e.setdefault('ABScl',(M,n,i))
                        if i not in B and not lt(q,CE.bumpW(i)):
                            ok=LX.lhd(q,W); c['ABSW.cl.ok' if ok else 'ABSW.cl.FAIL']+=1
                            if not ok: e.setdefault('ABSWcl',(M,n,i))
            for i in B:
                for q in summ(C.vOpt1(i)):
                    if lt(q,A_) and not lt(q,Az):
                        ok=LX.lhd(q,A_); c['ABS.leaf.ok' if ok else 'ABS.leaf.FAIL']+=1
                        if not ok: e.setdefault('ABSleaf',(M,n,i))
            for (bb,i) in DB:
                if not bb or i>=x or (False,i) in DB: continue
                cl=CE.CL(i)
                if not cl: c['VSN.nocl']+=1; continue
                Lc,cc=cl[:-1],cl[-1]
                if CE.v(cc)==C.v(cc): c['VSN.same']+=1
                else:
                    B0=spa(C.v(i),sumN([C.o(d) for d in Lc]))
                    ok=all(le(g,(CE.v(cc),Z,Z)) or le(g,B0) for g in comps(C.v(i),CE.v(cc)))
                    c['VSN.ok' if ok else 'VSN.FAIL']+=1
                    if not ok: e.setdefault('VSN',(M,n,i))
                ro,so=C.o(cc),CE.o(cc)
                if ro and so and ro[2]==Z and so[2]==Z and ro[0]==so[0] and ro!=so and lt(C.v(i),ro[0]):
                    c['HARD.pre']+=1
                    sS,y,_=ro; _,y2,_=so; vi=C.v(i)
                    B0=spa(vi,sumN([C.o(d) for d in Lc]))
                    th=(succ(sS),Z,Z)
                    if (lt(B0,y2) and lt((vi,Z,Z),(sS,y2,Z)) and lt(B0,y) and lt((vi,Z,Z),(sS,y,Z))
                        and lt(split(y2,th)[0],split(y,th)[0])):
                        Hv=YV.add(YV.cut(YV.add(sS,ONE),y2),YV.sub((sS,y2,Z),(sS,YV.cut(YV.add(sS,ONE),y2),Z)))
                        ok=all(le(g,Hv) for g in comps(vi,y2))
                        c['HARD.ok' if ok else 'HARD.FAIL']+=1
                        if not ok: e.setdefault('HARD',(M,n,i))
            for i in B:
                g=YV.sf(YV.add(C.vOpt1(i),Az))
                ok=LX.lhd(g,A_); c['LZ.leaf.ok' if ok else 'LZ.leaf.FAIL']+=1
                if not ok: e.setdefault('LZleaf',(M,n,i))
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
