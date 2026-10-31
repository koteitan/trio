"""qn seed path clause (third conjunct of WfScout.T2SeedQNBaseR) and candidate weakenings.
For each t2 qn source (q != r, q last counted child of r), path level u <= V (paths_all, = PathLvAll), records:
 t1.lt  : g in comps u t1, g < X1 (old)
 S.lt   : g in comps u S, g < X1 (old; refuted)
 S.cand : g in comps u S, g < B+Omega_S or exists d in comps u B ++ comps u V, g <= d   (candidate W1)
 S.le   : g in comps u S, g <= B+Omega_S or exists d in comps u B ++ comps u V, g <= d  (candidate W1')
 S.BV   : g in comps u S, exists d in comps u B ++ comps u V, g <= d
 S.OS   : g in comps u S, g < B+Omega_S
 cons.QNCl k=1..4: T2SeedQNCl (consumer), comps u t_k: g < B+Omega_{t_k} or <= comp of B/V
 cons.Dom0 (Lc=[]): u in LevAt (u=V or path), g in comps u S: g <= Omega_S or <= comp of V
 cons.QNClV : same as QNCl but also includes comps u S (the qn_closed_tqN invariant at k>=1)
"""
import sys,os,pickle,json,collections,traceback
sys.path[:0]=['/home/koteitan/proofs/trio/tmp/codex','/home/koteitan/proofs/trio/tools','/home/koteitan/proofs/trio/tmp/t0/probes','/home/koteitan/proofs/trio/tmp/t2/probes','/home/koteitan/proofs/trio/tmp/lead/probes']
from multiprocessing import Pool
def go(mm):
    import residual_extension_local_trio_codex as A
    from clshl_real_copy_trio_codex import Y,Z,ONE,comp,le,succ,summ,shf
    from fdcopy_offpath_audit_trio_codex import paths_all
    from probe_inv3_prefix import sumN
    M=[tuple(c) for c in mm]
    out=collections.Counter();ex={}
    def note(f,ok,**info):
        out[f+'.cases']+=1
        if not ok:
            out[f+'.fail']+=1
            if f not in ex: ex[f]={'M':''.join('(%d,%d,%d)'%c for c in M),'n':len(M),**info}
    if len(M)<2 or not M[-1][2]: return out,ex
    try:
        C=A.ctx(M);x=len(M)-1
        if not C.ok: return out,ex
        r=C.e.par(2,x);q=C.e.par(0,x)
        if r is None or q is None or q==r: return out,ex
        cl=C.CL(r)
        if not cl or cl[-1]!=q: return out,ex
        T=A.ctx(M[:-1])
        if not T.ok: return out,ex
        out['qn.sources']+=1
        V=C.v(r);X1=T.pre(r,T.CL(r));B=C.pre(r,cl[:-1]);sb=summ(B);sx=summ(X1)
        if not(len(sx)==len(sb)+1 and sx[:len(sb)]==sb and not sx[-1][1]): out['qn.noform']+=1;return out,ex
        t1=sx[-1][0]
        S=Y.add(V,Y.omega(sumN([ONE]+[C.bumpTerm(q,d) for d in C.ch(q) if d<x])))
        def app(Bt,Om):  # B + Omega_t
            return Y.add(Bt,Om) if Bt else Om
        OS=app(B,(S,Z,Z))
        paths=paths_all(C)
        tk=[t1]
        for k in range(1,5): tk.append(shf(V,S,tk[-1]))
        def bv(u,g): return any(le(g,d) for d in comp(u,B)+comp(u,V))
        for u in paths[r]:
            if not le(u,V): continue
            for g in comp(u,t1): note('t1.lt',Y.lt(g,X1),u=Y.tstr(u),g=Y.tstr(g))
            for g in comp(u,S):
                info=dict(u=Y.tstr(u),g=Y.tstr(g),S=Y.tstr(S),X1=Y.tstr(X1),B=Y.tstr(B))
                note('S.lt',Y.lt(g,X1),**info)
                note('S.BV',bv(u,g),**info)
                note('S.OS',Y.lt(g,OS),**info)
                note('S.cand',Y.lt(g,OS) or bv(u,g),**info)
                note('S.le',le(g,OS) or bv(u,g),**info)
                note('S.ltX1orBV',Y.lt(g,X1) or bv(u,g),**info)
            for k in range(1,5):
                Xk=app(B,(tk[k],Z,Z))
                for g in comp(u,tk[k]): note('cons.QNCl',Y.lt(g,Xk) or bv(u,g),k=k,u=Y.tstr(u),g=Y.tstr(g))
                for g in comp(u,S): note('cons.QNClV',Y.lt(g,Xk) or bv(u,g),k=k,u=Y.tstr(u),g=Y.tstr(g))
        if not cl[:-1]:
            for u in paths[r]|{V}:
                if not le(u,V): continue
                for g in comp(u,S): note('cons.Dom0',le(g,(S,Z,Z)) or any(le(g,d) for d in comp(u,V)),u=Y.tstr(u),g=Y.tstr(g))
    except Exception as e:
        out['exc']+=1; ex.setdefault('exc',{'M':str(M),'e':traceback.format_exc()})
    return out,ex
def norm(mm):
    if isinstance(mm,(bytes,bytearray)): return [tuple(mm[j:j+3]) for j in range(0,len(mm),3)]
    return [tuple(c) for c in mm]
def pre(M):
    if len(M)<2 or not M[-1][2]: return False
    x=len(M)-1
    def par(k,i):
        j=i
        while True:
            j=par(k-1,j) if k>0 else (j-1 if j>0 else None)
            if j is None: return None
            if k==0:
                while j is not None and M[j][0]>=M[i][0]: j=j-1 if j>0 else None
                return j
            if M[j][k]<M[i][k]: return j
    p0=par(0,x);p2=par(2,x)
    return p0 is not None and p2 is not None and p0!=p2
if __name__=='__main__':
    files=sys.argv[1:]
    tot=collections.Counter();exs={}
    for f in files:
        mats=pickle.load(open(f,'rb'))
        if isinstance(mats,dict): mats=list(mats)
        n0=len(mats);mats=[M for M in map(norm,mats) if pre(M)]
        cnt=collections.Counter();exf={}
        with Pool(int(os.environ.get("NP","3"))) as p:
            for c,e in p.imap_unordered(go,mats,chunksize=64):
                cnt.update(c)
                for k,v in e.items():
                    if k not in exf or v.get('n',0)<exf[k].get('n',0): exf[k]=v
        print(os.path.basename(f),n0,len(mats),dict(sorted(cnt.items())),flush=True)
        for k,v in exf.items(): print('  EX',k,json.dumps(v)[:600],flush=True)
        tot.update(cnt)
    print('TOTAL',dict(sorted(tot.items())))
