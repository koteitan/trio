"""Re-measure the current top hypotheses on a matrix pkl (WfReM, 2026-10-31).
usage: remeasure.py PROBE[,PROBE..] NPROC PKL...   (nice -n 15; NPROC <= 4)
Probes (per matrix M; existing scripts reused):
 hdropu : tools/probe_dropres.measure (HardArg, VSmallNew, WeakCS, BumpWeakSrc shape, BumpAbsC) + Bad2 (bad2_exact).
          HDropU.ab = BumpAbsC failure with (not Bad2 or e1 x = 0)  [HDropU's second conjunct: a refutation];
          BumpAbsC failure on Bad2 with e1 x != 0 is only a failure of the first disjunct of BumpAbsCB (reported apart);
          BumpWeakSrc (shape, old) failure is a candidate failure of BumpWeakShapeSrcB (weaker: psi w y, needs UpgBad/BadPos).
 hframe : tools/probe_hframe.measure (HFrameV2 / HLeafV2 fields)
 local  : codex residual_extension_local.run (Inv3V2 S/W fields, HBumpExt, UpgAbsXW0 = ua, SibColU)
 t2     : codex residual_extension_t2.run (seeds hCl/hPRE/hDomQ, KAG KA/KG, T2VAncStep diag)
 vraesc : tmp/claude/probe_t2vra_esc.measure (T2VRACopyEsc)
 qndom  : WfScout/qndom.go (T2QNDomBad2)
 canon  : WfScout/canon.go (HCanonV2)
 b2s    : WfB2S/fr6.run MODE=all (B2LevS = S.FAIL, B2UpgV = V.FAIL)
 sib    : WfH7W/probe_sib.run (H7WSib)
 plow   : WfPLow/probe_o.run (PLowRes)
 term   : WfTerm/probe_v.run (TermHi: V3.BAD)
 vanc   : tmp/claude/usefld.go (T2VAncUse)
"""
import sys,os,pickle,json,collections,time,importlib
from multiprocessing import Pool
for p in ['/home/koteitan/proofs/trio/tools','/home/koteitan/proofs/trio/tmp/codex','/home/koteitan/proofs/trio/tmp/lead/probes',
          '/home/koteitan/proofs/trio/tmp/claude']:
    if p not in sys.path:sys.path.append(p)
W='/home/koteitan/proofs/trio/tmp/wf/'
def ms(M):return ''.join('(%d,%d,%d)'%tuple(c) for c in M)
def load_mod(path,name):
    d=os.path.dirname(path)
    if d not in sys.path:sys.path.insert(0,d)
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
_M={}
def mod(k):
    if k in _M:return _M[k]
    if k=='D':import probe_dropres as m
    elif k=='HF':import probe_hframe as m
    elif k=='A':
        import residual_extension_local_trio_codex as m
        if not hasattr(m,'run_local'):m.run_local=m.run
    elif k=='T2':
        mod('A');import residual_extension_t2_trio_codex as m
    elif k=='VE':import probe_t2vra_esc as m
    elif k=='QN':m=load_mod(W+'WfScout/qndom.py','qndom_w')
    elif k=='CA':m=load_mod(W+'WfScout/canon.py','canon_w')
    elif k=='B2':m=load_mod(W+'WfB2S/fr6.py','fr6_w');m.MODE='all'
    elif k=='SB':m=load_mod(W+'WfH7W/probe_sib.py','probe_sib_w')
    elif k=='PL':m=load_mod(W+'WfPLow/probe_o.py','probe_o_w')
    elif k=='TE':m=load_mod(W+'WfTerm/probe_v.py','probe_v_w')
    elif k=='VA':import usefld as m
    elif k=='BAD2':
        import bad2_exact_trio_codex as m
    _M[k]=m;return m
def fails(cnt):return {k:v for k,v in cnt.items() if ('fail' in k.lower() or 'BAD' in k or 'exception' in k or k.endswith('.False') or 'err' in k) and v}
def run_one(probe,M,cnt,ex):
    def add(c,e,pref):
        for k,v in c.items():cnt[pref+str(k)]+=v
        if e:
            for k,v in (e.items() if isinstance(e,dict) else [('ex',e)]):
                kk=pref+str(k)
                if kk not in ex or len(M)<ex[kk][0]:ex[kk]=(len(M),ms(M),str(v)[:600])
    if probe=='hdropu':
        D=mod('D');cc,ee=D.measure(M);add(cc,None,'')
        bf=cc.get('BumpAbsC.failures',0)
        if bf or cc.get('BumpWeakSrc.failures',0):
            from huac_structure_trio_codex import Ctx as HC
            try:b2=mod('BAD2').bad2(HC(M),HC(M[:-1]))[0]
            except Exception:b2='err'
            if bf:
                tag='HDropU.ab.FAIL' if (b2 is False or M[-1][1]==0) else 'BumpAbsC.onBad2(first disjunct of CB fails)'
                cnt[tag]+=1
                if tag not in ex or len(M)<ex[tag][0]:ex[tag]=(len(M),ms(M),str(ee.get('BumpAbsC'))[:400])
            if cc.get('BumpWeakSrc.failures',0):
                cnt['BumpWeakSrc.old.fail.bad2=%s'%b2]+=1
                t='BumpWeakSrc.old.fail.bad2=%s'%b2
                if t not in ex or len(M)<ex[t][0]:ex[t]=(len(M),ms(M),str(ee.get('BumpWeakSrc'))[:400])
        import hdropB
        from probe_inv3_prefix import Ctx as PC
        C_=PC(M);T_=PC(M[:-1]);a_=hdropB.ua(C_);b_=hdropB.wsB(C_,T_)
        cnt['HDropU.ua.cases']+=len(a_);cnt['HDropU.wsB.cases']+=len(b_)
        for tag,bad in (('HDropU.ua.FAIL',[t for t in a_ if not t]),('HDropU.wsB.FAIL',[t for t in b_ if not t[1]])):
            if bad:
                cnt[tag]+=1
                if tag not in ex or len(M)<ex[tag][0]:ex[tag]=(len(M),ms(M),str(bad)[:300])
        for f in ('HardArg','VSmallNew','WeakCS'):
            if cc.get(f+'.failures',0):
                t='HDropU.%s.FAIL'%f
                if t not in ex or len(M)<ex[t][0]:ex[t]=(len(M),ms(M),str(ee.get(f))[:400])
    elif probe=='hframe':
        cc,ee=mod('HF').measure(M);add({k:v for k,v in cc.items() if not k.startswith(('TPLoW','AbsDW'))},None,'')
        from hframe_s import measure_s
        c2,e2=measure_s(M);add({k:v for k,v in c2.items() if k.startswith(('TPLoW','AbsDW'))},{k:v for k,v in e2.items() if k.startswith(('TPLoW','AbsDW'))},'seed.')
    elif probe=='vsf':
        from vsmallf import vsmallf
        b=vsmallf(M);cnt['VSmallF.cases']+=1
        if b:
            cnt['VSmallF.failures']+=1
            if 'VSmallF' not in ex or len(M)<ex['VSmallF'][0]:ex['VSmallF']=(len(M),ms(M),str(b))
    elif probe=='local':cc,ee=mod('A').run_local([bytes(v for c in M for v in c)]);add(cc,ee,'')
    elif probe=='t2':cc,ee=mod('T2').run([bytes(v for c in M for v in c)]);add(cc,ee,'')
    elif probe=='vraesc':cc,ee=mod('VE').measure(M);add(cc,ee,'')
    elif probe=='qndom':cc,ee=mod('QN').go(M);add(cc,ee,'')
    elif probe=='canon':cc,ee=mod('CA').go(M);add(cc,ee,'')
    elif probe=='b2s':cc,ee=mod('B2').run([M]);add(cc,ee,'')
    elif probe=='sib':cc,ee=mod('SB').run([M]);add(cc,ee,'')
    elif probe=='plow':cc,ee=mod('PL').run([M]);add(cc,ee,'')
    elif probe=='term':cc,ee=mod('TE').run([M]);add(cc,ee,'')
    elif probe=='vanc':cc,ee=mod('VA').go(tuple(M));add(cc,ee,'')
PROBES=None
def work(batch):
    cnt=collections.Counter();ex={}
    for mm in batch:
        M=[tuple(c) for c in mm]
        for p in PROBES:
            c2=collections.Counter()
            try:run_one(p,M,c2,ex)
            except Exception as e:
                c2['harness_exception.'+type(e).__name__]+=1
                k=p+'.harness_exception'
                if k not in ex:ex[k]=(len(M),ms(M),repr(e)[:300])
            for k,v in c2.items():cnt[p+':'+k]+=v
    return cnt,ex
def init(pr):
    global PROBES;PROBES=pr
if __name__=='__main__':
    pr=sys.argv[1].split(',');npr=int(sys.argv[2])
    for f in sys.argv[3:]:
        t=time.time();mats=pickle.load(open(f,'rb'))
        if isinstance(mats,dict):mats=mats['seeds']+mats['ext'] if 'seeds' in mats else list(mats.values())
        cnt=collections.Counter();ex={}
        with Pool(npr,initializer=init,initargs=(pr,)) as pool:
            for c,e in pool.imap_unordered(work,(mats[i:i+40] for i in range(0,len(mats),40))):
                cnt.update(c)
                for k,v in e.items():
                    if k not in ex or v[0]<ex[k][0]:ex[k]=v
        F=fails(cnt)
        print(json.dumps({'set':os.path.basename(f),'probes':pr,'n':len(mats),'sec':round(time.time()-t),'fails':F,
            'ex':{k:v for k,v in ex.items() if any(k.split(':')[-1] in kk or k in kk for kk in F) or 'FAIL' in k or 'exception' in k},
            'cnt':dict(sorted(cnt.items()))}),flush=True)
