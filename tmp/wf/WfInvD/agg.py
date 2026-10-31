import json,sys,collections,re
T=collections.Counter();n=0
for f in sys.argv[1:]:
    for l in open(f):
        d=json.loads(l);n+=d['cnt'].get('n',0)
        for k,v in d['cnt'].items():
            m=None
            if k.startswith('ua.FAIL.noWCSP'):m='UAw.FAIL(noWCSP)'
            elif k.startswith('ua.FAIL.cmpOnly.t1.xm1=1.kP0=1'):m='ua.cmp.FAIL.t1.L1(guard e2x=0 fails here)'
            elif k.startswith('ua.FAIL.cmpOnly.t'):m='ua.cmp.FAIL.t'+k[17]
            elif k=='ua.cases':m=k
            elif k.startswith('HDropU.ab.FAIL'):m='HDropU.ab.FAIL.t'+k[16]
            elif k.startswith('HDropUg.ab.FAIL'):m='HDropUx.ab.FAIL(no BadAbsShape)'
            elif k.startswith('B2X.new'):m='B2X.new(Bad2 frames added)'
            elif k.startswith('qrSeedC'):m=k
            elif k.startswith('PV.FAIL'):m=k
            elif k.startswith('ab.bas='):m='ab.fail.'+k
            elif k.startswith('exc') or k=='evalfail':m=k
            if m:T[m]+=v
print('measured',n)
for k,v in sorted(T.items()):print(' ',k,v)
