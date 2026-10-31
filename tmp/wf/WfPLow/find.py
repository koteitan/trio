import sys,json
sys.path[:0]=['tmp/codex','tools']
from t2src_a_trio_codex import *
d=json.load(open('tmp/wf/WfSrcP/p7.json'))
for s,r in d['sets'].items():
  for t,e in r['examples'].items():
    if '.P.cls' not in t: continue
    M=[tuple(map(int,q.split(','))) for q in e['matrix_text'].strip('()').split(')(')]
    C=Ctx(M);x=e['x'];m=e['m'];c=e['c']
    V=C.v(m)
    print('==',s[-10:],t,'x',x,'m',m,M[m],'c',c,M[c],'P1m',C.e.par(1,m),'upg m',C.e._upg[m] if hasattr(C.e,'_upg') else None)
    print('  V=',Y.tstr(V))
    # strip: V -> arg chain
    for k in range(len(M)):
        for nm,val in (('o',C.o(k)),('v',C.v(k))):
            sv=Y.tstr(val)
            if sv and sv!='0' and sv in Y.tstr(V) and len(sv)>8: print('   ',nm,k,M[k],sv)
