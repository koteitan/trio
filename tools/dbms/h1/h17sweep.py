# -*- coding: utf-8 -*-
"""H17 (2): つまみを 1 本 / 2 本の総当たりで、証人が何対直るかだけを粗く測る。"""
import sys, os, pickle, itertools, subprocess, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
KNOBS = ['cbd1', 'crd1', 'sb', 'sb_w', 'cbls', 'cbfa', 'cbfirst',
         'sdall', 'sibnball', 'awall']
CODE = '''
import sys, os, pickle
sys.path.insert(0,"/tmp/h1work"); sys.path.insert(0,"/home/koteitan/proofs/dbms/tools/dbms")
import rows3, rows3k2, inv3
from core import expand, isstd
tg=[tuple(map(tuple,A)) for A in pickle.load(open("/tmp/h1work/cof6.pkl","rb"))]
tg+= [((0,0,0),(1,1,1),(2,0,0),(3,1,1),(1,1,1)), ((0,0,0),(1,1,1),(1,1,0),(2,2,1),(2,1,0))]
tot=0; fix=0
for A in tg:
    fA=tuple(map(tuple,rows3.b2d3(list(A))))
    for m in range(1,6):
        T=tuple(expand(fA,m)); B=inv3.d2b3([list(x) for x in T])
        if not B: continue
        Bt=tuple(tuple(x) for x in B)
        if not isstd(Bt,"BMS") or any(x[2]>1 for x in Bt): continue
        if tuple(map(tuple,rows3.b2d3(list(Bt))))==T: continue
        tot+=1
        if tuple(map(tuple,rows3k2.b2d3(list(Bt))))==T: fix+=1
print("%d %d"%(tot,fix))
'''
combos = [()] + [(k,) for k in KNOBS] + list(itertools.combinations(KNOBS, 2))
combos = [c for c in combos if not ('sb_w' in c and 'sb' not in c)]
res = []
t0 = time.time()
for c in combos:
    env = dict(os.environ)
    env['KFLAGS'] = ','.join(c)
    r = subprocess.run([sys.executable, '-c', CODE], env=env,
                       capture_output=True, text=True)
    try:
        tot, fix = map(int, r.stdout.split())
    except Exception:
        print('  失敗 %s: %s' % (c, r.stderr.strip().split('\n')[-1][:80]))
        continue
    res.append((fix, c, tot))
res.sort(reverse=True)
print('つまみの組 %d 通り  (%.0fs)   母数 = 証人 %d 対' % (len(res), time.time() - t0, res[0][2]))
for fix, c, tot in res[:18]:
    print('   %-30s 直る証人 %d' % (','.join(c) or '(なし)', fix))
pickle.dump(res, open('/tmp/h1work/h17sweep.pkl', 'wb'))
