# -*- coding: utf-8 -*-
import sys, pickle, time
sys.path.insert(0,'/tmp/h1work')
NAMES, COLS, YB, FULL, n = pickle.load(open('/tmp/h1work/BITS.pkl','rb'))
LIT = []
for i, nm in enumerate(NAMES):
    LIT.append((nm, COLS[i])); LIT.append(('!'+nm, FULL ^ COLS[i]))
L = len(LIT)
pc = lambda v: bin(v).count('1')
NY = FULL ^ YB
best = []
t0 = time.time()
for i in range(L):
    ai, bi = LIT[i]
    for j in range(i+1, L):
        aj, bj = LIT[j]
        AB = bi & bj; OB = bi | bj
        for k in range(j+1, L):
            ak, bk = LIT[k]
            for lbl, b in (('%s & %s & %s' % (ai,aj,ak), AB & bk),
                           ('%s | %s | %s' % (ai,aj,ak), OB | bk),
                           ('(%s & %s) | %s' % (ai,aj,ak), AB | bk),
                           ('(%s | %s) & %s' % (ai,aj,ak), OB & bk)):
                fp = pc(b & NY); fn = pc(YB & ~b & FULL)
                if fp + fn < 46:
                    best.append((fp+fn, fp, fn, lbl))
print('%.0fs  候補 %d' % (time.time()-t0, len(best)))
best.sort()
seen=set(); out=[]
for t in best:
    if t[3] in seen: continue
    seen.add(t[3]); out.append(t)
    if len(out)>=30: break
print('=== 3 項（誤り<46, 最良 30）')
for e,fp,fn,nm in out:
    print('   %-52s 誤り %4d (深過ぎ %3d / 足りない %3d)' % (nm, e, fp, fn))
pickle.dump(best, open('/tmp/h1work/S3.pkl','wb'))
