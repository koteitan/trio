# -*- coding: utf-8 -*-
"""ビット集合で 1〜3 項の述語を総当たり。"""
import sys, pickle, itertools
sys.path.insert(0,'/tmp/h1work')
NAMES, X, Y, META = pickle.load(open('/tmp/h1work/P0.pkl','rb'))
n = len(Y)
FULL = (1 << n) - 1
def col(i):
    v = 0
    for r, x in enumerate(X):
        if x[i]: v |= (1 << r)
    return v
COLS = [col(i) for i in range(len(NAMES))]
YB = 0
for r, y in enumerate(Y):
    if y: YB |= (1 << r)
POS = bin(YB).count('1')

LIT = []
for i, nm in enumerate(NAMES):
    LIT.append((nm, COLS[i]))
    LIT.append(('!' + nm, FULL ^ COLS[i]))

def score(b):
    # 誤り = b XOR YB のビット数、内訳
    fp = bin(b & ~YB & FULL).count('1')   # 深いと言うが正解は浅い
    fn = bin(~b & YB & FULL).count('1')   # 浅いと言うが正解は深い
    return fp + fn, fp, fn

best = []
for nm, b in LIT:
    e, fp, fn = score(b)
    best.append((e, fp, fn, nm))
best.sort()
print('=== 1 項（最良 8）  n=%d  深い %d' % (n, POS))
for e, fp, fn, nm in best[:8]:
    print('   %-16s 誤り %4d (深いと言い過ぎ %3d / 足りない %3d)' % (nm, e, fp, fn))

print('=== 2 項（最良 12）')
best2 = []
L = len(LIT)
for i in range(L):
    ni, bi = LIT[i]
    for j in range(i+1, L):
        nj, bj = LIT[j]
        for op, b in (('&', bi & bj), ('|', bi | bj)):
            e, fp, fn = score(b)
            best2.append((e, fp, fn, '%s %s %s' % (ni, op, nj)))
best2.sort()
seen = set(); out = []
for t in best2:
    if t[3] in seen: continue
    seen.add(t[3]); out.append(t)
    if len(out) >= 12: break
for e, fp, fn, nm in out:
    print('   %-34s 誤り %4d (%3d/%3d)' % (nm, e, fp, fn))
pickle.dump((NAMES, COLS, YB, FULL, n), open('/tmp/h1work/BITS.pkl','wb'))
