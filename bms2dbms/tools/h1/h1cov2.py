# -*- coding: utf-8 -*-
import sys, pickle
sys.path.insert(0,'/tmp/h1work')
NAMES, COLS, YB, FULL, n = pickle.load(open('/tmp/h1work/BITS.pkl','rb'))
red = pickle.load(open('/tmp/h1work/COV.pkl','rb'))
pc = lambda v: bin(v).count('1')
POS = pc(YB)
pairs = []
for i in range(len(red)):
    ci, li, si = red[i]
    for j in range(i+1, len(red)):
        cj, lj, sj = red[j]
        if pc(ci | cj) == POS:
            pairs.append((si+sj, '(%s) | (%s)' % (li, lj)))
pairs.sort()
print('完全に覆う 2 選言 %d 組（項数の少ない順に 25）' % len(pairs))
for s, lb in pairs[:25]:
    print('   %2d  %s' % (s, lb))
singles = [(s,l) for c,l,s in red if pc(c)==POS]
print('1 選言で完全: %d 個' % len(singles))
for s,l in sorted(singles)[:10]: print('   ', l)
