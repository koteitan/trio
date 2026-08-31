# -*- coding: utf-8 -*-
"""fp=0 の連言（<=3 項）を全部集めて、正例 525 本を少ない選言で覆う。"""
import sys, pickle, time, itertools
sys.path.insert(0,'/tmp/h1work')
NAMES, COLS, YB, FULL, n = pickle.load(open('/tmp/h1work/BITS.pkl','rb'))
LIT = []
for i, nm in enumerate(NAMES):
    LIT.append((nm, COLS[i])); LIT.append(('!'+nm, FULL ^ COLS[i]))
L = len(LIT); NY = FULL ^ YB
pc = lambda v: bin(v).count('1')
POS = pc(YB)
cands = []            # (covered_bits, label, size)
t0=time.time()
for i in range(L):
    ni, bi = LIT[i]
    if not (bi & NY):
        c = bi & YB
        if c: cands.append((c, ni, 1))
    for j in range(i+1, L):
        nj, bj = LIT[j]
        b2 = bi & bj
        if not (b2 & NY):
            c = b2 & YB
            if c: cands.append((c, '%s & %s' % (ni,nj), 2))
            continue          # 3 項に伸ばしても覆いは増えない
        for k in range(j+1, L):
            nk, bk = LIT[k]
            b3 = b2 & bk
            if b3 and not (b3 & NY):
                cands.append((b3 & YB, '%s & %s & %s' % (ni,nj,nk), 3))
print('fp=0 の連言 %d 個  %.0fs' % (len(cands), time.time()-t0))
# 覆いの極大なものだけ残す
cands.sort(key=lambda t: (-pc(t[0]), t[2]))
red = []
seenb = set()
for c, lb, sz in cands:
    if c in seenb: continue
    seenb.add(c)
    red.append((c, lb, sz))
print('相異なる覆い %d 個' % len(red))
print('最大の覆い 10 個:')
for c, lb, sz in red[:10]:
    print('   %-50s 覆い %d/%d' % (lb, pc(c), POS))
# 貪欲被覆
sel = []; cov = 0
while cov != YB and len(sel) < 6:
    best = max(red, key=lambda t: pc(t[0] & ~cov))
    g = pc(best[0] & ~cov)
    if g == 0: break
    sel.append(best); cov |= best[0]
    print('   +%-48s 新規 %4d  累計 %d/%d' % (best[1], g, pc(cov), POS))
print('貪欲 %d 項で 覆い %d/%d  残り %d' % (len(sel), pc(cov), POS, POS-pc(cov)))
pickle.dump(red, open('/tmp/h1work/COV.pkl','wb'))
