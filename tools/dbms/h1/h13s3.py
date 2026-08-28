# -*- coding: utf-8 -*-
"""H13 (5b): 像のバッドルート r' は何なのか（(S2-b) の正しい形をさがす）。"""
import sys, time
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
import rows3, provc, core
from rows3 import gen3, key
from core import pim, show
from h13s2 import badroot, imgmap

lim = int(sys.argv[1]) if len(sys.argv) > 1 else 6
A = sorted(gen3('BMS', lim, zcap=1), key=key)
c = Counter()
ex = {}
t0 = time.time()
for i, M in enumerate(A):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    S = tuple(map(tuple, M))
    br = badroot(S)
    if br is None:
        continue
    t, r = br
    C, PR = provc.b2d3p(list(S))
    B = C
    br2 = badroot(B)
    if br2 is None:
        c['像の末尾が孤児'] += 1
        continue
    t2, r2 = br2
    c['_母数'] += 1
    # 末尾列が出した柱の添字（順に sh0 / sh1 / body のどれか）
    last = len(S) - 1
    pl = [i2 for i2, e in enumerate(PR) if e[1] == last]
    kinds = [PR[i2][0] for i2 in pl]
    img_r = next((i2 for i2, e in enumerate(PR)
                  if e[1] == r and e[0] == 'body'), None)
    # 仮説 1: r' = 末尾列の第 (t-1) 柱
    h1 = (pl[t - 1] if 0 <= t - 1 < len(pl) else None)
    # 仮説 2: r' = img r
    h2 = img_r
    # 仮説 3: r' = 末尾列の最初の柱 - 1 + t
    c['t=%d' % t] += 1
    c['t=%d 仮説1 r\'=末尾の第(t-1)柱 %s' % (t, 'OK' if r2 == h1 else 'NG')] += 1
    c['t=%d 仮説2 r\'=img r %s' % (t, 'OK' if r2 == h2 else 'NG')] += 1
    c['t=%d 末尾の柱の種類 %s' % (t, ','.join(kinds))] += 1
    if r2 != h1:
        k = ('h1NG', t, tuple(kinds))
        if k not in ex:
            ex[k] = (S, B, t, r, r2, pl, kinds, img_r)
print('lim=%d: 母数 %d  (%.0fs)' % (lim, c['_母数'], time.time() - t0))
for k in sorted(c, key=str):
    if k.startswith('_'):
        continue
    print('   %-46s %d' % (k, c[k]))
print()
for k, e in list(ex.items())[:6]:
    S, B, t, r, r2, pl, kinds, img_r = e
    print('   %s' % str(k))
    print('      A = %s' % show([list(x) for x in S]))
    print('      B = %s' % show([list(x) for x in B]))
    print('      t=%d r=%d  r\'=%d  末尾の柱 %s (%s)  img r=%s'
          % (t, r, r2, pl, kinds, img_r))
