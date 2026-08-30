# -*- coding: utf-8 -*-
"""H13 (2): 基準線の食い違い（rows3.check の 34 と imgfast.score の 40）を潰す。"""
import sys, pickle, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, imgfast, inv3
from rows3 import gen3, key, b2d3, preimage_try
from core import show
lim = int(sys.argv[1]) if len(sys.argv) > 1 else 6
A = [M for M in sorted(gen3('BMS', lim, zcap=1), key=key) if len(M) > 1]
print('lim=%d: |A|>1 の標準形 %d 個' % (lim, len(A)))
t0 = time.time()
r1 = imgfast.imgclosed_fast(b2d3, A, 3, None)
b1 = set(r1[2])
print('(a) imgfast, 段 1 = 素の d2b3        : 破れた A %d 個  (%.0fs)'
      % (len(b1), time.time() - t0))
t0 = time.time()
r2 = imgfast.imgclosed_fast(
    b2d3, A, 3, (lambda T: preimage_try(b2d3, T, inv3.d2b3)))
b2 = set(r2[2])
print('(b) imgfast, 段 1 = preimage_try 付き: 破れた A %d 個  (%.0fs)'
      % (len(b2), time.time() - t0))
print('    (a) - (b) = %d   (b) - (a) = %d' % (len(b1 - b2), len(b2 - b1)))
for M in sorted(b1 - b2, key=key)[:8]:
    print('      preimage_try が救出: %s' % show(list(M)))
pickle.dump((sorted(b1, key=key), sorted(b2, key=key), r1.badpairs, r2.badpairs),
            open('/tmp/h1work/h13base%d.pkl' % lim, 'wb'))
