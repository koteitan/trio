# -*- coding: utf-8 -*-
"""H28 (4): `cofinal.py` の `mmax` を上げると γ / β / δ が消えないか。

`ImgCofinalT` は「**いくらでも大きい m** で逆像がある」なので、
`m` を大きくすれば当たる A は破れではない。
"""
import sys, pickle, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import cofinal, rows3, imgfast, inv3
from core import show
lim = int(sys.argv[1]) if len(sys.argv) > 1 else 6
MM = int(sys.argv[2]) if len(sys.argv) > 2 else 32
t0 = time.time()
r = imgfast.score(lim=lim, mmax=3, verbose=0, f=rows3.b2d3,
                  d2b3=(lambda T: rows3.preimage_try(rows3.b2d3, T, inv3.d2b3)))
bad = sorted(set(A for A, m, T in r.badpairs), key=rows3.key)
print('ImgClosedT(m<=3) の破れ %d 個  (%.0fs)' % (len(bad), time.time() - t0))
out = []
for A in bad:
    p = cofinal.hits(A, MM)
    out.append((A, p))
still = [(A, p) for A, p in out if not cofinal.cofinal_ok(p)]
print('m<=%d まで見て **ImgCofinalT でも破れ %d 個**  (%.0fs)'
      % (MM, len(still), time.time() - t0))
print()
for A, p in out:
    tag = '**破れ**' if not cofinal.cofinal_ok(p) else '  当たる '
    print('   %s %-40s %s' % (tag, show(list(A)), p))
pickle.dump([A for A, p in still], open('/tmp/h1work/cof6_mm%d.pkl' % MM, 'wb'))
