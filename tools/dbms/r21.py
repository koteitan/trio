# -*- coding: utf-8 -*-
"""(S3) `PrefixT3`: 切れ目（加算ユニットの端）で切れば接頭辞の像は像の接頭辞か。

    j が切れ目  <=>  closes_top(Mo, j-1, Mo[j]) が真
`j` が切れ目かどうかで**層別**して破れを数える。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import b2d3, closes_top, closes_unit
from rows3 import gen3, key
from collections import Counter

W = sys.argv[1]
if W == 'stts':
    P = r7.stts_pool(int(sys.argv[2]), int(sys.argv[3]))
    nm = 'ST_TS v<=%s len<=%s' % (sys.argv[2], sys.argv[3])
else:
    P = [tuple(map(tuple, M)) for M in sorted(gen3('BMS', int(W), zcap=1), key=key)]
    nm = 'gen3 <=%s' % W
c = Counter(); ex = {}
t0 = time.time()
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    B = tuple(tuple(x) for x in b2d3(list(M)))
    for j in range(1, len(M)):
        Bk = tuple(tuple(x) for x in b2d3(list(M[:j])))
        # j は切れ目か（第 j-1 列の次が第 j 列で、ユニットを閉じるか）
        cut = closes_top(M, j - 1, M[j])
        cu = closes_unit(M[j])
        ok = (B[:len(Bk)] == Bk)
        c['_対'] += 1
        c['切れ目=%s  接頭辞になる=%s' % (cut, ok)] += 1
        c['closes_unit=%s  接頭辞になる=%s' % (cu, ok)] += 1
        if cut and not ok and ('cut' not in ex):
            ex['cut'] = (M, j, Bk, B)
        if cu and not ok:
            ex.setdefault('cu', []).append((M, j, Bk, B))
print('== %s  母数 %d 行列 / (M,j) の対 %d  %.0fs'
      % (nm, len(P), c['_対'], time.time() - t0))
for k in sorted(c, key=str):
    if not k.startswith('_'):
        print('   %-40s %d' % (k, c[k]))
for M, j, Bk, B in ex.get('cu', [])[:8]:
    print('   ### **closes_unit の切れ目なのに接頭辞にならない**')
    print('      M     = %s   j=%d  M[j]=%s'
          % (''.join(str(x).replace(' ', '') for x in M), j, M[j]))
    print('      f(M[:j]) = %s' % ''.join(str(x).replace(' ', '') for x in Bk))
    print('      f(M)     = %s' % ''.join(str(x).replace(' ', '') for x in B))
if 'cut' in ex:
    M, j, Bk, B = ex['cut']
    print('   ### 切れ目なのに接頭辞にならない例')
    print('      M     = %s' % ''.join(str(x).replace(' ', '') for x in M))
    print('      j     = %d' % j)
    print('      f(M[:j]) = %s' % ''.join(str(x).replace(' ', '') for x in Bk))
    print('      f(M)     = %s' % ''.join(str(x).replace(' ', '') for x in B))
