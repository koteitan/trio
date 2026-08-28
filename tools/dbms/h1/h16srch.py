# -*- coding: utf-8 -*-
"""H16: 族 II（証人が取れない 3 個）を**下限も上限も無しの探索**で確定させる。"""
import sys, time, pickle
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3, imgfast
from core import expand, show

CAP = int(sys.argv[2]) if len(sys.argv) > 2 else 400000
# 下限 lo なし・長さ上限 Lmax なし・節点上限だけ
LAD = ((4, CAP, False, None), (6, CAP, False, None),
       (8, CAP, False, None), (12, CAP, False, None))
i = int(sys.argv[1])
CASES = [((0, 0, 0), (1, 1, 1), (2, 0, 0), (3, 1, 1), (3, 1, 0), (3, 1, 0)),
         ((0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 0, 0), (3, 1, 1), (4, 1, 0)),
         ((0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (4, 1, 1), (5, 1, 0))]
A = CASES[i]
fA = tuple(map(tuple, rows3.b2d3(list(A))))
print('A = %s' % show(list(A)))
print('conv3 A = %s' % show([list(x) for x in fA]))
out = []
for m in (1, 2, 3):
    T = tuple(expand(fA, m))
    t0 = time.time()
    _, B, st, nodes, capped = imgfast.find2(
        tuple(A), m, f=rows3.b2d3, ladder=LAD, T=T, scale=64)
    print('  m=%d |T|=%2d -> %s  (段 %s, 節点 %d, 打ち切り %s, %.0fs)'
          % (m, len(T), ('**逆像 %s**' % show([list(x) for x in B])) if B else 'なし',
             st, nodes, capped, time.time() - t0), flush=True)
    out.append((m, B, st, nodes, capped))
pickle.dump(out, open('/tmp/h1work/h16srch%d.pkl' % i, 'wb'))
