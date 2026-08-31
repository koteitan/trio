# -*- coding: utf-8 -*-
"""H15 (2): `sbody_w` で衝突している 6 本の中身を見る。

正例（証人が要求）と負例（lim=7 の一致を壊す）が同じ `(行列, 添字)` なら
**行列は同じ**なので、素性の問題ではなく `conv3` の状態／文脈の問題である。
"""
import sys, os, pickle
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
import rows3, rows3b, provc, inv3, sheet3
from core import expand, show, isstd

# 正例をもう一度作る
POS = set()
targets = [((0, 0, 0), (1, 1, 1), (2, 0, 0), (3, 1, 1), (1, 1, 1)),
           ((0, 0, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1), (2, 1, 0))]
targets += [tuple(map(tuple, A)) for A in
            pickle.load(open('/tmp/h1work/cof6.pkl', 'rb'))]
src = {}
for A in targets:
    fA = tuple(map(tuple, rows3.b2d3(list(A))))
    for m in range(1, 7):
        T = tuple(expand(fA, m))
        B = inv3.d2b3([list(x) for x in T])
        if not B:
            continue
        Bt = tuple(tuple(x) for x in B)
        if not isstd(Bt, 'BMS') or any(x[2] > 1 for x in Bt):
            continue
        if tuple(map(tuple, rows3.b2d3(list(Bt)))) == T:
            continue
        oall, F = rows3b.b2d3b(list(Bt))
        if oall != T or not F:
            continue
        offs = sorted(set(f[0] for f in F))
        hit = [o for o in offs if rows3b.b2d3b(list(Bt), sites={o})[0] == T]
        for o in (hit if hit else offs):
            POS.add((Bt, o))
            src.setdefault((Bt, o), []).append((A, m))
NEG = set(tuple(x) for x in
          pickle.load(open('/tmp/h1work/h14sbneg_sbg.pkl', 'rb')))
both = sorted(POS & NEG)
print('正例 %d / 負例 %d / **衝突 %d**' % (len(POS), len(NEG), len(both)))
print()
print('衝突は同じ `(行列, 添字)` なので **行列はまったく同じ**。')
print('つまり素性をいくら足しても分けられない。ちがうのは「その行列が')
print('どの対で使われているか」＝ 外側の文脈である。')
print()
for Bt, off in both:
    print('=== off=%d 柱=%s' % (off, Bt[off]))
    print('   B  = %s' % show([list(x) for x in Bt]))
    print('   証人になっている (A, m): %s'
          % [(show(list(A)), m) for A, m in src[(Bt, off)][:3]])
    # 負例側: この行列を A<n> か A に持つ壊れた対
    print()
pickle.dump(both, open('/tmp/h1work/h15coll.pkl', 'wb'))
