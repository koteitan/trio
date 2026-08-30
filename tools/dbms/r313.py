# -*- coding: utf-8 -*-
"""**(ROW2-4) 自己検査 —— 「`Lift1 X d` の最終列は孤児にならない」は本当か。**

    ⚠ 「多すぎる 0% は警報」
    ⟹ (1) `d` を振る／根の `v` を振る
    ⟹ (2) 人工の総当たり箱（`W` でない列も入る）＝ **破れが出る形を狙う負の対照**
    ⟹ (3) 破れたら、その形を 1 行で
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1
from r260 import reach
from r310 import build_plus

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def orphan(S):
    j = len(S) - 1
    return trio.parent(S, srow(S, j), j) is None


def scan(L, tag, ds=(1, 2, 3)):
    c = Counter(); ex = []
    for X in L:
        X = list(X)
        if len(X) < 2 or X[0][0] != 0: continue
        c['元の X: 最終列が孤児'] += orphan(X)
        c['X の本数'] += 1
        for d in ds:
            Y = Lift1(X, d)
            c['d=%d 分母' % d] += 1
            o = orphan(Y)
            c['d=%d 最終列が孤児' % d] += o
            if o and len(ex) < 5: ex.append((d, X, Y))
    print('  [%s] X %d 本 | 元の X の孤児率 %.4f%%' % (tag, c['X の本数'], pct(c['元の X: 最終列が孤児'], c['X の本数'])))
    for d in ds:
        print('     d=%d: %7d 件中 孤児 %6d  %8.4f%%' % (d, c['d=%d 分母' % d], c['d=%d 最終列が孤児' % d],
                                                     pct(c['d=%d 最終列が孤児' % d], c['d=%d 分母' % d])))
    for (d, X, Y) in ex[:3]:
        print('     ⛔ 破れ例 d=%d: X=%s' % (d, ' '.join('(%d,%d,%d)' % q for q in X[:8])))
        print('                   Y=%s' % ' '.join('(%d,%d,%d)' % q for q in Y[:8]))
    return c


t0 = time.time()
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
scan([list(x) for x in RC], 'Reach（根 (0,0,0)）')
SP = build_plus(RC, (1, 2, 3), rounds=3, cap=400000)
scan([list(x) for x in SP], 'Reach+（根 (0,v,0)、v=0..4）')

print()
print('== ⛔ 負の対照: 人工総当たり（`W` でない列も入る）==')
COL = [(a, b, z) for a in range(0, 4) for b in range(0, 4) for z in (0, 1)]
for LEN in (3, 4):
    ART = [[(0, v, z)] + list(t) for v in (0, 1, 2) for z in (0, 1)
           for t in itertools.product(COL, repeat=LEN - 1)]
    scan(ART, '人工 %d 列 %d 本' % (LEN, len(ART)))
print('（%.1f 秒）' % (time.time() - t0))
