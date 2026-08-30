# -*- coding: utf-8 -*-
"""**★★★★★ 候補補題 (LIFT-ORPH): `HasParentInBlock` は `Lift1` で不変か。**

    HasParentInBlock N := hasParent N (srow N (|N|-1)) (|N|-1)     -- `L53Subst:914`
    ★ 主張: **`HasParentInBlock X ↔ HasParentInBlock (Lift1 X d)`**（点ごと）
    ⟹ ★ 既存の緑 `L105.srow_Lift1_last`（`srow` は不変）の相方になります。
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1
from r260 import reach
from r310 import build_plus

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def orph(S):
    j = len(S) - 1
    return trio.parent(S, srow(S, j), j) is None


def par(S):
    j = len(S) - 1
    return trio.parent(S, srow(S, j), j)


def scan(L, tag, ds=(1, 2, 3)):
    c = Counter(); ex = []
    for X in L:
        X = list(X)
        if len(X) < 2 or X[0][0] != 0: continue
        oX = orph(X); pX = par(X)
        for d in ds:
            Y = Lift1(X, d)
            c['分母'] += 1
            oY = orph(Y)
            c['★ 孤児性が一致'] += (oX == oY)
            c['★★ 親の位置も一致'] += (pX == par(Y))
            if oX != oY and len(ex) < 4: ex.append(('孤児性', d, X, Y))
            elif pX != par(Y) and len(ex) < 4: ex.append(('親の位置', d, X, Y, pX, par(Y)))
    n = c['分母']
    print('  [%-26s] 分母 %8d | ★ 孤児性一致 %9.4f%% | ★★ 親の位置も一致 %9.4f%%'
          % (tag, n, pct(c['★ 孤児性が一致'], n), pct(c['★★ 親の位置も一致'], n)))
    for e in ex[:3]:
        if e[0] == '孤児性':
            print('     ⛔ 孤児性の破れ d=%d: X=%s / Y=%s' % (e[1], e[2][:6], e[3][:6]))
        else:
            print('     ⚠ 親の位置の破れ d=%d: X=%s (親 %s) / Y=%s (親 %s)' % (e[1], e[2][:6], e[4], e[3][:6], e[5]))


t0 = time.time()
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
scan([list(x) for x in RC], 'Reach %d 本' % len(RC))
SP = build_plus(RC, (1, 2, 3), rounds=3, cap=400000)
import random
random.seed(0)
SPL = [list(x) for x in SP]
random.shuffle(SPL)
scan(SPL[:60000], "Reach+ 標本 60,000/%d 本" % len(SP))
COL = [(a, b, z) for a in range(0, 4) for b in range(0, 4) for z in (0, 1)]
for LEN in (3, 4):
    ART = [[(0, v, z)] + list(t) for v in (0, 1, 2) for z in (0, 1)
           for t in itertools.product(COL, repeat=LEN - 1)]
    scan(ART, '⛔ 人工 %d 列 %d 本' % (LEN, len(ART)))
# 根が (c,v,z) で c>0 の場合も（正規化の罠よけ）
ART2 = [[(c, v, z)] + list(t) for c in (1, 2) for v in (0, 1, 2) for z in (0, 1)
        for t in itertools.product(COL, repeat=2)]
scan(ART2, '⛔ 人工 根の行0>0 %d 本' % len(ART2))
print('（%.1f 秒）' % (time.time() - t0))
