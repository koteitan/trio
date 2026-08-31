# -*- coding: utf-8 -*-
"""**⛔ §R290 の訂正 —— `W_drop` の箱で「残差 ⟹ 末尾の行 1 = 根」が破れる。`srow` 別に確定させる。**"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r263 import load
from r126 import srow
from r260 import reach
from r315 import windows, hr0s

pct = lambda a, b: 100.0 * a / b if b else float('nan')
row2 = lambda Q: any(p[2] > 0 for p in Q)


def orphan(Q):
    j = len(Q) - 1
    return trio.parent(Q, srow(Q, j), j) is None


def scan(QS, tag):
    G = {}; ex = {}
    for Q in QS:
        if not (hr0s(Q) and row2(Q) and orphan(Q)): continue
        s = srow(Q, len(Q) - 1)
        for kk in ('残差 全', '残差 srow=%d' % s):
            g = G.setdefault(kk, Counter())
            g['n'] += 1
            g['末尾行1 = 根'] += (Q[-1][1] == Q[0][1])
            g['末尾行1 > 根'] += (Q[-1][1] > Q[0][1])
            g['⛔ 末尾行1 < 根'] += (Q[-1][1] < Q[0][1])
            g['末尾行2 >= 根'] += (Q[-1][2] >= Q[0][2])
            g['根の行0 = 0'] += (Q[0][0] == 0)
            g['根の行2 = 0'] += (Q[0][2] == 0)
        if Q[-1][1] < Q[0][1]:
            ex.setdefault(s, []).append(Q)
    print('  [%s]' % tag)
    print('     %-16s %8s %11s %11s %13s %12s %11s %11s' % (
        '群', '分母', '末尾行1=根', '末尾行1>根', '⛔末尾行1<根', '末尾行2>=根', '根の行0=0', '根の行2=0'))
    for kk in ('残差 全', '残差 srow=1', '残差 srow=2'):
        g = G.get(kk)
        if not g: continue
        n = g['n']
        print('     %-16s %8d %10.4f%% %10.4f%% %12.4f%% %11.4f%% %10.4f%% %10.4f%%'
              % (kk, n, pct(g['末尾行1 = 根'], n), pct(g['末尾行1 > 根'], n), pct(g['⛔ 末尾行1 < 根'], n),
                 pct(g['末尾行2 >= 根'], n), pct(g['根の行0 = 0'], n), pct(g['根の行2 = 0'], n)))
    for s in (1, 2):
        for Q in ex.get(s, [])[:3]:
            print('     ⛔ srow=%d の反例: %s' % (s, ' '.join('(%d,%d,%d)' % q for q in Q[:9])))
    return G


SH = [[tuple(v) for v in M] for M in load()]
scan(list(windows(SH)), 'シートの窓（健全: W_drop + W_take）')
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
scan(list(windows([list(x) for x in RC], cap=200000)), 'Reach の窓（健全）')

print()
print('== ⚠ 反例 Q = (5,4,0)(6,3,1) の検算 ==')
Q = [(5, 4, 0), (6, 3, 1)]
print('   hr0 = %s / 行2に非零 = %s / srow(末尾) = %d / parent = %s'
      % (hr0s(Q), row2(Q), srow(Q, 1), trio.parent(Q, srow(Q, 1), 1)))
print('   根の行1 = %d、末尾の行1 = %d ⟹ 末尾 < 根 = %s' % (Q[0][1], Q[1][1], Q[1][1] < Q[0][1]))
src = None
for X in RC:
    X = list(X)
    for j in range(len(X)):
        for k in range(j + 2, len(X) + 1):
            if X[j:k] == Q: src = (X, j, k); break
        if src: break
    if src: break
if src:
    X, j, k = src
    print('   出所: Reach の元 %s の窓 [%d:%d] ⟹ ★ `W_drop` ＋ `W_take` で **本物の W の元**'
          % (' '.join('(%d,%d,%d)' % q for q in X), j, k))
else:
    print('   ⚠ 出所が見つかりませんでした')
