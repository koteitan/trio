# -*- coding: utf-8 -*-
"""**(INV-1) 続き —— `hr0` だけでは偽。**(b) 行 2 に非零**を足すと救えるか。**"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r263 import load
from r126 import srow
from r260 import reach
from r315 import windows, hr0s, inv1, inv1L, inv2, inv2L

pct = lambda a, b: 100.0 * a / b if b else float('nan')
row2 = lambda Q: any(p[2] > 0 for p in Q)


def orphan(Q):
    j = len(Q) - 1
    return trio.parent(Q, srow(Q, j), j) is None


def scan(QS, tag):
    G = {}; ex = {}
    for Q in QS:
        h = hr0s(Q); b = row2(Q)
        keys = ['全']
        if h: keys.append('(a) hr0')
        if h and b: keys.append('★ (a)∧(b)')
        if h and b and orphan(Q): keys.append('★★ (a)∧(b)∧孤児（残差）')
        if h and b and not orphan(Q): keys.append('⚠ (a)∧(b)∧親あり（対照）')
        for kk in keys:
            g = G.setdefault(kk, Counter())
            g['n'] += 1
            g['行1最小(全列)'] += inv1(Q)
            g['行1(末尾)'] += inv1L(Q)
            g['行2最小(全列)'] += inv2(Q)
            g['行2(末尾)'] += inv2L(Q)
            g['末尾の行1 = 根'] += (Q[0][1] == Q[-1][1])
        if h and b and not inv1L(Q) and len(ex.get('ab', [])) < 3:
            ex.setdefault('ab', []).append(Q)
        if h and b and orphan(Q) and not inv1L(Q) and len(ex.get('res', [])) < 3:
            ex.setdefault('res', []).append(Q)
    print('  [%s]' % tag)
    print('     %-26s %8s %12s %11s %12s %11s %13s' % (
        '群', '分母', '行1最小(全列)', '行1(末尾)', '行2最小(全列)', '行2(末尾)', '末尾の行1=根'))
    for kk in ('全', '(a) hr0', '★ (a)∧(b)', '★★ (a)∧(b)∧孤児（残差）', '⚠ (a)∧(b)∧親あり（対照）'):
        g = G.get(kk)
        if not g: continue
        n = g['n']
        print('     %-26s %8d %11.4f%% %10.4f%% %11.4f%% %10.4f%% %12.4f%%'
              % (kk, n, pct(g['行1最小(全列)'], n), pct(g['行1(末尾)'], n),
                 pct(g['行2最小(全列)'], n), pct(g['行2(末尾)'], n), pct(g['末尾の行1 = 根'], n)))
    for k, lbl in (('ab', '⛔ (a)∧(b) で末尾の行1 < 根'), ('res', '⛔⛔ 残差で末尾の行1 < 根')):
        for Q in ex.get(k, []):
            print('     %s: %s' % (lbl, ' '.join('(%d,%d,%d)' % q for q in Q[:9])))
    return G


t0 = time.time()
SH = [[tuple(v) for v in M] for M in load()]
scan(list(windows(SH)), 'シートの窓（健全: W_drop + W_take）')
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
scan(list(windows([list(x) for x in RC], cap=200000)), 'Reach の窓（健全）')
COL = [(a, b, z) for a in range(0, 4) for b in range(0, 3) for z in (0, 1)]
scan([list(t) for t in itertools.product(COL, repeat=3)], '⛔ 負の対照: 人工 3 列')
scan([list(t) for t in itertools.product(COL, repeat=4)][:200000], '⛔ 負の対照: 人工 4 列（20 万本）')
print('（%.1f 秒）' % (time.time() - t0))
