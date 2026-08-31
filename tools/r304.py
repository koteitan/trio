# -*- coding: utf-8 -*-
"""**(PREV-A)(最小形) を `srow` で分けて、破れの形を特定する。**"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r263 import load
from r126 import srow
from r260 import reach

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def scan(L, tag, show=0):
    G = {}; exA = []; exM = []
    for X in L:
        X = [tuple(v) for v in X]
        for k in range(1, len(X)):
            C = X[:k]; p = X[k]; T = X[:k + 1]
            if not any(q[2] > 0 for q in C): continue
            sr = srow(T, k)
            if sr == 0: continue
            c = trio.parent(T, sr, k)
            if c is None: continue
            q = C[k - 1]
            h0 = q[0] < p[0]; h1 = q[1] < p[1]
            A = trio.parent(C, 1, k - 1)
            g = G.setdefault('最小形 srow=%d' % sr, Counter()); g['n'] += 1
            g['⟸破れ'] += ((h0 and h1) and c != k - 1)
            g['⟹破れ'] += ((c == k - 1) and not (h0 and h1))
            g['h0h1'] += (h0 and h1); g['c=k-1'] += (c == k - 1)
            if sr == 1 and (h0 and h1) and c != k - 1 and len(exM) < 5:
                exM.append((k, c, C[max(0, k - 3):k], p))
            if q[1] == p[1]:
                g = G.setdefault('PREV-A srow=%d' % sr, Counter()); g['n'] += 1
                ok = (A is not None and c == A)
                g['c=A'] += ok
                if sr == 1 and not ok and len(exA) < 6:
                    exA.append((k, c, A, C[max(0, k - 4):k], p, h0))
    print('  [%s]' % tag)
    for key in ('最小形 srow=1', '最小形 srow=2', 'PREV-A srow=1', 'PREV-A srow=2'):
        g = G.get(key)
        if not g: continue
        n = g['n']
        if key.startswith('最小形'):
            print('     %-16s 分母 %6d | h0h1 %7.4f%% c=k-1 %7.4f%% | ⛔⟸破れ %5d ⛔⟹破れ %5d'
                  % (key, n, pct(g['h0h1'], n), pct(g['c=k-1'], n), g['⟸破れ'], g['⟹破れ']))
        else:
            print('     %-16s 分母 %6d | ★ c=A %8.4f%%  （破れ %d 件）' % (key, n, pct(g['c=A'], n), n - g['c=A']))
    if show:
        for e in exM[:show]: print('     ⛔ 最小形⟸破れ(srow=1): k=%d c=%d …%s ++ [%s]' % e)
        for e in exA[:show]: print('     ⛔ PREV-A 破れ(srow=1): k=%d c=%d A=%s …%s ++ [%s] h0=%s' % e)


M = [[tuple(v) for v in X] for X in load()]
scan(M, 'シート 1,637 本', show=3)
sub = []
for X in M:
    for a in range(0, min(len(X), 6)):
        for b in range(2, min(len(X) - a, 12) + 1):
            sub.append(X[a:a + b])
scan(sub, '部分窓 %d 本' % len(sub), show=3)
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3, 4), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 5)):
    R = [list(x) for x in reach(vs, ns, depth)]
    scan(R, 'Reach v<=%d d%d' % (vs[-1], depth), show=3)
COL = [(a, b, z) for a in range(0, 5) for b in range(0, 4) for z in (0, 1)]
art = [[(0, 0, 0)] + list(t) for t in itertools.product(COL, repeat=3)]
scan(art, '人工 総当たり %d 本' % len(art), show=6)
