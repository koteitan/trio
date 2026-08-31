# -*- coding: utf-8 -*-
"""**(PREV-A) の仮説を締める —— `entry C 0 A < p.1` を足せば 100% か。**

    ★ **(PREV-A+)**  `srow (C++[p]) |C| = 1`
                   ∧ `entry C 1 (|C|-1) = p.2.1`          -- 行 1 が等しい
                   ∧ `A := parent C 1 (|C|-1)` が存在
                   ∧ `entry C 0 A < p.1`                   -- ★ 追加
                   ⟹ `nextrel1 (C ++ [p]) A |C|`
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r263 import load
from r126 import srow
from r260 import reach

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def scan(L, tag):
    G = {}; ex = []
    for X in L:
        X = [tuple(v) for v in X]
        for k in range(1, len(X)):
            C = X[:k]; p = X[k]; T = X[:k + 1]
            if not any(q[2] > 0 for q in C): continue
            sr = srow(T, k)
            if sr == 0: continue
            c = trio.parent(T, sr, k)
            if c is None: continue
            if C[k - 1][1] != p[1]: continue
            A = trio.parent(C, 1, k - 1)
            if A is None: continue
            for key in ('srow=%d' % sr,):
                g = G.setdefault(key, Counter()); g['n'] += 1
                g['素の c=A'] += (c == A)
                if C[A][0] < p[0]:
                    g['条件付き分母'] += 1
                    g['★ 条件付き c=A'] += (c == A)
                    if c != A and len(ex) < 5:
                        ex.append((sr, k, c, A, C[max(0, k - 4):k], p))
    print('  [%s]' % tag)
    for key in ('srow=1', 'srow=2'):
        g = G.get(key)
        if not g: continue
        print('     %-8s 素: %6d 件中 %8.4f%%   |  ★ 条件付き: %6d 件中 %8.4f%%（破れ %d）'
              % (key, g['n'], pct(g['素の c=A'], g['n']), g['条件付き分母'],
                 pct(g['★ 条件付き c=A'], g['条件付き分母']),
                 g['条件付き分母'] - g['★ 条件付き c=A']))
    for e in ex[:4]:
        print('     ⛔ 条件付きでも破れ: srow=%d k=%d c=%d A=%d …%s ++ [%s]' % e)


M = [[tuple(v) for v in X] for X in load()]
scan(M, 'シート')
sub = []
for X in M:
    for a in range(0, min(len(X), 6)):
        for b in range(2, min(len(X) - a, 12) + 1):
            sub.append(X[a:a + b])
scan(sub, '部分窓 %d 本' % len(sub))
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3, 4), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 5)):
    scan([list(x) for x in reach(vs, ns, depth)], 'Reach v<=%d d%d' % (vs[-1], depth))
COL = [(a, b, z) for a in range(0, 5) for b in range(0, 4) for z in (0, 1)]
scan([[(0, 0, 0)] + list(t) for t in itertools.product(COL, repeat=3)], '人工 総当たり 64,000 本')
COL4 = [(a, b, z) for a in range(0, 4) for b in range(0, 4) for z in (0, 1)]
scan([[(0, 0, 0)] + list(t) for t in itertools.product(COL4, repeat=4)], '人工 4 列 %d 本' % (32 ** 4))
