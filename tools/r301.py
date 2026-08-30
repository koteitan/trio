# -*- coding: utf-8 -*-
"""**(PREV-3) 深堀り —— 「直前が親」でないとき、親はどこか。**

    ⟹ 候補 A: `c = parent(C, 1, k-1)`（**直前の列の行 1 の親**）
    ⟹ 候補 B: `c = parent(C, 0, k-1)`（直前の列の行 0 の親）
    ⟹ 候補 C: `c = 最も近い行 2 列の位置`
    ⟹ 候補 D: `c = parent(C, srow(C,k-1), k-1)`（直前の列の srow の親）
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r263 import load
from r126 import srow

pct = lambda a, b: 100.0 * a / b if b else float('nan')

M = [[tuple(v) for v in X] for X in load()]
G = {}
ex = []
for X in M:
    for k in range(1, len(X)):
        C = X[:k]; p = X[k]; T = X[:k + 1]
        if not any(q[2] > 0 for q in C): continue
        sr = srow(T, k)
        if sr == 0: continue
        c = trio.parent(T, sr, k)
        if c is None: continue
        ps = [j for j in range(k) if C[j][2] > 0]
        d = k - max(ps)
        if c == k - 1: continue          # ⛔ 直前が親の場合は除外（残り 79.33%）
        A = trio.parent(C, 1, k - 1)
        B = trio.parent(C, 0, k - 1)
        D = trio.parent(C, srow(C, k - 1), k - 1)
        for key in ('ALL', 'srow=%d' % sr, '距離%s' % (d if d <= 3 else '>=4'),
                    '行1: 前=p' if C[k-1][1] == p[1] else ('行1: 前>p' if C[k-1][1] > p[1] else '行1: 前<p')):
            g = G.setdefault(key, Counter())
            g['n'] += 1
            g['A'] += (A is not None and c == A)
            g['B'] += (B is not None and c == B)
            g['C'] += (c == max(ps))
            g['D'] += (D is not None and c == D)
            g['A|C'] += ((A is not None and c == A) or c == max(ps))
        if len(ex) < 6 and not ((A is not None and c == A) or c == max(ps)):
            ex.append((k, sr, c, A, B, max(ps), C[max(0, k-4):k+1], p))

print('== (PREV-3) 「直前が親でない」場面（分母 = 開いている場面 − 窓長 1）==')
print('%-14s %8s %10s %10s %10s %10s %12s' % ('群', '分母', 'A:前の行1親', 'B:前の行0親', 'C:行2列', 'D:前のsrow親', '★ A または C'))
for key in ('ALL', 'srow=1', 'srow=2', '距離1', '距離2', '距離3', '距離>=4', '行1: 前=p', '行1: 前>p', '行1: 前<p'):
    g = G.get(key)
    if not g: continue
    n = g['n']
    print('%-14s %8d %9.4f%% %9.4f%% %9.4f%% %9.4f%% %11.4f%%'
          % (key, n, pct(g['A'], n), pct(g['B'], n), pct(g['C'], n), pct(g['D'], n), pct(g['A|C'], n)))

print()
print('  ⛔ A でも C でもない例（先頭 6 件）:')
for (k, sr, c, A, B, mp, tail, p) in ex:
    print('    k=%d srow=%d 親c=%d | 前の行1親=%s 前の行0親=%s 最近行2列=%d | …%s ++ [%s]' % (k, sr, c, A, B, mp, tail, p))
if not ex: print('    （無し）')
