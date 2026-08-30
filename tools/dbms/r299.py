# -*- coding: utf-8 -*-
"""**(PREV-1) 続き —— シート 0% と Reach 100% の食い違いの正体。**"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r263 import load
from r126 import srow
from r260 import reach
import core

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def d1scenes(X):
    X = [tuple(v) for v in X]
    for k in range(1, len(X)):
        C = X[:k]; p = X[k]; T = X[:k + 1]
        ps = [j for j in range(k) if C[j][2] > 0]
        if not ps or k - max(ps) != 1: continue
        sr = srow(T, k)
        if sr == 0 or trio.parent(T, sr, k) is None: continue
        yield (k, C, p, T, sr)


print('== Reach の距離 1 の場面（先頭 6 件）==')
R = [list(x) for x in reach([3, 4], [1, 2, 3], 3)]
n = 0
for X in R:
    for (k, C, p, T, sr) in d1scenes(X):
        print('   C[k-1]=%s p=%s srow=%d  列全体=%s' % (C[k-1], p, sr, X[:k+2]))
        n += 1
        if n >= 6: break
    if n >= 6: break

print()
print('== シートの距離 1 の場面（先頭 6 件）==')
M = [[tuple(v) for v in X] for X in load()]
n = 0
for X in M:
    for (k, C, p, T, sr) in d1scenes(X):
        print('   C[k-1]=%s p=%s srow=%d  列全体=%s' % (C[k-1], p, sr, X[:k+2]))
        n += 1
        if n >= 6: break
    if n >= 6: break

print()
print('== 標準形か（core.isstd）==')
for tag, L in (('シート', M), ('Reach', R)):
    c = Counter()
    for X in L:
        c['n'] += 1
        try: c['std'] += bool(core.isstd([list(q) for q in X]))
        except Exception as e: c['err'] += 1
    print('   %s: %d 本中 標準形 %d 本 (%.2f%%) err=%d' % (tag, c['n'], c['std'], pct(c['std'], c['n']), c['err']))

print()
print('== Reach の距離 1 場面だけ、標準形に絞ると ==')
c = Counter()
for X in R:
    try: std = bool(core.isstd([list(q) for q in X]))
    except Exception: std = False
    for (k, C, p, T, sr) in d1scenes(X):
        c['n'] += 1
        h0 = C[k-1][0] < p[0]; h1 = C[k-1][1] < p[1]
        c['both'] += (h0 and h1)
        if std:
            c['std_n'] += 1; c['std_both'] += (h0 and h1)
print('   全 %d 件 両立 %.4f%% / 標準形だけ %d 件 両立 %.4f%%'
      % (c['n'], pct(c['both'], c['n']), c['std_n'], pct(c['std_both'], c['std_n'])))

print()
print('== 「(i,i,1) の形」の有無で分ける ==')
for tag, L in (('シート', M), ('Reach', R)):
    c = Counter()
    for X in L:
        for (k, C, p, T, sr) in d1scenes(X):
            q = C[k-1]
            key = 'q=(i,i,1)' if q[0] == q[1] else 'q!=(i,i,1)'
            c[key] += 1
            if C[k-1][1] < p[1]: c[key + '/h1'] += 1
    for key in ('q=(i,i,1)', 'q!=(i,i,1)'):
        print('   %s %s: %d 件、h1 成立 %.4f%%' % (tag, key, c[key], pct(c[key + '/h1'], c[key])))
