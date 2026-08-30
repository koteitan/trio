# -*- coding: utf-8 -*-
"""**(PREV-1) 強化ストレス —— Reach を深くして、(i,i,1) 以外の行 2 列を出す。**"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r263 import load
from r126 import srow
from r260 import reach
import core

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def scan(L, tag):
    c = Counter()
    for X in L:
        X = [tuple(v) for v in X]
        for k in range(1, len(X)):
            C = X[:k]; p = X[k]; T = X[:k + 1]
            ps = [j for j in range(k) if C[j][2] > 0]
            if not ps or k - max(ps) != 1: continue
            sr = srow(T, k)
            if sr == 0 or trio.parent(T, sr, k) is None: continue
            c['n'] += 1
            q = C[k - 1]
            h0 = q[0] < p[0]; h1 = q[1] < p[1]
            c['h0'] += h0; c['h1'] += h1; c['both'] += (h0 and h1)
            c['iii' if q[0] == q[1] else 'other'] += 1
            if q[0] != q[1]:
                c['other/h1'] += h1; c['other/both'] += (h0 and h1)
            c['r1>'] += (q[1] > p[1]); c['r1='] += (q[1] == p[1]); c['r1<'] += (q[1] < p[1])
    n = c['n']
    print('  [%-16s] 分母 %6d | h0 %8.4f%% h1 %8.4f%% ★両立 %8.4f%%   (行1: 前> %.2f%% / = %.2f%% / < %.2f%%)'
          % (tag, n, pct(c['h0'], n), pct(c['h1'], n), pct(c['both'], n),
             pct(c['r1>'], n), pct(c['r1='], n), pct(c['r1<'], n)))
    print('     うち q=(i,i,1) %d 件 / q!=(i,i,1) %d 件（後者の両立 %.4f%%）'
          % (c['iii'], c['other'], pct(c['other/both'], c['other'])))
    return c


t0 = time.time()
M = [[tuple(v) for v in X] for X in load()]
print('== 母集団を並べる ==')
scan(M, 'シート')
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5),
                      ((1, 2, 3, 4), (1, 2, 3, 4), 5),
                      ((1, 2, 3, 4, 5, 6), (1, 2, 3), 5)):
    R = [list(x) for x in reach(vs, ns, depth)]
    scan(R, 'Reach %s d%d' % (str(vs[-1]), depth))
    print('     Reach の本数 %d' % len(R))

print()
print('== 標準形か（core.isstd(b, 3)）==')
for tag, L in (('シート', M),):
    c = Counter()
    for X in L:
        c['n'] += 1
        try: c['std'] += bool(core.isstd(tuple(tuple(q) for q in X), 3))
        except Exception as e:
            c['err'] += 1; c['msg'] = str(e)
    print('   %s: %d 本中 標準形 %d 本 (%.2f%%) err=%d %s' % (tag, c['n'], c['std'], pct(c['std'], c['n']), c['err'], c.get('msg', '')))
print('（%.1f 秒）' % (time.time() - t0))
