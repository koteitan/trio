# -*- coding: utf-8 -*-
"""**(PREV-A) の自己検査 —— 「行 1 が等しいなら親 = 直前の行 1 親」100% は本物か。**

    ⚠ 「多すぎる 100% は警報」
    ⟹ (1) srow 別に分ける（srow=2 では親は行 2 の親なので、成立理由が違う）
    ⟹ (2) 母集団を広げる: 部分窓 / Reach / 人工列
    ⟹ (3) 負の対照: 「破れが出る形」を狙う
"""
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r263 import load
from r126 import srow
from r260 import reach

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def scan(L, tag):
    G = {}
    ex = []
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
            # 最小形: h0 ∧ h1 ⟺ c = k-1 ?
            g = G.setdefault('最小形 全', Counter()); g['n'] += 1
            g['h0h1'] += (h0 and h1); g['c=k-1'] += (c == k - 1)
            g['⟸ 破れ'] += ((h0 and h1) and c != k - 1)
            g['⟹ 破れ'] += ((c == k - 1) and not (h0 and h1))
            if (h0 and h1) and c != k - 1 and len(ex) < 5:
                ex.append(('最小形⟸', k, sr, c, q, p))
            # (PREV-A)
            if q[1] == p[1]:
                for key in ('PREV-A 全', 'PREV-A srow=%d' % sr):
                    g = G.setdefault(key, Counter()); g['n'] += 1
                    g['A なし'] += (A is None)
                    g['c=A'] += (A is not None and c == A)
                    if A is not None: g['窓長 k-A'] += (k - A)
                if not (A is not None and c == A) and len(ex) < 10:
                    ex.append(('PREV-A', k, sr, c, q, p))
    print('  [%s]' % tag)
    for key in ('最小形 全', 'PREV-A 全', 'PREV-A srow=1', 'PREV-A srow=2'):
        g = G.get(key)
        if not g: continue
        n = g['n']
        if key.startswith('最小形'):
            print('     %-16s 分母 %6d | h0h1 %.4f%% / c=k-1 %.4f%% | ⛔⟸破れ %d 件 ⛔⟹破れ %d 件'
                  % (key, n, pct(g['h0h1'], n), pct(g['c=k-1'], n), g['⟸ 破れ'], g['⟹ 破れ']))
        else:
            print('     %-16s 分母 %6d | ★ c=A %.4f%% | A なし %d 件 | 平均窓長 %.2f'
                  % (key, n, pct(g['c=A'], n), g['A なし'], (g['窓長 k-A'] / n) if n else 0))
    for e in ex[:5]:
        print('     ⛔ 破れ例: %s k=%d srow=%d c=%d 前=%s p=%s' % e)
    return G


t0 = time.time()
M = [[tuple(v) for v in X] for X in load()]
print('== 母集団を並べる ==')
scan(M, 'シート 1,637 本')

sub = []
for X in M:
    for a in range(0, min(len(X), 6)):
        for b in range(2, min(len(X) - a, 12) + 1):
            sub.append(X[a:a + b])
scan(sub, '部分窓 %d 本' % len(sub))

for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3, 4), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 5)):
    R = [list(x) for x in reach(vs, ns, depth)]
    scan(R, 'Reach v<=%d d%d (%d 本)' % (vs[-1], depth, len(R)))

print()
print('== 負の対照: 「破れが出る形」を人工的に総当たり ==')
COL = [(a, b, z) for a in range(0, 5) for b in range(0, 4) for z in (0, 1)]
art = []
for t in itertools.product(COL, repeat=3):
    art.append([(0, 0, 0)] + list(t))
print('   人工列 %d 本（(0,0,0) + 任意 3 列）' % len(art))
scan(art, '人工 総当たり')
print('（%.1f 秒）' % (time.time() - t0))
