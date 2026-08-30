# -*- coding: utf-8 -*-
"""**(PREV-1) の自己検査 —— 「距離 1 で h1 が 0%」は本物か、箱の癖か。**

    ⚠ 「多すぎる 0% も警報」（自分で作った規則）
    ⟹ (1) 距離 1 の場面で `(C[k-1], p)` の形を数える
    ⟹ (2) 箱を広げる: 開いている条件を外す / Reach 由来 / 部分窓
    ⟹ (3) 「破れが出る形」を狙った負の対照
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r263 import load
from r126 import srow
from r260 import reach

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def scan(mats, tag, require_open=True):
    c = Counter(); shapes = Counter()
    for X in mats:
        X = [tuple(v) for v in X]
        for k in range(1, len(X)):
            C = X[:k]; p = X[k]; T = X[:k + 1]
            if not any(q[2] > 0 for q in C): continue
            sr = srow(T, k)
            if require_open:
                if sr == 0: continue
                if trio.parent(T, sr, k) is None: continue
            ps = [j for j in range(k) if C[j][2] > 0]
            if k - max(ps) != 1: continue
            c['n'] += 1
            h0 = C[k - 1][0] < p[0]; h1 = C[k - 1][1] < p[1]
            c['h0'] += h0; c['h1'] += h1; c['both'] += (h0 and h1)
            shapes[(C[k - 1][1], p[1], 'r1親>' if C[k-1][1] > p[1] else ('=' if C[k-1][1]==p[1] else '<'))] += 1
            c['r1: 前 > p'] += (C[k - 1][1] > p[1])
            c['r1: 前 = p'] += (C[k - 1][1] == p[1])
            c['r1: 前 < p'] += (C[k - 1][1] < p[1])
    n = c['n']
    print('  [%s] 分母 %d | h0 %.4f%% h1 %.4f%% 両立 %.4f%%' % (tag, n, pct(c['h0'], n), pct(c['h1'], n), pct(c['both'], n)))
    print('     行 1 の比較: 前 > p %.4f%% / 前 = p %.4f%% / 前 < p %.4f%%'
          % (pct(c['r1: 前 > p'], n), pct(c['r1: 前 = p'], n), pct(c['r1: 前 < p'], n)))
    return c


def main():
    t0 = time.time()
    M = [[tuple(v) for v in X] for X in load()]
    print('== (1) シート、開いている場面 ==')
    scan(M, 'シート/開', True)
    print('== (2a) シート、開いている条件を外す（箱を広げる） ==')
    scan(M, 'シート/全', False)

    print('== (2b) 部分窓 (M.drop a).take b も母集団に入れる ==')
    sub = []
    for X in M:
        for a in range(0, min(len(X), 6)):
            for b in range(2, min(len(X) - a, 12) + 1):
                sub.append(X[a:a + b])
    print('   部分窓の本数: %d' % len(sub))
    scan(sub, '部分窓/開', True)
    scan(sub, '部分窓/全', False)

    print('== (2c) Reach 由来（シート外） ==')
    try:
        R = [list(x) for x in reach([3, 4], [1, 2, 3], 3)]
    except Exception as e:
        print('   reach 失敗: %s' % e); R = []
    print('   Reach の本数: %d' % len(R))
    if R:
        scan(R, 'Reach/開', True)
        scan(R, 'Reach/全', False)

    print()
    print('== (3) 負の対照: 「破れが出る形」を人工的に作る ==')
    # C[k-1] = (a,b,1) の直後に行 1 がもっと大きい列を置く
    art = []
    for a in range(1, 4):
        for b in range(0, 3):
            for pa in range(0, 5):
                for pb in range(0, 5):
                    for pz in (0, 1):
                        C0 = [(0, 0, 0), (1, 1, 0), (a + 1, b + 1, 1), (pa, pb, pz)]
                        art.append(C0)
    print('   人工列: %d 本' % len(art))
    scan(art, '人工/開', True)
    scan(art, '人工/全', False)
    print()
    print('（%.1f 秒）' % (time.time() - t0))


if __name__ == '__main__':
    main()
