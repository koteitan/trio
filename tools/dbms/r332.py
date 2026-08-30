# -*- coding: utf-8 -*-
"""**(R-C11) —— (R-C9) の本線 14 件で、実際に `mTower` を作って鎖を回す。**

## ⚠ 本線の形（team-lead / L3 / H12 の逐語）

    本線の `Q` ＝ **`Lift1 ((0, v, z) :: R.dropLast) t`**
    **`d = entry R 0 (R の末尾列)`**（H12 の (W80)）
    `M = (0, v, z) :: R` が出所の行列 ⟹ **`v = M[0][1]`、`z = M[0][2]`**
    `t` は塔の持ち上げ量（`oper_cons_tower2` では `entry R 1 (末尾) - v`）⟹ ★ **その値 ＋ 0,1,2 も振る**

## ⚠ 母集団

    (R-C9) で見つけた **本線の `R` 14 件**（`Reach` 29,459 本から、`argOK ∧ domT ∧ 末尾が行 0 最浅`）
    `e ∈ {0,1,2}`、`n0, k ∈ {1,2,3}`、15 段。**所属の判定はしません**。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1
from r260 import reach
from r329 import step, span
from r330 import argOK, domT, shallowest

pct = lambda a, b: 100.0 * a / b if b else float('nan')

t0 = time.time()
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6),
                      ((1, 2, 3, 4, 5, 6, 7, 8), (1, 2), 6), ((1, 2, 3, 4), (1, 2, 3, 4), 6),
                      ((1, 2, 3, 4, 5, 6), (1, 2, 3, 4), 5), ((2, 3, 5, 7), (1, 2, 3), 7)):
    RC |= reach(vs, ns, depth)
found = {}
for X in RC:
    X = list(X)
    if not X or X[0][0] != 0: continue
    R = X[1:]
    if len(R) < 1 or not argOK(R) or not domT(R) or not shallowest(R): continue
    if tuple(R) not in found: found[tuple(R)] = X
print('== (R-C9) の本線 R: %d 件（うち |R|>=2 が %d 件）=='
      % (len(found), sum(1 for R in found if len(R) >= 2)))

c = Counter(); rows = []
for Rt, M in sorted(found.items(), key=lambda kv: len(kv[0])):
    R = list(Rt); v, z = M[0][1], M[0][2]
    d = R[-1][0]
    QQbase = [(0, v, z)] + R[:-1]      # (0,v,z) :: R.dropLast
    if len(QQbase) < 2:
        c['⛔ |Q| < 2（自明）'] += 1; continue
    tlift = max(0, R[-1][1] - v)
    for t in sorted({0, 1, 2, tlift}):
        Q = Lift1(QQbase, t)
        sp = span(Q)
        for e in (0, 1, 2):
            for n0 in (1, 2, 3):
                for k in (1, 2, 3):
                    c['鎖'] += 1
                    c['★ d <= 段差'] += (d <= sp)
                    QQ, dd, ee, nn = Q, d, e, n0
                    steps = 0; how = None
                    for i in range(15):
                        st, lab, sr, cc = step(QQ, dd, ee, nn)
                        if st is None: how = lab; break
                        QQ, dd, ee = st; nn = k; steps += 1
                    if how is None: c['⛔ 15 段続いた'] += 1
                    else:
                        c['★ 終了'] += 1; c['終了 段%d' % min(steps, 9)] += 1
                        c['★★ 3 段以内'] += (steps <= 2)
    rows.append((R, M, v, z, d, span(Lift1(QQbase, 0))))

n = c['鎖']
print('  鎖 %d 本 | ★ 終了 %.4f%% / ⛔ 15 段続いた %d 件 | ★★ 3 段以内 %.4f%% | `d <= 段差` %.4f%%'
      % (n, pct(c['★ 終了'], n), c['⛔ 15 段続いた'], pct(c['★★ 3 段以内'], n), pct(c['★ d <= 段差'], n)))
print('  終了段の分布: ' + ' / '.join('段%d %d (%.2f%%)' % (i, c['終了 段%d' % i], pct(c['終了 段%d' % i], n))
                                  for i in range(6) if c['終了 段%d' % i]))
print()
print('== ★ 本線 14 件の逐語（`|R|>=2` を優先）==')
for (R, M, v, z, d, sp) in rows:
    print('  R = %-42s ／ M = %-46s ／ v=%d z=%d d=%d 段差(Q)=%d %s'
          % (' '.join('(%d,%d,%d)' % q for q in R), ' '.join('(%d,%d,%d)' % q for q in M),
             v, z, d, sp, '★d<=段差' if d <= sp else '⛔d>段差'))
print()
print('== ⚠ 「行 1 が全部同じ（タイ）」か ==')
cc = Counter()
for (R, M, v, z, d, sp) in rows:
    cc['n'] += 1
    cc['R の行 1 が全部同じ'] += (len(set(q[1] for q in R)) == 1)
    cc['R に v と同じ行 1 の列がある（タイ）'] += any(q[1] == v for q in R)
    cc['R の行 1 の最大 = 最小 + 1 以内'] += (max(q[1] for q in R) - min(q[1] for q in R) <= 1)
print('   分母 %d | 行 1 が全部同じ %.4f%% / v とタイ %.4f%% / 行 1 の幅 <= 1 %.4f%%'
      % (cc['n'], pct(cc['R の行 1 が全部同じ'], cc['n']),
         pct(cc['R に v と同じ行 1 の列がある（タイ）'], cc['n']),
         pct(cc['R の行 1 の最大 = 最小 + 1 以内'], cc['n'])))
print('（%.1f 秒）' % (time.time() - t0))
