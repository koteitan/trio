# -*- coding: utf-8 -*-
"""**(W74-M) の自己検査 —— 0.0000% は本物か。陽性対照 ＋ 箱を広げる。**

    ⚠ 「多すぎる 0% は警報」
    ⟹ (1) **陽性対照**: 残差でない `Q`（`Q` の中で親を持つ）は、塔でも親を保つか ⟹ 100% のはず
    ⟹ (2) `d, e, n` をもっと広げる（`e` を 4 まで、`n` を 6 まで）
    ⟹ (3) シートの窓の `srow=2` 残差（16 件）も入れる
    ⟹ (4) ⛔ 負の対照: 人工の `srow=2` 残差でも 0% か（0% でなければ、機構が Reach の偏り）
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r263 import load
from r126 import srow
from r113 import mTower
from r260 import reach
from r315 import windows, hr0s

pct = lambda a, b: 100.0 * a / b if b else float('nan')
le1 = lambda M, y, j: trio.is_ancestor(M, 1, y, j)


def hasp2(M):
    t = len(M) - 1
    return any(M[c][2] == 0 and le1(M, c, t) for c in range(t))


def split(QS):
    res, ok = [], []
    for Q in QS:
        if len(Q) < 2 or not hr0s(Q): continue
        if srow(Q, len(Q) - 1) != 2: continue
        (res if trio.parent(Q, 2, len(Q) - 1) is None else ok).append(Q)
    return res, ok


t0 = time.time()
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
SH = [[tuple(v) for v in M] for M in load()]
resR, okR = split(windows([list(x) for x in RC], cap=200000))
resS, okS = split(windows(SH))
COL = [(a, b, z) for a in range(0, 4) for b in range(0, 3) for z in (0, 1)]
resA, okA = split([list(t) for t in itertools.product(COL, repeat=3)])
print('== 母集団 ==')
print('  Reach の窓: 残差 %d / 親あり %d ｜ シートの窓: 残差 %d / 親あり %d ｜ ⛔人工3列: 残差 %d / 親あり %d'
      % (len(resR), len(okR), len(resS), len(okS), len(resA), len(okA)))

print()
print('== (1) ★ 陽性対照: **親あり** の `Q` は、塔でも親を保つか（100% のはず）==')
print('%-6s %-4s %-4s %14s %14s %14s' % ('n', 'd', 'e', 'Reach 親あり', 'シート 親あり', '⛔人工 親あり'))
for (n, d, e) in ((2, 1, 1), (3, 1, 1), (2, 1, 0), (3, 2, 2)):
    row = []
    for L in (okR, okS, okA):
        c = sum(1 for Q in L if hasp2(mTower(Q, d, e, n)))
        row.append(pct(c, len(L)))
    print('%-6d %-4d %-4d %13.4f%% %13.4f%% %13.4f%%' % (n, d, e, row[0], row[1], row[2]))

print()
print('== (2)(3)(4) ★ 残差群を、箱を広げて測る ==')
print('%-6s %-4s %-4s %14s %14s %14s' % ('n', 'd', 'e', 'Reach 残差', 'シート 残差', '⛔人工 残差'))
for n in (2, 3, 4, 6):
    for d in (0, 1, 2, 3):
        for e in (1, 2, 3, 4):
            row = []
            for L in (resR, resS, resA):
                c = sum(1 for Q in L if hasp2(mTower(Q, d, e, n)))
                row.append(pct(c, len(L)))
            if max(row) > 0 or (n, d, e) in ((2, 1, 1), (3, 1, 1), (6, 3, 4)):
                print('%-6d %-4d %-4d %13.4f%% %13.4f%% %13.4f%%' % (n, d, e, row[0], row[1], row[2]))
print('  ⟹ 上に出ていない (n,d,e) は 3 群とも 0.0000% です')

print()
print('== ★ 機構の確認: 塔の末尾は、そもそも行 1 の親を持つか ==')
c = Counter()
for Q in resR:
    for (n, d, e) in ((2, 1, 1), (3, 1, 1), (3, 2, 2)):
        M = mTower(Q, d, e, n); t = len(M) - 1
        c['分母'] += 1
        c['行1の親がある'] += (trio.parent(M, 1, t) is not None)
        c['末尾の行1 が塔の最小'] += (M[t][1] == min(q[1] for q in M))
print('   分母 %d | 行 1 の親がある %.4f%% | ★ 末尾の行 1 が塔の最小 %.4f%%'
      % (c['分母'], pct(c['行1の親がある'], c['分母']), pct(c['末尾の行1 が塔の最小'], c['分母'])))
print('（%.1f 秒）' % (time.time() - t0))
