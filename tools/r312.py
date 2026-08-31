# -*- coding: utf-8 -*-
"""**(ROW2-4) —— `Reach+` の核 1,436 件で、標的の最終列・孤児構造。**

## ⚠ なぜ新しいか

§R122 で同じ量を測ったが、あれは **`X ∈ W` を落とした上位集合**だった（明記済み）。
今回は **`Reach+ ⊆ W`（健全）** なので **前提が本物の事例**だけで測る。

## ⚠ 逐語

    `Aop` 節 3（`Wset.lean:169`）: `∃ m, m < u ∧ domT M m ∧ …`
    `domT M m` = `lev M (|M|-1) = m + 1` ∧ `¬ hasParent M (srow M (|M|-1)) (|M|-1)`
    ⟹ **`m < u ⟺ lev Y (|Y|-1) <= u`**（第 1 連言から）

    核（`v=0`）: `X = (0,0,0)::R`、`argOK R`、`∃p∈R, p.2.1=0`、`∃p∈X, 0<p.2.2`
    標的 `Y := Lift1 X 1 ∈ W u`、**`u = 2*v+z+2 = 2`**

## ⚠ 測る前の見積もり

§R122（上位集合）は `|R|` とともに単調減で **18〜21% 頭打ち**。
`Reach+` の核は列が長いので、★ **5〜15%** と見ます。破れの主因は **`lev` 側**（孤児より厳しい）。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1
from r260 import reach
from r310 import build_plus

pct = lambda a, b: 100.0 * a / b if b else float('nan')
lev = lambda S, j: 2 * S[j][1] + S[j][2]


def orphan(S):
    j = len(S) - 1
    return trio.parent(S, srow(S, j), j) is None


t0 = time.time()
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
SP = build_plus(RC, (1, 2, 3), rounds=3, cap=400000)
print('|Reach+| = %d' % len(SP))

core = []
for X in SP:
    X = list(X)
    if len(X) < 2 or X[0] != (0, 0, 0): continue
    R = X[1:]
    if not all(p[0] > 0 for p in R): continue
    if all(p[1] > 0 for p in R): continue          # 狭義／無タイ（緑）
    if all(p[2] == 0 for p in X): continue         # 行2≡0（緑）
    core.append(X)
print('★ 核（v=0、前提 4 本すべて確認ずみ）= %d 件' % len(core))

G = {}
ex = []
for X in core:
    Y = Lift1(X, 1)
    u = 2                                          # v=0, z=0 ⟹ u = 2*v+z+2 = 2
    jl = len(Y) - 1
    lv = lev(Y, jl)
    orp = orphan(Y)
    sr = srow(Y, jl)
    srX = srow(X, len(X) - 1)
    for key in ('全', 'srow=%d' % sr, '|X| = %s' % (len(X) if len(X) <= 5 else ('6-9' if len(X) <= 9 else '>=10'))):
        g = G.setdefault(key, Counter())
        g['n'] += 1
        g['lev <= u'] += (lv <= u)
        g['最終列が孤児'] += orp
        g['★ 節3が使える'] += (lv <= u and orp)
        g['⛔ lev だけ破れ'] += (lv > u and orp)
        g['⛔ 孤児だけ破れ'] += (lv <= u and not orp)
        g['⛔ 両方破れ'] += (lv > u and not orp)
        g['srow_Lift1_last の検算'] += (sr == srX)
    if not (lv <= u and orp) and len(ex) < 5:
        ex.append((X, Y, lv, orp, sr))

print()
print('== (ROW2-4) 標的 `Y = Lift1 X 1` で 節 3（graft）が使えるか（u = 2）==')
print('%-12s %7s %10s %11s %12s | %10s %10s %10s' % ('群', '分母', 'lev<=u', '最終列が孤児', '★ 節3が使える', 'lev だけ破', '孤児だけ破', '両方破'))
for key in ('全', 'srow=0', 'srow=1', 'srow=2', '|X| = 2', '|X| = 3', '|X| = 4', '|X| = 5', '|X| = 6-9', '|X| = >=10'):
    g = G.get(key)
    if not g: continue
    n = g['n']
    print('%-12s %7d %9.4f%% %10.4f%% %11.4f%% | %9.4f%% %9.4f%% %9.4f%%'
          % (key, n, pct(g['lev <= u'], n), pct(g['最終列が孤児'], n), pct(g['★ 節3が使える'], n),
             pct(g['⛔ lev だけ破れ'], n), pct(g['⛔ 孤児だけ破れ'], n), pct(g['⛔ 両方破れ'], n)))
g = G['全']
print('   ⚠ `L105.srow_Lift1_last`（緑）の検算: %d / %d = %.4f%%'
      % (g['srow_Lift1_last の検算'], g['n'], pct(g['srow_Lift1_last の検算'], g['n'])))

print()
print('  ⛔ 節 3 が使えない例（先頭 5 件）:')
for (X, Y, lv, orp, sr) in ex:
    print('    X=%s' % ' '.join('(%d,%d,%d)' % q for q in X[:7]))
    print('      Y=%s  lev(最終)=%d 孤児=%s srow=%d' % (' '.join('(%d,%d,%d)' % q for q in Y[:7]), lv, orp, sr))

print()
print('== ⚠ 対照: 核でない群（緑 4 本のどれかが当たる）でも同じ量を測る ==')
c = Counter()
for X in SP:
    X = list(X)
    if len(X) < 2 or X[0] != (0, 0, 0): continue
    R = X[1:]
    if not all(p[0] > 0 for p in R): continue
    if not (all(p[1] > 0 for p in R) or all(p[2] == 0 for p in X)): continue
    Y = Lift1(X, 1); jl = len(Y) - 1
    c['n'] += 1
    c['lev <= 2'] += (lev(Y, jl) <= 2)
    c['孤児'] += orphan(Y)
    c['節3が使える'] += (lev(Y, jl) <= 2 and orphan(Y))
print('   分母 %d | lev<=u %.4f%% / 孤児 %.4f%% / 節3が使える %.4f%%'
      % (c['n'], pct(c['lev <= 2'], c['n']), pct(c['孤児'], c['n']), pct(c['節3が使える'], c['n'])))
print('（%.1f 秒）' % (time.time() - t0))
