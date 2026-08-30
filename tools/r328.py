# -*- coding: utf-8 -*-
"""**(R-C7)(a) H12 の見立て「0.73% の破れは `d = 0` の分」＋ (b) `j > 0` も含めた `srow` の親の位置。**

## ⚠ (a) の問い

    「`j > 0` ⟹ 同ブロック」の破れは **`d = 0` の分**か。⟹ `d > 0` に絞れば 100% か。
    ⟹ ★ **`j > 0` × (`d = 0` / `d > 0` / `d <= 段差` / `d > 段差`)** の交差表を出す。

## ⚠ (b) の問い（本命）

    `c0 := parent S 0 t`（行 0 の親）、`c := parent S (srow S t) t`（`srow` の親）
    ⟹ ⛔ **`c > c0`（`srow` の親が行 0 の親より後ろ）が 1 件でもあるか** ⟹ **`j > 0` も含めて**
    ⟹ ★ `j=0` は直前ブロック内か、`j>0` は同ブロック内か

## ⚠ 母集団

    Reach の窓（`W_drop` ＋ `W_take`、健全）の狭義 `hr0` な `Q` 400 本
    ⛔ 負の対照: 人工 3 列 6,144 本・4 列 16,384 本（`W` でない）
    **`d ∈ {0,1,2,3,4}`**（規則 8）、`e ∈ {0,1,2}`、`n ∈ {1,2,3}`、`j ∈ [0, |Q|)`。所属の判定はしません。
"""
import sys, itertools, time, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, sh, mTower
from r260 import reach
from r315 import windows, hr0s

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def scan(QS, tag, DS=(0, 1, 2, 3, 4), ES=(0, 1, 2), NS=(1, 2, 3)):
    A = {}; B = {}; exA = []; exB = []
    for Q in QS:
        L = len(Q); span = min(Q[i][0] - Q[0][0] for i in range(1, L))
        for d in DS:
            for e in ES:
                for n in NS:
                    T = mTower(Q, d, e, n); Bl = Lift1(sh(Q, d * n), e * n)
                    for j in range(L):
                        S = T + Bl[:j + 1]; t = len(S) - 1
                        sr = srow(S, t); c = trio.parent(S, sr, t)
                        if c is None: continue
                        c0 = trio.parent(S, 0, t)
                        blk = c // L
                        # ---- (a) j>0 の同ブロック率 ----
                        if j > 0:
                            for kk in ('j>0 全', 'j>0 / d=0' if d == 0 else 'j>0 / d>0',
                                       'j>0 / d<=段差' if d <= span else 'j>0 / d>段差'):
                                g = A.setdefault(kk, Counter()); g['n'] += 1
                                g['★ 同ブロック'] += (blk == n)
                                g['⛔ 直前'] += (blk == n - 1)
                                g['⛔ 奥'] += (blk < n - 1)
                            if blk != n and d > 0 and len(exA) < 3:
                                exA.append((Q, d, e, n, j, c, span))
                        # ---- (b) c vs c0 ----
                        if sr >= 1:
                            for kk in ('★ 全', 'j=0' if j == 0 else 'j>0', 'srow=%d' % sr,
                                       ('d<=段差' if d <= span else 'd>段差')):
                                g = B.setdefault(kk, Counter()); g['n'] += 1
                                g['所定のブロック内'] += (blk == (n if j > 0 else n - 1))
                                if c0 is not None:
                                    g['c = c0'] += (c == c0); g['c < c0'] += (c < c0)
                                    g['⛔ c > c0'] += (c > c0)
                                else: g['行0 親なし'] += 1
                            if c0 is not None and c > c0 and len(exB) < 4:
                                exB.append((Q, d, e, n, j, sr, c, c0))
    print('  [%s]' % tag)
    print('   == (a) `j > 0` の同ブロック率 ==')
    print('     %-18s %9s %13s %11s %10s' % ('群', '分母', '★ 同ブロック', '⛔ 直前', '⛔ 奥'))
    for kk in ('j>0 全', 'j>0 / d=0', 'j>0 / d>0', 'j>0 / d<=段差', 'j>0 / d>段差'):
        g = A.get(kk)
        if not g: continue
        m = g['n']
        print('     %-18s %9d %12.4f%% %10.4f%% %9.4f%%'
              % (kk, m, pct(g['★ 同ブロック'], m), pct(g['⛔ 直前'], m), pct(g['⛔ 奥'], m)))
    for e in exA:
        print('     ⛔ `d > 0` なのに同ブロックでない: Q=%s d=%d e=%d n=%d j=%d 親=%d 段差=%d'
              % (' '.join('(%d,%d,%d)' % q for q in e[0]), e[1], e[2], e[3], e[4], e[5], e[6]))
    print('   == (b) `srow` の親 vs 行 0 の親 ==')
    print('     %-14s %9s %15s %11s %11s %13s' % ('群', '分母', '所定ブロック内', 'c = c0', 'c < c0', '⛔ c > c0'))
    for kk in ('★ 全', 'j=0', 'j>0', 'srow=1', 'srow=2', 'd<=段差', 'd>段差'):
        g = B.get(kk)
        if not g: continue
        m = g['n']
        print('     %-14s %9d %14.4f%% %10.4f%% %10.4f%% %12.4f%%'
              % (kk, m, pct(g['所定のブロック内'], m), pct(g['c = c0'], m), pct(g['c < c0'], m), pct(g['⛔ c > c0'], m)))
    for e in exB:
        print('     ⛔⛔ `c > c0` の例: Q=%s d=%d e=%d n=%d j=%d srow=%d c=%d c0=%d'
              % (' '.join('(%d,%d,%d)' % q for q in e[0]), e[1], e[2], e[3], e[4], e[5], e[6], e[7]))
    if not exB: print('     ★ `c > c0` は **0 件**')


t0 = time.time()
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
QS = [Q for Q in windows([list(x) for x in RC], cap=60000) if 2 <= len(Q) <= 6 and hr0s(Q)]
random.seed(0); random.shuffle(QS); QS = QS[:400]
scan(QS, 'Reach の窓（健全）/ `Q` %d 本' % len(QS))
COL = [(a, b, z) for a in range(1, 5) for b in range(0, 4) for z in (0, 1)]
ART3 = [[(0, v, z)] + list(t) for v in (0, 1, 2) for z in (0, 1) for t in itertools.product(COL, repeat=2)]
scan(ART3, '⛔ 負の対照: 人工 3 列 %d 本' % len(ART3))
ART4 = [[(0, v, z)] + list(t) for v in (0, 1) for z in (0, 1) for t in itertools.product(COL[:16], repeat=3)]
scan(ART4, '⛔ 負の対照: 人工 4 列 %d 本' % len(ART4), ES=(0, 1), NS=(2, 3))
print('（%.1f 秒）' % (time.time() - t0))
