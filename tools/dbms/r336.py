# -*- coding: utf-8 -*-
"""**(R-C16) —— H12 の (W90) の仮定 `hlow` は 100% か。**

## ⚠ 測る述語（逐語）

    `c0 := parent T 0 t`（**行 0 の親**）、`t := |T|-1`
    **`hlow` := `entry T 1 c0 < entry T 1 t`**（行 0 の親の行 1 が的より低い）

## ⚠ 母集団（箱の固定条件、規則 9）

    `T := mTower Q d e n ++ [第 n ブロックの根]`（**`j = 0`**）、**`srow(T,t) >= 1`**、**`c0` が存在**
    `Q`: Reach の窓（`W_drop` ＋ `W_take`、健全）の狭義 `hr0`、`2 <= |Q| <= 6`、標本 400 本
    ⛔ 負の対照: 人工 3 列 400 本（狭義 `hr0`）
    **`d ∈ {1,2,3,4}`**（規則 8）、`e ∈ {0,1,2}`、`n ∈ {1,2,3}`。**所属の判定はしません**。

## ⚠ 測る前の見積もり

    ★ `srow = 1` で **`srow` の親 `c` が存在**するとき:
      `c < c0` なら `nextrel1` の最小性（`∀ j, c < j ∧ le0 T j t → entry T 1 t <= entry T 1 j`）から
      **`entry T 1 c0 >= entry T 1 t`** ⟹ ⛔ **`hlow` が破れる**
    ⟹ ★ そして (R-C7) で **`c = c0` は 71.66% / 87.37% / 83.96%**
    ⟹ ⟹ ⛔ **`hlow` は 100% にならない**と見ます（**7〜28% 破れる**）。
"""
import sys, itertools, time, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, sh, mTower
from r260 import reach
from r315 import windows, hr0s
from r329 import span

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def scan(QS, tag):
    G = {}; ex = []
    for Q in QS:
        L = len(Q); sp = span(Q)
        for d in (1, 2, 3, 4):
            for e in (0, 1, 2):
                for n in (1, 2, 3):
                    T = mTower(Q, d, e, n) + [Lift1(sh(Q, d * n), e * n)[0]]
                    t = len(T) - 1
                    sr = srow(T, t)
                    if sr < 1: continue
                    c0 = trio.parent(T, 0, t)
                    if c0 is None: continue
                    hlow = T[c0][1] < T[t][1]
                    c = trio.parent(T, sr, t)
                    keys = ['★ 全', 'srow=%d' % sr,
                            'd<=段差' if d <= sp else 'd>段差', 'e=0' if e == 0 else 'e>0',
                            ('srow=%d' % sr) + ' / ' + ('e=0' if e == 0 else 'e>0'),
                            ('srow=%d' % sr) + ' / ' + ('d<=段差' if d <= sp else 'd>段差')]
                    for kk in keys:
                        g = G.setdefault(kk, Counter()); g['n'] += 1
                        g['★ hlow'] += hlow
                        g['⛔ ¬hlow'] += (not hlow)
                        g['孤児'] += (c is None)
                        if c is not None:
                            g['親あり'] += 1
                            g['c = c0'] += (c == c0)
                            g['c < c0'] += (c < c0)
                            g['★ hlow ⟺ (c = c0)'] += (hlow == (c == c0))
                    if (not hlow) and len(ex) < 4:
                        ex.append((Q, d, e, n, sr, c0, c, T[c0][1], T[t][1]))
    print('  [%s]' % tag)
    print('     %-22s %9s %11s %11s %10s %11s %16s' % (
        '群', '分母', '★ hlow', '⛔ ¬hlow', '孤児', 'c = c0', '★ hlow ⟺ c=c0'))
    for kk in ('★ 全', 'srow=1', 'srow=2', 'd<=段差', 'd>段差', 'e=0', 'e>0',
               'srow=1 / e=0', 'srow=1 / e>0', 'srow=2 / e=0', 'srow=2 / e>0',
               'srow=1 / d<=段差', 'srow=1 / d>段差', 'srow=2 / d<=段差', 'srow=2 / d>段差'):
        g = G.get(kk)
        if not g: continue
        m = g['n']; pa = g['親あり']
        print('     %-22s %9d %10.4f%% %10.4f%% %9.4f%% %10.4f%% %15.4f%%'
              % (kk, m, pct(g['★ hlow'], m), pct(g['⛔ ¬hlow'], m), pct(g['孤児'], m),
                 pct(g['c = c0'], pa), pct(g['★ hlow ⟺ (c = c0)'], pa)))
    for (Q, d, e, n, sr, c0, c, v0, vt) in ex:
        print('     ⛔ `hlow` の破れ: Q=%s d=%d e=%d n=%d srow=%d ⟹ c0=%d(行1=%d) 的の行1=%d 親c=%s'
              % (' '.join('(%d,%d,%d)' % q for q in Q), d, e, n, sr, c0, v0, vt, c))
    if not ex: print('     ★ `hlow` の破れは **0 件**')
    return G


t0 = time.time()
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
QS = [Q for Q in windows([list(x) for x in RC], cap=60000) if 2 <= len(Q) <= 6 and hr0s(Q)]
random.seed(0); random.shuffle(QS); QS = QS[:400]
scan(QS, 'Reach の窓（健全）/ `Q` %d 本' % len(QS))
COL = [(a, b, z) for a in range(1, 5) for b in range(0, 4) for z in (0, 1)]
ART = [[(0, v, z)] + list(t) for v in (0, 1, 2) for z in (0, 1) for t in itertools.product(COL, repeat=2)]
ART = [Q for Q in ART if hr0s(Q)]
random.seed(0); random.shuffle(ART)
scan(ART[:400], '⛔ 負の対照: 人工 3 列 400 本（狭義 hr0）')
print('（%.1f 秒）' % (time.time() - t0))
