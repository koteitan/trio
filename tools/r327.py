# -*- coding: utf-8 -*-
"""**(R-C7) —— `j=0` ∧ `d>0` ∧ `srow >= 1` ∧ 親あり で、`srow` の親はどこか。**

## ⚠ 測る対象

    `T := mTower Q d e n ++ [第 n ブロックの根]`、末尾 `t = n*|Q|`
    `c0 := parent T 0 t`（**行 0 の親**）、`c := parent T (srow T t) t`（**`srow` の親**）
    `k戻り := n - (c // |Q|)`
    ★ **H12 の見立て**: 「`nextrel1` は `le0` を含むので行 0 版から絞れる」
      ⟹ ⚠ **`nextrel1 M j0 j1` は `le0 M j0 j1` を要求**（`Trio.lean:49` 逐語）
      ⟹ ★ ですから `srow` の親は **行 0 の祖先鎖の上**にあり、**`c <= c0` のはず**
      ⟹ ⛔ **`c > c0` が 1 件でもあれば、見立てが崩れます** ⟹ ★ そこが要点

## ⚠ 母集団

    Reach の窓（`W_drop` ＋ `W_take`、健全）の狭義 `hr0` な `Q` 400 本 ／ ⛔ 負の対照 人工 3 列・4 列
    **`d ∈ {1,2,3,4}`**（`d <= 2` の罠を避ける）、`e ∈ {0,1,2}`、`n ∈ {1,2,3}`
    ⚠ **`srow = 1` / `2`、`d <= 段差` / `>` を必ず分ける**。**所属の判定はしません**。

## ⚠ 測る前の見積もり

    `c <= c0` は **100%**（`nextrel1` が `le0` を含むので算術）
    `k戻り >= 2` は **0 件**（§R299/§R300 と同じ）
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

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def scan(QS, tag, DS=(1, 2, 3, 4), ES=(0, 1, 2), NS=(1, 2, 3)):
    G = {}; ex = []
    for Q in QS:
        L = len(Q); span = min(Q[i][0] - Q[0][0] for i in range(1, L))
        for d in DS:
            for e in ES:
                for n in NS:
                    T = mTower(Q, d, e, n) + [Lift1(sh(Q, d * n), e * n)[0]]
                    t = len(T) - 1
                    sr = srow(T, t)
                    if sr < 1: continue
                    c = trio.parent(T, sr, t)
                    if c is None: continue
                    c0 = trio.parent(T, 0, t)
                    kb = n - (c // L)
                    keys = ['★ 全', 'srow=%d' % sr,
                            '★ d<=段差' if d <= span else '⛔ d>段差',
                            ('★ d<=段差' if d <= span else '⛔ d>段差') + ' / srow=%d' % sr,
                            'e=0' if e == 0 else 'e>0']
                    for kk in keys:
                        g = G.setdefault(kk, Counter()); g['n'] += 1
                        g['★ 第 n-1 ブロック内'] += (c >= (n - 1) * L and c < n * L)
                        g['⛔ k>=2'] += (kb >= 2)
                        g['⛔ 同ブロック'] += (c >= n * L)
                        g['行0 親なし'] += (c0 is None)
                        if c0 is not None:
                            g['★ c = c0（同じ列）'] += (c == c0)
                            g['★ c < c0（もっと前）'] += (c < c0)
                            g['⛔ c > c0（行0の親より後ろ）'] += (c > c0)
                    if (kb >= 2 or (c0 is not None and c > c0)) and len(ex) < 4:
                        ex.append((Q, d, e, n, c, c0, kb, span, sr))
    print('  [%s]' % tag)
    print('     %-22s %8s %15s %10s %12s %14s %16s' % (
        '群', '分母', '★第n-1ブロック内', '⛔ k>=2', '★ c = c0', '★ c < c0', '⛔ c > c0'))
    for kk in ('★ 全', 'srow=1', 'srow=2', '★ d<=段差', '⛔ d>段差',
               '★ d<=段差 / srow=1', '⛔ d>段差 / srow=1', '⛔ d>段差 / srow=2', 'e=0', 'e>0'):
        g = G.get(kk)
        if not g: continue
        m = g['n']
        print('     %-22s %8d %14.4f%% %9.4f%% %11.4f%% %13.4f%% %15.4f%%'
              % (kk, m, pct(g['★ 第 n-1 ブロック内'], m), pct(g['⛔ k>=2'], m),
                 pct(g['★ c = c0（同じ列）'], m), pct(g['★ c < c0（もっと前）'], m),
                 pct(g['⛔ c > c0（行0の親より後ろ）'], m)))
    g = G.get('★ 全')
    if g: print('     ⚠ 検算: 同ブロック %d 件 / 行0 親なし %d 件' % (g['⛔ 同ブロック'], g['行0 親なし']))
    for e in ex:
        print('     ⛔ 例外: Q=%s d=%d e=%d n=%d srow=%d ⟹ c=%s c0=%s k戻り=%d 段差=%d'
              % (' '.join('(%d,%d,%d)' % q for q in e[0]), e[1], e[2], e[3], e[8], e[4], e[5], e[6], e[7]))
    if not ex: print('     ★ 例外（`k>=2` または `c > c0`）は **0 件**')
    return G


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
scan(ART4, '⛔ 負の対照: 人工 4 列 %d 本' % len(ART4), DS=(1, 2, 3, 4), ES=(0, 1), NS=(2, 3))
print('（%.1f 秒）' % (time.time() - t0))
