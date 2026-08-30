# -*- coding: utf-8 -*-
"""**(R-C5) —— 「親は直前のブロック以降」を、定理にできる形まで細かく。**

## ⚠ 測る対象

    `S_j := mTower Q d e n ++ B.take (j+1)`、`B := Lift1 (shiftr01 (d*n) 0 Q) (e*n)`
    末尾 `t = n*|Q| + j`、親 `p = parent S_j (srow S_j t) t`
    **`k戻り := n - (p // |Q|)`**（0 = 同ブロック、1 = 直前、2 以上 = 塔の奥）
    **オフセット := `p % |Q|`**（0 = そのブロックの根）

## ⚠ 母集団

    Reach の窓（`Wtower2.W_drop` `:2870` ＋ `Wset.W_take`、健全）の狭義 `hr0` な `Q`、`2 <= |Q| <= 6`、標本 400 本
    ⛔ 負の対照: 人工 3 列・4 列（`W` でない）
    `d ∈ {0,1,2,3}`、`e ∈ {0,1,2}`、`n ∈ {1,2,3}`。**所属の判定はしません**。
    ⚠ **`d=0` / `e=0` は必ず別に集計**。⚠ **`|Q|` 別にも出す**。

## ⚠ 測る前の見積もり

    `k >= 2` は **0 件**（§R297 と同じ）。⟹ ★ `|Q|`・`d`・`e` を振っても 0 のはず。
    `j = 0` の親のオフセット: 根（0）が 53.83%、残りは **ブロックの末尾寄り**と見ます。
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


def scan(QS, DS, ES, NS, tag):
    G = {}; OFF = {}; ex = []
    for Q in QS:
        L = len(Q)
        for d in DS:
            for e in ES:
                for n in NS:
                    T = mTower(Q, d, e, n); B = Lift1(sh(Q, d * n), e * n)
                    for j in range(L):
                        S = T + B[:j + 1]; t = len(S) - 1
                        sr = srow(S, t); p = trio.parent(S, sr, t)
                        if p is None: continue
                        kb = n - (p // L); off = p % L
                        keys = ['全', 'd=0' if d == 0 else 'd>0', 'e=0' if e == 0 else 'e>0',
                                '|Q|=%d' % L, 'j=0' if j == 0 else 'j>0']
                        for kk in keys:
                            g = G.setdefault(kk, Counter()); g['n'] += 1
                            g['k=0 同ブロック'] += (kb == 0)
                            g['k=1 直前'] += (kb == 1)
                            g['⛔ k>=2 塔の奥'] += (kb >= 2)
                        if kb >= 2 and len(ex) < 5:
                            ex.append((Q, d, e, n, j, p, kb))
                        if j == 0 and kb == 1:
                            o = OFF.setdefault('j=0 直前ブロック内のオフセット', Counter())
                            o['オフセット %s' % (off if off <= 3 else '>=4')] += 1
                            o['末尾（= |Q|-1）'] += (off == L - 1)
                            o['n'] += 1
                            o2 = OFF.setdefault('j=0 / srow=%d' % sr, Counter())
                            o2['n'] += 1; o2['根（0）'] += (off == 0); o2['末尾'] += (off == L - 1)
    print('  [%s]' % tag)
    print('     %-12s %9s %13s %11s %14s' % ('群', '分母', 'k=0 同ブロック', 'k=1 直前', '⛔ k>=2 塔の奥'))
    for kk in ('全', 'j=0', 'j>0', 'd=0', 'd>0', 'e=0', 'e>0', '|Q|=2', '|Q|=3', '|Q|=4', '|Q|=5', '|Q|=6'):
        g = G.get(kk)
        if not g: continue
        m = g['n']
        print('     %-12s %9d %12.4f%% %10.4f%% %13.4f%%'
              % (kk, m, pct(g['k=0 同ブロック'], m), pct(g['k=1 直前'], m), pct(g['⛔ k>=2 塔の奥'], m)))
    o = OFF.get('j=0 直前ブロック内のオフセット')
    if o:
        m = o['n']
        print('     ⟹ ★ `j=0` で親が直前ブロックのとき、そのブロック内のオフセット（分母 %d）:' % m)
        for k in ('オフセット 0', 'オフセット 1', 'オフセット 2', 'オフセット 3', 'オフセット >=4'):
            if k in o: print('        %-16s %7d  %8.4f%%' % (k, o[k], pct(o[k], m)))
        print('        %-16s %7d  %8.4f%%' % ('（うち末尾）', o['末尾（= |Q|-1）'], pct(o['末尾（= |Q|-1）'], m)))
    for kk in sorted(k for k in OFF if k.startswith('j=0 / srow')):
        o = OFF[kk]
        print('     　%s: 分母 %d、根 %.4f%% / 末尾 %.4f%%' % (kk, o['n'], pct(o['根（0）'], o['n']), pct(o['末尾'], o['n'])))
    for (Q, d, e, n, j, p, kb) in ex:
        print('     ⛔⛔ 塔の奥の例: Q=%s d=%d e=%d n=%d j=%d ⟹ 親=%d（%d ブロック前）'
              % (' '.join('(%d,%d,%d)' % q for q in Q), d, e, n, j, p, kb))
    if not ex: print('     ★ `k >= 2` は **0 件**')
    return G


t0 = time.time()
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
QS = [Q for Q in windows([list(x) for x in RC], cap=60000) if 2 <= len(Q) <= 6 and hr0s(Q)]
random.seed(0); random.shuffle(QS); QS = QS[:400]
scan(QS, (0, 1, 2, 3), (0, 1, 2), (1, 2, 3), 'Reach の窓（健全）/ `Q` %d 本' % len(QS))
COL = [(a, b, z) for a in range(1, 5) for b in range(0, 4) for z in (0, 1)]
ART3 = [[(0, v, z)] + list(t) for v in (0, 1, 2) for z in (0, 1) for t in itertools.product(COL, repeat=2)]
scan(ART3, (0, 1, 2, 3), (0, 1, 2), (1, 2, 3), '⛔ 負の対照: 人工 3 列 %d 本' % len(ART3))
ART4 = [[(0, v, z)] + list(t) for v in (0, 1) for z in (0, 1) for t in itertools.product(COL[:16], repeat=3)]
scan(ART4, (1, 2), (0, 1), (2, 3), '⛔ 負の対照: 人工 4 列 %d 本' % len(ART4))
print('（%.1f 秒）' % (time.time() - t0))
