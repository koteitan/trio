# -*- coding: utf-8 -*-
"""**(R-C6) —— `j = 0` ∧ `d > 0` ∧ **親がある** 手の中身。**

## ⚠ 測る対象

    `T := mTower Q d e n ++ [第 n ブロックの根]`、末尾 `t = n*|Q|`、`c := parent T (srow T t) t`
    **親がある手だけ**を分母にする（孤児は `snoc_orphan_W` が無料で引き取る ＝ 規則 7）。
    **オフセット := `c % |Q|`**（0 ＝ 直前ブロックの根）、**窓の長さ := `t - c` ＝ `n*|Q| - c`**
    ★ **段差 := `min_{i>=1}(entry Q 0 i - entry Q 0 0)`**

## ⚠ 母集団

    Reach の窓（`Wtower2.W_drop` `:2870` ＋ `Wset.W_take`、健全）の狭義 `hr0` な `Q` 400 本（`2 <= |Q| <= 6`）
    ⛔ 負の対照: 人工 3 列（`W` でない）。`d ∈ {1,2,3,4}`、`e ∈ {0,1,2}`、`n ∈ {1,2,3}`。
    ⚠ **`d <= 段差` / `d > 段差`、`e = 0` / `e > 0` を必ず分ける**。**所属の判定はしません**。

## ⚠ 測る前の見積もり

    (4) 窓の長さ <= `|Q|` は **100%**（`j=0` の親は必ず直前ブロック ⟹ `|Q| - オフセット <= |Q|`）
    (1) `srow = 2` はオフセット 0（根）が **0%**（§R299）
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


def scan(QS, tag, DS=(1, 2, 3, 4), ES=(0, 1, 2), NS=(1, 2, 3)):
    G = {}; ex = []
    for Q in QS:
        L = len(Q); span = min(Q[i][0] - Q[0][0] for i in range(1, L))
        for d in DS:
            for e in ES:
                for n in NS:
                    T = mTower(Q, d, e, n) + [Lift1(sh(Q, d * n), e * n)[0]]
                    t = len(T) - 1
                    sr = srow(T, t); c = trio.parent(T, sr, t)
                    if c is None: continue          # ★ 孤児は無料。分母から外す
                    off = c % L; win = t - c
                    keys = ['★ 親あり 全', 'srow=%d' % sr,
                            '★ d<=段差' if d <= span else '⛔ d>段差',
                            'e=0' if e == 0 else 'e>0',
                            ('★ d<=段差' if d <= span else '⛔ d>段差') + ' / srow=%d' % sr]
                    for kk in keys:
                        g = G.setdefault(kk, Counter()); g['n'] += 1
                        g['直前ブロックの根（off=0）'] += (off == 0)
                        g['直前ブロック内（off>0）'] += (off > 0 and c >= (n - 1) * L)
                        g['⛔ 同ブロック'] += (c >= n * L)
                        g['⛔ もっと前'] += (c < (n - 1) * L)
                        g['★ 窓 <= |Q|'] += (win <= L)
                        g['窓 = |Q|'] += (win == L)
                        g['off=1'] += (off == 1)
                        g['off=末尾'] += (off == L - 1)
                    if win > L and len(ex) < 3:
                        ex.append((Q, d, e, n, c, win, L))
    print('  [%s]' % tag)
    print('     %-22s %8s %14s %14s %10s %12s %11s' % (
        '群', '分母', '★直前根(off=0)', '直前ブロック内', 'off=1', '★窓<=|Q|', '窓=|Q|'))
    for kk in ('★ 親あり 全', 'srow=0', 'srow=1', 'srow=2', '★ d<=段差', '⛔ d>段差',
               '★ d<=段差 / srow=1', '★ d<=段差 / srow=2', '⛔ d>段差 / srow=1', '⛔ d>段差 / srow=2',
               'e=0', 'e>0'):
        g = G.get(kk)
        if not g: continue
        m = g['n']
        print('     %-22s %8d %13.4f%% %13.4f%% %9.4f%% %11.4f%% %10.4f%%'
              % (kk, m, pct(g['直前ブロックの根（off=0）'], m), pct(g['直前ブロック内（off>0）'], m),
                 pct(g['off=1'], m), pct(g['★ 窓 <= |Q|'], m), pct(g['窓 = |Q|'], m)))
    g = G.get('★ 親あり 全')
    if g:
        m = g['n']
        print('     ⚠ 検算: 同ブロック %d 件 / もっと前 %d 件（どちらも 0 のはず）'
              % (g['⛔ 同ブロック'], g['⛔ もっと前']))
        print('     ⟹ `srow` の内訳（親ありの中）: 0 が %.4f%% / 1 が %.4f%% / 2 が %.4f%%'
              % (pct(G.get('srow=0', Counter())['n'], m), pct(G.get('srow=1', Counter())['n'], m),
                 pct(G.get('srow=2', Counter())['n'], m)))
    for e in ex: print('     ⛔ 窓 > |Q| の例:', e)
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
scan(ART, '⛔ 負の対照: 人工 3 列 %d 本' % len(ART))
print()
print('== ★ `srow = 0` の形（216 件、全部に親がある）==')
c = Counter()
for Q in QS:
    L = len(Q); span = min(Q[i][0] - Q[0][0] for i in range(1, L))
    for d in (1, 2, 3, 4):
        for e in (0, 1, 2):
            for n in (1, 2, 3):
                T = mTower(Q, d, e, n) + [Lift1(sh(Q, d * n), e * n)[0]]
                t = len(T) - 1
                if srow(T, t) != 0: continue
                c['n'] += 1
                c['根が (x,0,0)'] += (Q[0][1] == 0 and Q[0][2] == 0)
                c['e=0'] += (e == 0)
                c['d<=段差'] += (d <= span)
                c['親=直前根'] += (trio.parent(T, 0, t) == (n - 1) * L)
print('   分母 %d | 根が (x,0,0) %.4f%% / e=0 %.4f%% / d<=段差 %.4f%% / 親=直前根 %.4f%%'
      % (c['n'], pct(c['根が (x,0,0)'], c['n']), pct(c['e=0'], c['n']), pct(c['d<=段差'], c['n']), pct(c['親=直前根'], c['n'])))
print('（%.1f 秒）' % (time.time() - t0))
