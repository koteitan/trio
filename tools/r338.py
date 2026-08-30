# -*- coding: utf-8 -*-
"""**(R-C18) —— 最後の角: `j=0` ∧ `srow=2` ∧ `d>段差` ∧ `e>0` ∧ 親あり で 窓 < `|Q|` か。**

## ⚠ なぜこの角だけ残るか

    `srow = 2` では **`e' := entry T 1 t - entry T 1 c` が実差** ⟹ ⛔ **`e` が増えうる**
    ⟹ ★ ですから **第 1 成分（`|Q|`）が減るしかない** ⟹ ★★ **窓 < `|Q|` が要る**

## ⚠ 箱の固定条件（規則 9）

    `T := mTower Q d e n ++ [第 n ブロックの根]`（**`j = 0`**）、`t := |T|-1`、`c := parent T 2 t`
    **`srow(T,t) = 2` ∧ `d > 段差` ∧ `e > 0` ∧ `c` が存在**
    `Q`: ★ Reach の窓（`W_drop` ＋ `W_take`、健全）の狭義 `hr0`、`2 <= |Q| <= 6`、標本 400 本
    ⛔ 負の対照: 人工 3 列・4 列 各 400 本（狭義 `hr0`）
    **`d ∈ {1,...,5}`**（規則 8）、**`e ∈ {1,2,3}`**、`n ∈ {1,2,3}`。**所属の判定はしません**。

## ⚠ 測る前の見積もり

    §R300: **`j = 0` では 窓 <= `|Q|` が無条件 100%** ／ §R310: **等号は `srow = 1` のみ**
    ⟹ ★ **窓 < `|Q|` が 100%** と見ます（＝ 穴なし）。
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
    c = Counter(); ex = []; eq = []
    for Q in QS:
        L = len(Q); sp = span(Q)
        for d in (1, 2, 3, 4, 5):
            if d <= sp: continue                     # ★ d > 段差
            for e in (1, 2, 3):                      # ★ e > 0
                for n in (1, 2, 3):
                    T = mTower(Q, d, e, n) + [Lift1(sh(Q, d * n), e * n)[0]]
                    t = len(T) - 1
                    if srow(T, t) != 2: continue     # ★ srow = 2
                    c['srow=2 の手'] += 1
                    cc = trio.parent(T, 2, t)
                    if cc is None: c['孤児（無料）'] += 1; continue
                    c['★ 親あり（分母）'] += 1
                    win = t - cc; off = cc % L
                    c['★ 窓 < |Q|'] += (win < L)
                    c['⛔ 窓 = |Q|'] += (win == L)
                    c['⛔ 窓 > |Q|'] += (win > L)
                    c['オフセット %s' % (off if off <= 3 else '>=4')] += 1
                    c['ブロック n-%d' % (n - cc // L)] += 1
                    if win == L:
                        d2 = T[t][0] - T[cc][0]; e2 = T[t][1] - T[cc][1]
                        c['等号: e が増'] += (e2 > e); c['等号: (e,d) 減'] += ((e2, d2) < (e, d))
                        if len(eq) < 3: eq.append((Q, d, e, n, cc, d2, e2, sp))
                    if win > L and len(ex) < 4: ex.append((Q, d, e, n, cc, win, L, sp))
    m = c['★ 親あり（分母）']
    print('  [%s] `srow=2` ∧ `d>段差` ∧ `e>0` の手 %d（孤児 %d = %.4f%%）'
          % (tag, c['srow=2 の手'], c['孤児（無料）'], pct(c['孤児（無料）'], c['srow=2 の手'])))
    print('     ★ 親あり（分母）= %d' % m)
    if m:
        print('        ★★★ **窓 < `|Q|`**: %d = **%.4f%%**' % (c['★ 窓 < |Q|'], pct(c['★ 窓 < |Q|'], m)))
        print('        ⛔ 窓 = `|Q|`: %d = %.4f%%' % (c['⛔ 窓 = |Q|'], pct(c['⛔ 窓 = |Q|'], m)))
        print('        ⛔ 窓 > `|Q|`: %d = %.4f%%' % (c['⛔ 窓 > |Q|'], pct(c['⛔ 窓 > |Q|'], m)))
        print('        オフセット: ' + ' / '.join('%s: %.4f%%' % (k[6:], pct(c[k], m))
                                              for k in ('オフセット 0', 'オフセット 1', 'オフセット 2', 'オフセット 3', 'オフセット >=4') if c[k]))
        print('        ブロック: ' + ' / '.join('%s: %.4f%%' % (k, pct(c[k], m))
                                            for k in sorted(k for k in c if k.startswith('ブロック'))))
        if c['⛔ 窓 = |Q|']:
            print('        等号のとき: `e` が増 %d 件 / `(e,d)` 減 %d 件' % (c['等号: e が増'], c['等号: (e,d) 減']))
        for e_ in eq: print('        ⚠ 等号の例:', e_)
        for e_ in ex: print('        ⛔⛔ 窓 > |Q| の逐語:', e_)
        if not ex: print('        ★ 窓 > `|Q|` は **0 件**')
    return c


t0 = time.time()
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
QS = [Q for Q in windows([list(x) for x in RC], cap=60000) if 2 <= len(Q) <= 6 and hr0s(Q)]
random.seed(0); random.shuffle(QS)
scan(QS[:400], '★ 健全: Reach の窓 400 本（狭義 hr0）')
COL = [(a, b, z) for a in range(1, 5) for b in range(0, 4) for z in (0, 1)]
A3 = [[(0, v, z)] + list(t) for v in (0, 1, 2) for z in (0, 1) for t in itertools.product(COL, repeat=2)]
random.seed(0); random.shuffle(A3)
scan([Q for Q in A3 if hr0s(Q)][:400], '⛔ 負の対照: 人工 3 列 400 本')
COL4 = [(a, b, z) for a in range(1, 4) for b in range(0, 3) for z in (0, 1)]
A4 = [[(0, v, z)] + list(t) for v in (0, 1) for z in (0, 1) for t in itertools.product(COL4, repeat=3)]
random.seed(0); random.shuffle(A4)
scan([Q for Q in A4 if hr0s(Q)][:400], '⛔ 負の対照: 人工 4 列 400 本')
print('（%.1f 秒）' % (time.time() - t0))
