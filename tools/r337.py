# -*- coding: utf-8 -*-
"""**(R-C17) —— `j > 0` ∧ `srow = 2` で `|V| >= |Q|` が起きる条件は何か。**

## ⚠ 測る対象

    `T := mTower Q d e n ++ B.take (j+1)`（`B` ＝ 第 `n` ブロック）、`t := |T|-1`、`c := parent T (srow T t) t`
    **`V := T[c:t]`**、⛔ **`|V| >= |Q|`（窓が縮まない）** が起きる手を集める
    候補: **(1) `d <= 段差`** ／ **(2) 狭義 `hr0`** ／ **(3) `Q ∈ W`（健全な箱か）**

## ⚠ 箱の固定条件（規則 9）—— **人工を広げます**

    ★ 健全: Reach の窓（`W_drop` ＋ `W_take`）の狭義 `hr0`、`2 <= |Q| <= 6`、標本 400 本
    ⛔ 人工 A: 3 列（`hr0` あり / なし の両方）
    ⛔ 人工 B: **4 列**（`hr0` あり / なし の両方）
    **`d ∈ {1,..,5}`**、`e ∈ {0,1,2}`、`n ∈ {1,2,3}`、**`j ∈ [1, |Q|)`**、**`srow(T,t) = 2` に絞る**
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
from r329 import span

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def scan(QS, tag, sound):
    c = Counter(); bad = []
    for Q in QS:
        L = len(Q); sp = span(Q); h = hr0s(Q)
        for d in (1, 2, 3, 4, 5):
            for e in (0, 1, 2):
                for n in (1, 2, 3):
                    B = Lift1(sh(Q, d * n), e * n); T0 = mTower(Q, d, e, n)
                    for j in range(1, L):
                        T = T0 + B[:j + 1]; t = len(T) - 1
                        if srow(T, t) != 2: continue
                        cc = trio.parent(T, 2, t)
                        if cc is None: c['孤児'] += 1; continue
                        c['★ srow=2 ∧ 親あり'] += 1
                        V = T[cc:t]
                        if len(V) >= L:
                            c['⛔ |V| >= |Q|'] += 1
                            c['　うち d<=段差'] += (d <= sp)
                            c['　うち 狭義hr0'] += h
                            c['　うち 健全（Q∈W）'] += sound
                            if len(bad) < 400: bad.append((tuple(Q), d, e, n, j, sp, h, len(V), L))
                        else: c['★ |V| < |Q|'] += 1
    m = c['★ srow=2 ∧ 親あり']
    b = c['⛔ |V| >= |Q|']
    print('  [%s] `j>0` ∧ `srow=2` ∧ 親あり: %d（孤児 %d）' % (tag, m, c['孤児']))
    print('     ⛔ `|V| >= |Q|`: **%d 件 = %.4f%%**' % (b, pct(b, m)))
    if b:
        print('       うち **`d <= 段差`**: %d 件 = %.4f%%' % (c['　うち d<=段差'], pct(c['　うち d<=段差'], b)))
        print('       うち **狭義 `hr0`**: %d 件 = %.4f%%' % (c['　うち 狭義hr0'], pct(c['　うち 狭義hr0'], b)))
        print('       うち **健全（`Q ∈ W`）**: %d 件 = %.4f%%' % (c['　うち 健全（Q∈W）'], pct(c['　うち 健全（Q∈W）'], b)))
        seen = set()
        for (Q, d, e, n, j, sp, h, lv, L) in bad:
            if Q in seen: continue
            seen.add(Q)
            if len(seen) > 4: break
            print('       ⛔ 逐語: Q=%s（段差=%d, hr0=%s）d=%d e=%d n=%d j=%d ⟹ |V|=%d >= |Q|=%d'
                  % (' '.join('(%d,%d,%d)' % q for q in Q), sp, h, d, e, n, j, lv, L))
    return c


t0 = time.time()
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
QS = [Q for Q in windows([list(x) for x in RC], cap=60000) if 2 <= len(Q) <= 6 and hr0s(Q)]
random.seed(0); random.shuffle(QS)
scan(QS[:400], '★ 健全: Reach の窓 400 本（狭義 hr0）', True)

COL = [(a, b, z) for a in range(1, 5) for b in range(0, 4) for z in (0, 1)]
A3 = [[(0, v, z)] + list(t) for v in (0, 1, 2) for z in (0, 1) for t in itertools.product(COL, repeat=2)]
random.seed(0); random.shuffle(A3)
scan([Q for Q in A3 if hr0s(Q)][:400], '⛔ 人工 3 列 400 本（狭義 hr0）', False)
scan([Q for Q in A3 if not hr0s(Q)][:400], '⛔ 人工 3 列 400 本（`hr0` なし）', False)
COL4 = [(a, b, z) for a in range(1, 4) for b in range(0, 3) for z in (0, 1)]
A4 = [[(0, v, z)] + list(t) for v in (0, 1) for z in (0, 1) for t in itertools.product(COL4, repeat=3)]
random.seed(0); random.shuffle(A4)
scan([Q for Q in A4 if hr0s(Q)][:400], '⛔ 人工 4 列 400 本（狭義 hr0）', False)
scan([Q for Q in A4 if not hr0s(Q)][:400], '⛔ 人工 4 列 400 本（`hr0` なし）', False)
print('（%.1f 秒）' % (time.time() - t0))
