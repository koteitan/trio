# -*- coding: utf-8 -*-
"""**(INV-1) —— 「`W` の元では、根が行 1 で最小」は成り立つか。**

## ⚠ 逐語

    `Wtower2.W_drop`（`Wtower2.lean:2870`、緑）: `M ∈ W u → M.drop j ∈ W (lev M j)`
    `Wset.W_take`（`Wset.lean:2120`、緑）:      `M ∈ W u → M.take k ∈ W u`
    ⟹ ★ **窓 `M[j:k]` は健全な `W` の元**（根が `M[j]` なので **行 1 も行 2 も上がります**）

    `hr0 Q` := `∀ j, 1 ≤ j → j < |Q| → entry Q 0 0 < entry Q 0 j`

## 測る述語

    **(INV-1a)** `∀ j < |Q|, entry Q 1 0 ≤ entry Q 1 j`     … 根が行 1 で最小（全列）
    **(INV-1a-last)** 末尾だけ                                 … `entry Q 1 0 ≤ entry Q 1 (|Q|-1)`
    **(INV-1z)** `∀ j < |Q|, entry Q 2 0 ≤ entry Q 2 j`     … 行 2 版（(ROW2-7) の問い）

## ⚠ 測る前の見積もり

    ★ **`hr0` 無しでは破れる**と見ます（深い列から始まる窓は、あとで行 1 が下がる）。
      反例の形の予想: `M = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(2,1,0)` の `j=3` の窓 `(3,2,1)(2,1,0)`
      ⟹ 根の行 1 = 2 > 1 = 次の列の行 1。
    ★ **`hr0` ありでは破れない**と見ます（§R290 の 0 / 435,578 から）。
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r263 import load
from r126 import srow
from r260 import reach

pct = lambda a, b: 100.0 * a / b if b else float('nan')
hr0s = lambda Q: all(Q[0][0] < Q[j][0] for j in range(1, len(Q)))
inv1 = lambda Q: all(Q[0][1] <= Q[j][1] for j in range(len(Q)))
inv1L = lambda Q: Q[0][1] <= Q[-1][1]
inv2 = lambda Q: all(Q[0][2] <= Q[j][2] for j in range(len(Q)))
inv2L = lambda Q: Q[0][2] <= Q[-1][2]


def windows(MS, cap=None):
    seen = set()
    for M in MS:
        X = [tuple(v) for v in M]
        for j in range(len(X)):
            for k in range(j + 2, len(X) + 1):
                Q = tuple(X[j:k])
                if Q in seen: continue
                seen.add(Q); yield list(Q)
                if cap and len(seen) > cap: return


def scan(QS, tag, examples=2):
    G = {}; ex = {}
    for Q in QS:
        h = hr0s(Q)
        for key in ('全', 'hr0 あり' if h else '⛔ hr0 なし'):
            g = G.setdefault(key, Counter())
            g['n'] += 1
            g['(INV-1a) 根が行1で最小'] += inv1(Q)
            g['(INV-1a-last) 末尾だけ'] += inv1L(Q)
            g['(INV-1z) 根が行2で最小'] += inv2(Q)
            g['(INV-1z-last) 末尾だけ'] += inv2L(Q)
            g['根の行1 > 0'] += (Q[0][1] > 0)
            g['根の行2 > 0'] += (Q[0][2] > 0)
        if not inv1(Q) and ('a' not in ex or len(ex.get('a', [])) < examples):
            ex.setdefault('a', []).append((Q, h))
        if h and not inv1(Q) and len(ex.get('ah', [])) < examples:
            ex.setdefault('ah', []).append((Q, h))
        if h and not inv2(Q) and len(ex.get('zh', [])) < examples:
            ex.setdefault('zh', []).append((Q, h))
    print('  [%s]' % tag)
    print('     %-12s %8s %13s %12s %13s %12s | %9s %9s' % (
        '群', '分母', '★行1最小(全列)', '行1(末尾)', '★行2最小(全列)', '行2(末尾)', '根行1>0', '根行2>0'))
    for key in ('全', 'hr0 あり', '⛔ hr0 なし'):
        g = G.get(key)
        if not g: continue
        n = g['n']
        print('     %-12s %8d %12.4f%% %11.4f%% %12.4f%% %11.4f%% | %8.4f%% %8.4f%%'
              % (key, n, pct(g['(INV-1a) 根が行1で最小'], n), pct(g['(INV-1a-last) 末尾だけ'], n),
                 pct(g['(INV-1z) 根が行2で最小'], n), pct(g['(INV-1z-last) 末尾だけ'], n),
                 pct(g['根の行1 > 0'], n), pct(g['根の行2 > 0'], n)))
    for tagk, lbl in (('a', '⛔ 行1 の破れ（hr0 問わず）'), ('ah', '⛔⛔ 行1 の破れ（hr0 あり）'), ('zh', '⛔ 行2 の破れ（hr0 あり）')):
        for (Q, h) in ex.get(tagk, [])[:examples]:
            print('     %s: %s' % (lbl, ' '.join('(%d,%d,%d)' % q for q in Q[:8])))
    return G


t0 = time.time()
SH = [[tuple(v) for v in M] for M in load()]
print('== 1. シート由来（`W_drop` ＋ `W_take` で健全）==')
scan(list(windows(SH)), 'シートの窓 M[j:k]')
print('== 2. Reach 由来（健全）==')
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
scan(list(windows([list(x) for x in RC], cap=200000)), 'Reach の窓 %d 本' % len(RC))
print('== 3. ⛔ 負の対照: 人工総当たり（`W` でない）==')
COL = [(a, b, z) for a in range(0, 4) for b in range(0, 3) for z in (0, 1)]
ART = [list(t) for t in itertools.product(COL, repeat=3)]
scan(ART, '人工 3 列 %d 本' % len(ART))
print('（%.1f 秒）' % (time.time() - t0))
