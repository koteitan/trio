# -*- coding: utf-8 -*-
"""**(R-C14) —— `d > 段差` の枝。等号（`|V| = |Q|`）で何が起きるか。＋ `j > 0` の 1 行確認。**

## ⚠ 測る対象

    `T := mTower Q d e n ++ B.take (j+1)`、`t := |T|-1`、`c := parent T (srow T t) t`
    `V := T[c:t]`、**`d' := entry T 0 t - entry T 0 c`（`0<sr`）**、**`e' := entry T 1 t - entry T 1 c`（`1<sr`）**
    **段差(X) := `min_{i>=1}(entry X 0 i - entry X 0 0)`**

## ⚠ 問い

    `j = 0` ∧ **`d > 段差(Q)`** の手を 3 つに分ける:
      (a) **孤児** ⟹ 無料 ／ (b) **`|V| < |Q|`** ⟹ 長さが減る ／ (c) **`|V| = |Q|`（等号）**
    (c) で: **(1) `(e,d)` が減るか ／ (2) 段差(V) はどうなるか ／ (3) `d' <= 段差(V)` に入るか**
    ＋ **`j > 0` は `|V| < |Q|` が本当に狭義か**（H12 の `window_lt_of_blockInner` の 1 行確認）

## ⚠ 箱の固定条件（規則 9）

    Reach の窓（`W_drop` ＋ `W_take`、健全）の狭義 `hr0` な `Q` 400 本（`2 <= |Q| <= 6`）
    ⛔ 負の対照 人工 3 列 400 本（狭義 `hr0`）。**`d ∈ {1,2,3,4}`**（規則 8）、`e ∈ {0,1,2}`、`n ∈ {1,2,3}`。
    **所属の判定はしません**。
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


def scan(QS, tag):
    G = {}; H = Counter(); ex = []
    for Q in QS:
        L = len(Q); sp = span(Q)
        for d in (1, 2, 3, 4):
            for e in (0, 1, 2):
                for n in (1, 2, 3):
                    B = Lift1(sh(Q, d * n), e * n)
                    T0 = mTower(Q, d, e, n)
                    # ---- j = 0、d > 段差 ----
                    if d > sp:
                        T = T0 + B[:1]; t = len(T) - 1
                        sr = srow(T, t); c = trio.parent(T, sr, t)
                        g = G.setdefault('全（j=0, d>段差）', Counter()); g['n'] += 1
                        if c is None: g['(a) 孤児 ⟹ 無料'] += 1
                        else:
                            V = T[c:t]
                            if len(V) < L: g['(b) |V| < |Q| ⟹ 長さ減'] += 1
                            elif len(V) == L:
                                g['(c) |V| = |Q|（等号）'] += 1
                                d2 = (T[t][0] - T[c][0]) if sr > 0 else 0
                                e2 = (T[t][1] - T[c][1]) if sr > 1 else 0
                                sp2 = span(V) if len(V) >= 2 else 0
                                H['n'] += 1
                                H['★ (e,d) 狭義減少'] += ((e2, d2) < (e, d))
                                H['⛔ (e,d) 減らない'] += ((e2, d2) >= (e, d))
                                H['段差が同じ'] += (sp2 == sp)
                                H['★ 段差が増えた'] += (sp2 > sp)
                                H['⛔ 段差が減った'] += (sp2 < sp)
                                H["★★ 次段で d' <= 段差(V) に入る"] += (d2 <= sp2)
                                H['srow=%d' % sr] += 1
                                if (e2, d2) >= (e, d) and len(ex) < 3:
                                    ex.append((Q, d, e, n, sr, d2, e2, sp, sp2))
                            else: g['⛔ |V| > |Q|（あり得ないはず）'] += 1
                    # ---- j > 0 の 1 行確認 ----
                    for j in range(1, L):
                        T = T0 + B[:j + 1]; t = len(T) - 1
                        sr = srow(T, t); c = trio.parent(T, sr, t)
                        g = G.setdefault('全（j>0）', Counter()); g['n'] += 1
                        if c is None: g['孤児'] += 1
                        else:
                            V = T[c:t]
                            g['★ |V| < |Q|（狭義）'] += (len(V) < L)
                            g['⛔ |V| >= |Q|'] += (len(V) >= L)
    print('  [%s]' % tag)
    g = G.get('全（j=0, d>段差）', Counter()); m = g['n']
    print('     == `j = 0` ∧ `d > 段差`（分母 %d）==' % m)
    for kk in ('(a) 孤児 ⟹ 無料', '(b) |V| < |Q| ⟹ 長さ減', '(c) |V| = |Q|（等号）', '⛔ |V| > |Q|（あり得ないはず）'):
        if g[kk] or kk.startswith('⛔'):
            print('        %-28s %8d  %8.4f%%' % (kk, g[kk], pct(g[kk], m)))
    if H['n']:
        h = H['n']
        print('     == (c) 等号 %d 件の中身 ==' % h)
        for kk in ('★ (e,d) 狭義減少', '⛔ (e,d) 減らない', '段差が同じ', '★ 段差が増えた', '⛔ 段差が減った',
                   "★★ 次段で d' <= 段差(V) に入る", 'srow=0', 'srow=1', 'srow=2'):
            print('        %-32s %8d  %8.4f%%' % (kk, H[kk], pct(H[kk], h)))
    g2 = G.get('全（j>0）', Counter()); m2 = g2['n']
    print('     == `j > 0`（分母 %d）==' % m2)
    print('        孤児 %.4f%% ／ ★ `|V| < |Q|`（狭義）%.4f%% ／ ⛔ `|V| >= |Q|` %d 件'
          % (pct(g2['孤児'], m2), pct(g2['★ |V| < |Q|（狭義）'], m2 - g2['孤児']), g2['⛔ |V| >= |Q|']))
    for (Q, d, e, n, sr, d2, e2, sp, sp2) in ex:
        print('     ⛔ 等号で (e,d) 減らない: Q=%s d=%d e=%d n=%d srow=%d ⟹ (e,d)=(%d,%d)→(%d,%d) 段差 %d→%d'
              % (' '.join('(%d,%d,%d)' % q for q in Q), d, e, n, sr, e, d, e2, d2, sp, sp2))


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
