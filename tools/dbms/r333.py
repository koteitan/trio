# -*- coding: utf-8 -*-
"""**(R-C12) —— 80.63% の正体は「的が `Q` の中で行 1 の最小」か。**

## ⚠ 逐語（教訓 25）

    `Cgraft.lean:848`  noncomputable def amin (A : TrioSeq) (j : ℕ) : ℕ :=
                         sInf {m | ∃ y, Relation.ReflTransGen (nextrel0 A) y j ∧ entry A 1 y = m}
    `L106.lean:8360`   theorem orphan_row1_iff_amin_eq (hj : j < M.length) :
                         **¬ hasParent M 1 j ↔ amin M j = entry M 1 j**
    `H12Export.lean:6590` theorem row1_min_of_orphan_and_no_low (hj : j < Q.length)
                         (horph : ¬ hasParent Q 1 j)
                         (hno : ∀ r, r < Q.length → entry Q 1 r < entry Q 1 j → le0 Q r j) :
                         **∀ r, r < Q.length → entry Q 1 j ≤ entry Q 1 r**

⟹ ★ 測る述語 **`row1min(Q) := ∀ r, entry Q 1 0 <= entry Q 1 r`**（的は `j = 0` ＝ ブロック根）

## ⚠ 母集団（§R298 と同じ）

    Reach の窓（`W_drop` ＋ `W_take`、健全）の狭義 `hr0` な `Q` 400 本（`2 <= |Q| <= 6`）
    ⛔ 負の対照: 人工 3 列。`d ∈ {1,2,3,4}`（規則 8）、`e ∈ {0,1,2}`、`n ∈ {1,2,3}`、**`j = 0`**。
    `T := mTower Q d e n ++ [第 n ブロックの根]`、孤児 := `parent T (srow T t) t is None`。
    ⚠ **`e = 0` / `e > 0`、`d <= 段差` / `d > 段差` を分ける**。**所属の判定はしません**。
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
row1min = lambda Q: all(Q[0][1] <= q[1] for q in Q)
# amin（逐語）: 行 0 の祖先鎖（reflexive）の行 1 の最小
def amin(A, j):
    out = A[j][1]; cur = j; seen = {j}
    while True:
        p = trio.parent(A, 0, cur)
        if p is None or p in seen: break
        seen.add(p); out = min(out, A[p][1]); cur = p
    return out


def scan(QS, tag):
    G = {}; ex = []
    for Q in QS:
        L = len(Q); sp = span(Q); rm = row1min(Q)
        for d in (1, 2, 3, 4):
            for e in (0, 1, 2):
                for n in (1, 2, 3):
                    T = mTower(Q, d, e, n) + [Lift1(sh(Q, d * n), e * n)[0]]
                    t = len(T) - 1
                    orp = trio.parent(T, srow(T, t), t) is None
                    keys = ['全', 'e=0' if e == 0 else 'e>0',
                            'd<=段差' if d <= sp else 'd>段差',
                            ('e=0' if e == 0 else 'e>0') + ' / ' + ('d<=段差' if d <= sp else 'd>段差')]
                    for kk in keys:
                        g = G.setdefault(kk, Counter()); g['n'] += 1
                        g['⛔ 孤児'] += orp
                        g['★ row1min(Q)'] += rm
                        g['★★ 一致（孤児 ⟺ row1min）'] += (orp == rm)
                        g['⛔ row1min だが親あり'] += (rm and not orp)
                        g['⛔ 孤児だが row1min でない'] += (orp and not rm)
                        # amin の検算（`orphan_row1_iff_amin_eq`）
                        g['amin 検算'] += ((trio.parent(T, 1, t) is None) == (amin(T, t) == T[t][1]))
                    if orp != rm and len(ex) < 3: ex.append((Q, d, e, n, orp, rm))
    print('  [%s]' % tag)
    print('     %-20s %9s %11s %14s %16s %18s' % (
        '群', '分母', '⛔ 孤児', '★ row1min(Q)', '★★ 一致', '⛔ row1min だが親あり'))
    for kk in ('全', 'e=0', 'e>0', 'd<=段差', 'd>段差',
               'e=0 / d<=段差', 'e=0 / d>段差', 'e>0 / d<=段差', 'e>0 / d>段差'):
        g = G.get(kk)
        if not g: continue
        m = g['n']
        print('     %-20s %9d %10.4f%% %13.4f%% %15.4f%% %17.4f%%'
              % (kk, m, pct(g['⛔ 孤児'], m), pct(g['★ row1min(Q)'], m),
                 pct(g['★★ 一致（孤児 ⟺ row1min）'], m), pct(g['⛔ row1min だが親あり'], m)))
    g = G['全']
    print('     ⚠ `orphan_row1_iff_amin_eq`（緑）の検算: %d / %d = %.4f%%'
          % (g['amin 検算'], g['n'], pct(g['amin 検算'], g['n'])))
    for (Q, d, e, n, orp, rm) in ex:
        print('     ⛔ 不一致: 孤児=%s row1min=%s d=%d e=%d n=%d  Q=%s'
              % (orp, rm, d, e, n, ' '.join('(%d,%d,%d)' % q for q in Q[:6])))
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
random.shuffle(ART)
scan(ART[:400], '⛔ 負の対照: 人工 3 列 400 本')
print('（%.1f 秒）' % (time.time() - t0))
