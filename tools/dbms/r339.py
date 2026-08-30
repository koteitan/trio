# -*- coding: utf-8 -*-
"""**(R-C19) —— (W91a) の機構の裏取り。`c` のオフセットは「行 1 が根より低い列の最大添字」か。**

## ⚠ 鍵（`Trio.lean:49` 逐語）

    def nextrel1 (M) (j0 j1) := … ∧ entry M 1 j0 < entry M 1 j1 ∧ le0 M j0 j1 ∧
      (**∀ j, j0 < j ∧ le0 M j j1 → entry M 1 j1 <= entry M 1 j**)
    ⟹ ★★★ **`j0` は「行 1 が的より小さい `le0` 祖先のうち、添字が最大のもの」**

## ⚠ 母集団（規則 9）

    **`j = 0` ∧ `srow(T,t) = 1` ∧ `e = 0` ∧ `d > 段差` ∧ 親あり**（(R-C15) と同じ、分母 714 / 387）
    `e = 0` なので **的の行 1 ＝ `entry Q 1 0`**（ブロック根は行 1 を持ち上げない）
    候補集合 **`S := {r | entry Q 1 r < entry Q 1 0}`**、主張は **`c % |Q| = max S`**
    `Q`: Reach の窓（健全）の狭義 `hr0` 400 本 ／ ⛔ 人工 3 列・4 列 400 本。`d ∈ {1..5}`、`n ∈ {1,2,3}`。
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
    c = Counter(); ex = []; noS = []
    for Q in QS:
        L = len(Q); sp = span(Q)
        S = [r for r in range(L) if Q[r][1] < Q[0][1]]
        for d in (1, 2, 3, 4, 5):
            if d <= sp: continue
            for n in (1, 2, 3):
                T = mTower(Q, d, 0, n) + [Lift1(sh(Q, d * n), 0)[0]]
                t = len(T) - 1
                if srow(T, t) != 1: continue
                cc = trio.parent(T, 1, t)
                if cc is None:
                    c['孤児'] += 1
                    c['  うち S が空'] += (not S)
                    continue
                c['★ 親あり（分母）'] += 1
                c['(3) ⛔ S が空なのに親あり'] += (not S)
                if not S and len(noS) < 3: noS.append((Q, d, n, cc))
                r = cc % L
                if S:
                    c['★ (1) r = max S'] += (r == max(S))
                    c['⛔ (1) r ≠ max S'] += (r != max(S))
                    if r != max(S) and len(ex) < 4: ex.append((Q, d, n, cc, r, max(S), S))
                c['★ (2) ブロック n-1'] += (cc // L == n - 1)
                c['⛔ (2) 別のブロック'] += (cc // L != n - 1)
                c['★ (4) hlow'] += ((trio.parent(T, 0, t) is not None) and T[trio.parent(T, 0, t)][1] < T[t][1])
                c['(4) c0 なし'] += (trio.parent(T, 0, t) is None)
    m = c['★ 親あり（分母）']
    print('  [%s] 親あり %d（孤児 %d、うち `S` が空 %d）' % (tag, m, c['孤児'], c['  うち S が空']))
    if not m: return c
    print('     ★★★ (1) `r = max S`: %d / %d = **%.4f%%**（⛔ ずれ %d 件）'
          % (c['★ (1) r = max S'], c['★ (1) r = max S'] + c['⛔ (1) r ≠ max S'],
             pct(c['★ (1) r = max S'], c['★ (1) r = max S'] + c['⛔ (1) r ≠ max S']), c['⛔ (1) r ≠ max S']))
    print('     ★ (2) ブロック `n-1`: %.4f%%（⛔ 別 %d 件）' % (pct(c['★ (2) ブロック n-1'], m), c['⛔ (2) 別のブロック']))
    print('     ★ (3) ⛔ `S` が空なのに親あり: **%d 件 = %.4f%%**' % (c['(3) ⛔ S が空なのに親あり'], pct(c['(3) ⛔ S が空なのに親あり'], m)))
    print('     ★ (4) `hlow`（この 714 件の中）: %.4f%%（`c0` なし %d 件）' % (pct(c['★ (4) hlow'], m), c['(4) c0 なし']))
    for e in ex: print('     ⛔ (1) のずれ: Q=%s d=%d n=%d c=%d r=%d max S=%d S=%s'
                       % (' '.join('(%d,%d,%d)' % q for q in e[0]), e[1], e[2], e[3], e[4], e[5], e[6]))
    for e in noS: print('     ⛔ (3) `S` 空なのに親あり: Q=%s d=%d n=%d c=%d'
                        % (' '.join('(%d,%d,%d)' % q for q in e[0]), e[1], e[2], e[3]))
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
