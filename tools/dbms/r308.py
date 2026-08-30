# -*- coding: utf-8 -*-
"""**(LT-1) 決定打 —— 最小核 4 件は、既存の緑定理だけで届くか。**

## `Reach+` の作り方（**健全**、すべて既存の緑定理）

    種   `D_v`（`Om_mem_W`）
    (i)  `oper_closed`  : `M ∈ W u → M⟦n⟧ ∈ W u`
    (ii) `W_take`       : 接頭辞
    (iii)`W_dropLast`
    (iv) **持ち上げ 4 本**（仮定ゼロ）: `X ∈ W m ⟹ Lift1 X d ∈ W (m + 2d)`、
         ただし `X = (0,v,z)::R` が次のどれか
           1 狭義    `∀ p ∈ R, v < p.2.1`        （`L53.liftStage_of_strict`）
           2 無タイ  `∀ p ∈ R, p.2.1 ≠ v`        （`L53.liftStage_of_noTie`）
           3 TieFree `1 <= v ∧ TieFree X`        （`L53.liftTie_case_tieFree`）
           4 行2≡0   `∀ p ∈ X, p.2.2 = 0`        （`L105.liftStage_of_zeroRow2`）

⟹ ★ `Reach+ ⊆ W` は**健全**。⟹ **標的が `Reach+` に入れば、その核事例は既に証明できます**。
⛔ 入らなくても `∉ W` ではありません（下からの近似）。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r113 import Lift1
from r260 import reach
from r111 import tiefree

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def green(X):
    """4 本の仮定ゼロ持ち上げ定理のどれかが当たるか。"""
    if not X or X[0][0] != 0: return None
    R = X[1:]; v = X[0][1]
    if all(p[2] == 0 for p in X): return '4 行2≡0'
    if not all(p[0] > 0 for p in R): return None       # argOK（1,2 が要求）
    if all(v < p[1] for p in R): return '1 狭義'
    if all(p[1] != v for p in R): return '2 無タイ'
    if v >= 1 and tiefree(list(X)): return '3 TieFree'
    return None


def build(seeds, ns, rounds, cap):
    S = set(seeds)
    for rd in range(rounds):
        new = set()
        for X in list(S):
            if len(S) + len(new) > cap: break
            g = green(list(X))
            if g:
                for d in (1, 2):
                    L = tuple(tuple(q) for q in Lift1(list(X), d))
                    if L not in S: new.add(L)
        S |= new
        # oper 閉包 ＋ 接頭辞
        new2 = set()
        for X in list(S):
            if len(S) + len(new2) > cap: break
            for n in ns:
                try: T = tuple(tuple(q) for q in trio.expand([list(q) for q in X], n))
                except Exception: continue
                if T and T not in S: new2.add(T)
        for T in list(new2):
            for k in range(1, len(T) + 1): new2.add(T[:k])
        S |= new2
        print('   round %d: |Reach+| = %d' % (rd + 1, len(S)))
    return S


t0 = time.time()
seeds = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    seeds |= reach(vs, ns, depth)
print('種 |Reach| = %d' % len(seeds))
SP = build(seeds, (1, 2, 3), rounds=3, cap=400000)
print('|Reach+| = %d（%.1f 秒）' % (len(SP), time.time() - t0))

targets = [
    [(0, 0, 0), (1, 1, 1), (2, 0, 0)],
    [(0, 0, 0), (1, 1, 1), (2, 0, 0), (3, 1, 1)],
    [(0, 0, 0), (1, 1, 1), (2, 0, 0), (3, 1, 1), (4, 0, 0)],
    [(0, 0, 0), (1, 1, 1), (2, 0, 0), (3, 1, 1), (4, 0, 0), (5, 1, 1)],
]
print()
print('== 最小核 4 件の標的が Reach+ に入るか ==')
for X in targets:
    L = tuple(tuple(q) for q in Lift1(X, 1))
    inX = tuple(tuple(q) for q in X) in SP
    print('   X=%s (Reach+ に X: %s)' % (' '.join('(%d,%d,%d)' % q for q in X), inX))
    print('     標的 Lift1 X 1 = %s  ⟹ %s'
          % (' '.join('(%d,%d,%d)' % q for q in L), '★★★ Reach+ に入る（既に証明できる）' if L in SP else '⚠ Reach+ に無い（未定）'))

print()
print('== Reach+ 全体で、核の場面はどれくらい残るか（v=0）==')
c = Counter()
for X in SP:
    X = list(X)
    if len(X) < 2 or X[0] != (0, 0, 0): continue
    R = X[1:]
    if not all(p[0] > 0 for p in R): continue
    c['argOK'] += 1
    if all(p[1] > 0 for p in R): c['1 狭義/無タイ（緑）'] += 1; continue
    if all(p[2] == 0 for p in X): c['4 行2≡0（緑）'] += 1; continue
    c['★ 核'] += 1
    L = tuple(tuple(q) for q in Lift1(X, 1))
    if L in SP: c['★★ 標的が Reach+ に入る'] += 1
n = c['argOK']
for k in ('argOK', '1 狭義/無タイ（緑）', '4 行2≡0（緑）', '★ 核', '★★ 標的が Reach+ に入る'):
    print('   %-26s %7d  %7.4f%%' % (k, c[k], pct(c[k], n)))
print('   ⟹ 核のうち標的が届くもの: %.4f%%' % pct(c['★★ 標的が Reach+ に入る'], c['★ 核']))
