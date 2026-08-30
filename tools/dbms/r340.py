# -*- coding: utf-8 -*-
"""**(R-C19') —— `c` を一切見ずに、「直前ブロックに低い `le0` 祖先があるか」を測る。**

## ⚠ 循環を避ける（H12 の指摘、正しい）

    ⛔ (R-C19) の項目 (1) は **`c` を見て `c` の下界を測っていた** ⟹ **結論を仮定する形**
    ⟹ ★ ですから今回は **`c` を一切参照しません**。

## ★ 測る述語（H12 の `nextrel1_src_ge_prev_of_low_ancestor` の前提、逐語の形）

    **`LOW` := ∃ r ∈ [1, |Q|), `entry T 1 ((n-1)*|Q| + r) < entry T 1 t`
                              ∧ `le0 T ((n-1)*|Q| + r) t`**
    （＝ **直前ブロックの中に「行 1 が的より低い `le0` 祖先」がある**）
    ⟹ ★ **`c` を使わずに `T` の構造だけで判定できます**（`parent` を呼びません）

## ⚠ 母集団（規則 9）

    **`j = 0` ∧ `srow(T,t) = 1` ∧ `e = 0` ∧ `d > 段差`**、`d ∈ {1..5}`、`n ∈ {1,2,3}`
    ★ **親あり / 孤児 を分けて**出す（`parent` は**分類のためだけ**に使い、`LOW` の判定には使いません）
    `Q`: ★ Reach の窓（健全）の狭義 `hr0` 400 本 ／ ⛔ 人工 3 列・4 列 400 本
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
le0 = lambda T, y, j: trio.is_ancestor(T, 0, y, j)


def scan(QS, tag):
    c = Counter(); ex = []
    for Q in QS:
        L = len(Q); sp = span(Q)
        haslow = any(Q[r][1] < Q[0][1] for r in range(1, L))    # (2) `Q` に低い列があるか
        for d in (1, 2, 3, 4, 5):
            if d <= sp: continue
            for n in (1, 2, 3):
                T = mTower(Q, d, 0, n) + [Lift1(sh(Q, d * n), 0)[0]]
                t = len(T) - 1
                if srow(T, t) != 1: continue
                base = (n - 1) * L
                # ★★★ `c` を見ない判定
                LOW = any(T[base + r][1] < T[t][1] and le0(T, base + r, t) for r in range(1, L))
                # 分類のためだけに parent を呼ぶ
                cc = trio.parent(T, 1, t)
                key = '★ 親あり' if cc is not None else '孤児'
                for kk in ('全', key):
                    g = c.setdefault(kk, Counter()) if isinstance(c, dict) else None
                c['%s / n' % key] += 1
                c['%s / ★ LOW' % key] += LOW
                c['%s / ⛔ ¬LOW' % key] += (not LOW)
                c['%s / (2) Q に低い列あり' % key] += haslow
                if cc is not None:
                    c0 = trio.parent(T, 0, t)
                    c['★ 親あり / (3) hlow'] += (c0 is not None and T[c0][1] < T[t][1])
                if key == '★ 親あり' and not LOW and len(ex) < 4:
                    ex.append((Q, d, n, sp, haslow))
    a = c['★ 親あり / n']; o = c['孤児 / n']
    print('  [%s]' % tag)
    print('     ★ 親あり %d ／ 孤児 %d' % (a, o))
    if a:
        print('        ★★★ **`LOW`（直前ブロックに低い `le0` 祖先）**: %d = **%.4f%%**（⛔ ¬LOW %d 件）'
              % (c['★ 親あり / ★ LOW'], pct(c['★ 親あり / ★ LOW'], a), c['★ 親あり / ⛔ ¬LOW']))
        print('        ★ (2) `Q` に「行 1 が根より低い列」あり: %.4f%%' % pct(c['★ 親あり / (2) Q に低い列あり'], a))
        print('        ⛔ (3) `hlow`: %.4f%%' % pct(c['★ 親あり / (3) hlow'], a))
    if o:
        print('        ⚠ 対照（孤児 %d 件）: `LOW` %.4f%% ／ `Q` に低い列あり %.4f%%'
              % (o, pct(c['孤児 / ★ LOW'], o), pct(c['孤児 / (2) Q に低い列あり'], o)))
    for (Q, d, n, sp, hl) in ex:
        print('        ⛔ 親ありなのに ¬LOW: Q=%s（段差=%d、Q に低い列 %s）d=%d n=%d'
              % (' '.join('(%d,%d,%d)' % q for q in Q), sp, hl, d, n))
    if a and not ex: print('        ★ 「親ありなのに `¬LOW`」は **0 件**')
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
