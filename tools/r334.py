# -*- coding: utf-8 -*-
"""**(R-C13) —— H12 の (W88) の健全性チェック。`d <= 段差` ∧ `e = 0` で「親あり」は起きるか。**

## ⚠ H12 の (W88)（team-lead 経由、逐語）

    **`d <= 段差` ∧ `e = 0` ⟹ ブロック根に行 1 の親は無い**
    ⟹ ★ 正しければ **`d <= 段差` ∧ `e = 0` で「親あり」は 0 件**のはず

## ⚠ 私の箱の固定条件（規則 9。L3 の箱と違う可能性があるので明記）

    `Q`: **Reach の窓 `M[j:k]`**（`Wtower2.W_drop` `:2870` ＋ `Wset.W_take`、健全）で
         **狭義 `hr0`**（`∀ j, 1 <= j < |Q| → entry Q 0 0 < entry Q 0 j`）、`2 <= |Q| <= 6`、**標本 400 本**
    ⛔ 負の対照: 人工 3 列 400 本（`W` でない）
    **`d ∈ {1,2,3,4}`**、**`e = 0` に固定**、`n ∈ {1,2,3}`、**`j = 0`（ブロック根）**
    `T := mTower Q d 0 n ++ [第 n ブロックの根]`、`t := |T|-1`、`sr := srow T t`
    **`srow = 1` に絞る**（L3 の箱と同じ）
    **段差 := `min_{i>=1}(entry Q 0 i - entry Q 0 0)`**

## ⚠ 測る前の見積もり

    §R324 で **`e=0 / d<=段差` の孤児率は 95.5000%**（`srow` を混ぜた値）⟹ **4.5% が親あり**。
    ⟹ ⛔ **`srow = 1` に絞っても親ありが残るなら、(W88) は偽**と見ます。
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


def lowcol(T, t):
    """的より行 1 が低い列があるか（L3 の『低い列』）。"""
    return any(T[r][1] < T[t][1] for r in range(t))


def scan(QS, tag, DS=(1, 2, 3, 4)):
    G = {}; ex = []
    for Q in QS:
        sp = span(Q)
        for d in DS:
            for n in (1, 2, 3):
                T = mTower(Q, d, 0, n) + [Lift1(sh(Q, d * n), 0)[0]]
                t = len(T) - 1
                sr = srow(T, t)
                if sr != 1: continue                     # ★ L3 の箱: srow = 1
                c = trio.parent(T, sr, t)
                orp = c is None
                low = lowcol(T, t)
                keys = ['★ 全（e=0, ブロック根, srow=1, 狭義hr0）',
                        '★ d<=段差' if d <= sp else '⛔ d>段差', 'd=%d' % d]
                for kk in keys:
                    g = G.setdefault(kk, Counter()); g['n'] += 1
                    g['孤児'] += orp
                    g['⛔ 親あり'] += (not orp)
                    g['孤児 ∧ 低い列なし'] += (orp and not low)
                    g['孤児 ∧ 低い列あり'] += (orp and low)
                    g['⛔ 親あり ∧ 低い列なし'] += ((not orp) and not low)
                if (not orp) and d <= sp and len(ex) < 5:
                    ex.append((Q, d, n, sp, c, t))
    print('  [%s]' % tag)
    print('     %-34s %8s %10s %11s %16s %16s %20s' % (
        '群', '分母', '孤児', '⛔ 親あり', '孤児∧低い列なし', '孤児∧低い列あり', '⛔ 親あり∧低い列なし'))
    for kk in ('★ 全（e=0, ブロック根, srow=1, 狭義hr0）', '★ d<=段差', '⛔ d>段差', 'd=1', 'd=2', 'd=3', 'd=4'):
        g = G.get(kk)
        if not g: continue
        m = g['n']
        print('     %-34s %8d %9.4f%% %10.4f%% %15d %15d %19d'
              % (kk, m, pct(g['孤児'], m), pct(g['⛔ 親あり'], m),
                 g['孤児 ∧ 低い列なし'], g['孤児 ∧ 低い列あり'], g['⛔ 親あり ∧ 低い列なし']))
    g = G.get('★ d<=段差', Counter())
    print('     ⟹ ★★★ **`d <= 段差` で「親あり」は %d 件 / %d = %.4f%%**'
          % (g['⛔ 親あり'], g['n'], pct(g['⛔ 親あり'], g['n'])))
    for (Q, d, n, sp, c, t) in ex:
        print('     ⛔⛔ (W88) の反例: Q=%s  d=%d（段差=%d）e=0 n=%d ⟹ 的 t=%d 親=%d'
              % (' '.join('(%d,%d,%d)' % q for q in Q), d, sp, n, t, c))
    if not ex: print('     ★ `d <= 段差` の反例は **0 件** ⟹ (W88) は実測で裏づけ')
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
ART = [Q for Q in ART if hr0s(Q)]
random.seed(0); random.shuffle(ART)
scan(ART[:400], '⛔ 負の対照: 人工 3 列 400 本（狭義 hr0）')
print('（%.1f 秒）' % (time.time() - t0))
