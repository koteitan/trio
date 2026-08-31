# -*- coding: utf-8 -*-
"""**(R-C3')(R-C4) —— 塔にブロック根を 1 列 snoc したときの親の位置。**

## ⚠ 測る対象（定理の文と 1 対 1。教訓 28）

    `S := mTower Q d e n`（**`n` ブロック**、位置 `0 .. n*|Q|-1`）
    `p := 第 n ブロックの根` ＝ `Lift1 (shiftr01 (d*n) 0 Q) (e*n) [0]`（行 0 は `entry Q 0 0 + d*n`）
    `T := S ++ [p]`、末尾 `t = n*|Q|`
    **直前ブロックの根の位置 ＝ `(n-1)*|Q|`**

    `mTower Q d0 d1 n = (range n).flatMap fun k => Lift1 (shiftr01 (d0*k) 0 Q) (d1*k)`（`L105Cap:4177`）
    `Lift1` は **行 1** を根の `le1` 錐の中だけ `+d`（`Wset:927`）

## ⚠ 既存定理（grep 済み。教訓 25）

    `H12Export.blockRoot_parent_prevBlock`（`:484`）  `0<d ∧ 0<e ∧ k+1<n ∧ hr0` ∧ `nextrel1 (mTower…) a ((k+1)*|Q|)`
                                                    ⟹ `k*|Q| ≤ a`   ← ★ **塔の内部**の話（`k+1 < n`）
    `H12Export.blockRoot_parent_prevBlock_e_zero`（`:1193`） 同（`e = 0`）
    ⟹ ★ どちらも **行 1（`nextrel1`）の下界**。**snoc（`k+1 = n`）の場合は別**なので測る価値があります。

## ⚠ 母集団

    Reach の窓（`Wtower2.W_drop` `:2870` ＋ `Wset.W_take`、**健全**）で**狭義 `hr0`**、`2 <= |Q| <= 6`、標本 400 本。
    `d ∈ {0,1,2}`、`e ∈ {0,1,2}`、`n ∈ {0,1,2,3}`。
    ⚠⚠ **`d = 0` / `e = 0` / `n = 0` は必ず別に数える**。**所属の判定はしません**（親の位置の計算だけ）。

## ⚠ 測る前の見積もり

    `d > 0` … 行 0 の親 ＝ **直前ブロックの根**が **100%**（等差なので）
    `d = 0` … 全ブロック根が同じ行 0 ⟹ **行 0 の親なし**（＝ 孤児、`snoc_orphan_W` で無料）
"""
import sys, time, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, sh, mTower
from r260 import reach
from r315 import windows, hr0s

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def one(Q, d, e, n):
    L = len(Q)
    S = mTower(Q, d, e, n)
    p = Lift1(sh(Q, d * n), e * n)[0]
    T = S + [p]
    t = len(T) - 1
    return T, t, L


def run(QS, DS, ES, NS, tag, detail=0):
    G = {}; ex = []
    for Q in QS:
        for d in DS:
            for e in ES:
                for n in NS:
                    T, t, L = one(Q, d, e, n)
                    sr = srow(T, t)
                    p0 = trio.parent(T, 0, t); p1 = trio.parent(T, 1, t); p2 = trio.parent(T, 2, t)
                    prev = (n - 1) * L if n >= 1 else None
                    keys = ['全', 'n=%d' % n, 'd=0' if d == 0 else 'd>0', 'e=0' if e == 0 else 'e>0']
                    if n >= 1:
                        keys.append('★ n>=1 / d=0' if d == 0 else '★ n>=1 / d>0')
                        if d > 0: keys.append('★★ n>=1 ∧ d>0 / e=0' if e == 0 else '★★ n>=1 ∧ d>0 / e>0')
                    for kk in keys:
                        g = G.setdefault(kk, Counter()); g['n'] += 1
                        g['srow=%d' % sr] += 1
                        g['行0 親なし'] += (p0 is None)
                        g['★ 行0 親＝直前ブロックの根'] += (prev is not None and p0 == prev)
                        g['⛔ 行0 親＝別の場所'] += (p0 is not None and p0 != prev)
                        g['行1 親なし'] += (p1 is None)
                        g['★ 行1 親＝直前ブロックの根'] += (prev is not None and p1 == prev)
                        g['行2 親なし'] += (p2 is None)
                        g['★ 行2 親＝直前ブロックの根'] += (prev is not None and p2 == prev)
                        g['⛔ srow の親なし（孤児）'] += (trio.parent(T, sr, t) is None)
                    if n >= 1 and d > 0 and p0 is not None and p0 != prev and len(ex) < 4:
                        ex.append((Q, d, e, n, p0, prev))
                    if detail:
                        print('    d=%d e=%d n=%d ⟹ 末尾=%s srow=%d | 行0親=%s(直前根=%s) 行1親=%s 行2親=%s ⟹ %s'
                              % (d, e, n, T[t], sr, p0, prev, p1, p2,
                                 '孤児' if trio.parent(T, sr, t) is None else '親あり'))
    print('  [%s]' % tag)
    print('     %-22s %8s %14s %13s %12s %12s %12s' % (
        '群', '分母', '★行0親=直前根', '行0 親なし', '⛔行0 別', 'srow=1', '⛔ 孤児'))
    for kk in ('全', 'n=0', 'n=1', 'n=2', 'n=3', 'd=0', 'd>0', 'e=0', 'e>0',
               '★ n>=1 / d=0', '★ n>=1 / d>0', '★★ n>=1 ∧ d>0 / e=0', '★★ n>=1 ∧ d>0 / e>0'):
        g = G.get(kk)
        if not g: continue
        m = g['n']
        print('     %-22s %8d %13.4f%% %12.4f%% %11.4f%% %11.4f%% %11.4f%%'
              % (kk, m, pct(g['★ 行0 親＝直前ブロックの根'], m), pct(g['行0 親なし'], m),
                 pct(g['⛔ 行0 親＝別の場所'], m), pct(g['srow=1'], m), pct(g['⛔ srow の親なし（孤児）'], m)))
    g = G.get('★ n>=1 / d>0')
    if g:
        m = g['n']
        print('     ⟹ ★ `n>=1 ∧ d>0` の 行1: 親なし %.4f%% / 直前根 %.4f%% ｜ 行2: 親なし %.4f%% / 直前根 %.4f%%'
              % (pct(g['行1 親なし'], m), pct(g['★ 行1 親＝直前ブロックの根'], m),
                 pct(g['行2 親なし'], m), pct(g['★ 行2 親＝直前ブロックの根'], m)))
        print('     ⟹ ★ `n>=1 ∧ d>0` の srow: 0 が %.4f%% / 1 が %.4f%% / 2 が %.4f%%'
              % (pct(g['srow=0'], m), pct(g['srow=1'], m), pct(g['srow=2'], m)))
    for (Q, d, e, n, p0, prev) in ex:
        print('     ⛔ 例外: Q=%s d=%d e=%d n=%d ⟹ 行0親=%s（直前根=%s）'
              % (' '.join('(%d,%d,%d)' % q for q in Q), d, e, n, p0, prev))
    return G


t0 = time.time()
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
QS = [Q for Q in windows([list(x) for x in RC], cap=60000) if 2 <= len(Q) <= 6 and hr0s(Q)]
random.seed(0); random.shuffle(QS); QS = QS[:400]
print('== (R-C3\') 母集団: Reach の窓（健全）の狭義 hr0 な `Q` %d 本 ==' % len(QS))
run(QS, (0, 1, 2), (0, 1, 2), (0, 1, 2, 3), 'Reach の窓 / `Q` 400 本')

print()
print('== ★ (R-C4) `|Q| = 2` の残核 3 本を全部出す ==')
for Q in ([(3, 2, 1), (4, 1, 0)], [(7, 7, 1), (8, 7, 0)], [(5, 4, 0), (6, 3, 1)]):
    print('  ★ Q = %s' % ' '.join('(%d,%d,%d)' % q for q in Q))
    run([Q], (0, 1, 2), (0, 1), (1, 2, 3), '同上', detail=1)
print('（%.1f 秒）' % (time.time() - t0))
