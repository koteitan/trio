# -*- coding: utf-8 -*-
"""**(R-C3)(R-C4) —— `TowerSnocStep` で足す列の親は、どこに落ちるか。**

## ⚠ 測る対象（定理の文と 1 対 1 に照合する。教訓 28）

    `S_j := mTower Q d e n ++ B.take j`、`B := Lift1 (shiftr01 (d*n) 0 Q) (e*n)`（＝ 第 `n` ブロック）
    足す列は `B[j]` ⟹ **`S_{j+1}` の末尾 `t = n*|Q| + j` の親の位置**を数える。
    `mTower Q d0 d1 n = (List.range n).flatMap fun k => Lift1 (shiftr01 (d0*k) 0 Q) (d1*k)`
                                                                （`L105Cap.lean:4177`、逐語）
    `Lift1` は **行 1** を、根の `le1` 錐の中だけ `+d`（`Wset.lean:927`、逐語）

## ⚠ 母集団（所属の判定はしません。`W` の健全な判定器は無い＝H56）

    `Q` は **`Reach` の窓 `M[j:k]`**（`Wtower2.W_drop` `:2870` ＋ `Wset.W_take`、健全）で
    **狭義 `hr0`** を満たすもの。`2 <= |Q| <= 6`、標本 400 本。`d,e ∈ {0,1,2}`、`n ∈ {1,2,3}`。
    ⟹ ★ **親の位置は計算するだけ**なので、健全性の心配は要りません。

## ⚠ 測る前の見積もり

    (1) `j = 0` … **親は前のブロックの根**が高い（`blockRoot_parent_prevBlock` が既に緑）
    (2) `0 < j` … **親は同じブロック内**が高いが、**例外が出る**
    (3) 親が塔（前のブロック群）に落ちる割合 … **小さいが 0 ではない** ⟹ そこが穴
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


def run(QS, DS, ES, NS, tag, detail=False):
    G = {}
    for Q in QS:
        L = len(Q)
        for d in DS:
            for e in ES:
                for n in NS:
                    T = mTower(Q, d, e, n)
                    B = Lift1(sh(Q, d * n), e * n)
                    for j in range(L):
                        S = T + B[:j + 1]
                        t = len(S) - 1
                        sr = srow(S, t)
                        p = trio.parent(S, sr, t)
                        keys = ['全', 'j=0' if j == 0 else 'j>0', 'n=%d' % n,
                                'e=0' if e == 0 else 'e>0']
                        for kk in keys:
                            g = G.setdefault(kk, Counter())
                            g['n'] += 1
                            g['srow=%d' % sr] += 1
                            if p is None:
                                g['⛔ 孤児'] += 1
                            elif p >= n * L:
                                g['★ 同じブロック内'] += 1
                            elif p >= (n - 1) * L:
                                g['★ 直前のブロック'] += 1
                                if j == 0 and p == (n - 1) * L: g['　うち直前ブロックの根'] += 1
                            else:
                                g['⛔ もっと前（塔の奥）'] += 1
                        if detail:
                            print('    d=%d e=%d n=%d j=%d ⟹ 末尾=%s srow=%d 親=%s (%s)'
                                  % (d, e, n, j, S[t], sr, p,
                                     '孤児' if p is None else
                                     ('同ブロック' if p >= n * L else
                                      ('直前ブロック' if p >= (n - 1) * L else '塔の奥'))))
    print('  [%s]' % tag)
    print('     %-10s %9s %13s %13s %10s %16s %10s' % (
        '群', '分母', '★同ブロック', '★直前ブロック', '⛔塔の奥', '⛔孤児', 'srow=2'))
    for kk in ('全', 'j=0', 'j>0', 'n=1', 'n=2', 'n=3', 'e=0', 'e>0'):
        g = G.get(kk)
        if not g: continue
        m = g['n']
        print('     %-10s %9d %12.4f%% %12.4f%% %9.4f%% %15.4f%% %9.4f%%'
              % (kk, m, pct(g['★ 同じブロック内'], m), pct(g['★ 直前のブロック'], m),
                 pct(g['⛔ もっと前（塔の奥）'], m), pct(g['⛔ 孤児'], m), pct(g['srow=2'], m)))
    g = G.get('j=0')
    if g:
        print('     ⟹ ★ `j=0` のうち **直前ブロックの根**が親: %.4f%%（%d / %d）'
              % (pct(g['　うち直前ブロックの根'], g['n']), g['　うち直前ブロックの根'], g['n']))
    return G


t0 = time.time()
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
QS = [Q for Q in windows([list(x) for x in RC], cap=60000) if 2 <= len(Q) <= 6 and hr0s(Q)]
random.seed(0); random.shuffle(QS)
QS = QS[:400]
print('== (R-C3) 母集団: Reach の窓（健全）から狭義 hr0 の `Q` %d 本 ==' % len(QS))
run(QS, (0, 1, 2), (0, 1, 2), (1, 2, 3), 'Reach の窓 / `Q` 400 本')

print()
print('== ★ (R-C4) 既知の 2 列残核 3 本（`d,e ∈ {1}`、`n ∈ {2,3}` を全部出す）==')
for Q in ([(3, 2, 1), (4, 1, 0)], [(7, 7, 1), (8, 7, 0)], [(5, 4, 0), (6, 3, 1)]):
    print('  ★ Q = %s（srow(末尾)=%d）' % (' '.join('(%d,%d,%d)' % q for q in Q), srow(Q, 1)))
    run([Q], (1,), (1,), (2, 3), '同上', detail=True)
print('（%.1f 秒）' % (time.time() - t0))
