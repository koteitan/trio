# -*- coding: utf-8 -*-
"""**(ROW2-5)(NC-1) —— 行 2 が一定か、0 と 1 が混ざっているか。**

## ⚠ 2 つは表裏です

    L3 の `mTowerClosedS_of_nonconst`（§301、緑）: **行 2 が一定な `Q` は即終了**
    ⟹ 残核 ＝ **行 2 が非一定** ＝ **`z <= 1` なら「0 の列と 1 の列が両方ある」**
    ⟹ ★ (ROW2-5)「一定は何 %」と (NC-1)「混在は何 %」は **足して 100%** です。

## ⚠ 母集団（**正規化の罠 5 回目を踏まえ、根が上がる箱を必ず入れる**）

    (i) シート行列そのもの（1,637 本）      … 根は `(0,0,0)` のみ
    (ii) ★ **シートの窓 `M[j:k]`**          … `W_drop`（`Wtower2:2870`）＋ `W_take`、**健全**、根が上がる
    (iii) Reach 行列そのもの
    (iv) ★ **Reach の窓**
    (v) ⛔ 負の対照: 人工総当たり（`W` でない）

    **残差 B** := `hr0 Q` ∧ `|Q| >= 2` ∧ `srow(末尾) >= 1` ∧ **`¬ hasParent Q (srow) (|Q|-1)`**
    ⚠ `W` の判定は不要（列の条件だけ）。

## ⚠ 測る前の見積もり

    残差 B の中で「行 2 が一定」は **10〜30%** と見ます
    （残差は行 2 に非零を含むので、一定なら全列 1。長い `Q` では起きにくいはず）。
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r263 import load
from r126 import srow
from r260 import reach
from r315 import windows, hr0s

pct = lambda a, b: 100.0 * a / b if b else float('nan')
const2 = lambda Q: len(set(p[2] for p in Q)) == 1
mixed2 = lambda Q: (0 in set(p[2] for p in Q)) and any(p[2] > 0 for p in Q)


def orphan(Q):
    j = len(Q) - 1
    return trio.parent(Q, srow(Q, j), j) is None


def scan(QS, tag):
    G = {}; ex = {}
    for Q in QS:
        if len(Q) < 2: continue
        s = srow(Q, len(Q) - 1)
        res = hr0s(Q) and s >= 1 and orphan(Q)
        keys = ['全']
        if res: keys += ['★ 残差B', '★ 残差B srow=%d' % s]
        elif hr0s(Q) and s >= 1: keys += ['⚠ 対照（親あり）']
        for kk in keys:
            g = G.setdefault(kk, Counter())
            g['n'] += 1
            g['★ 行2が一定'] += const2(Q)
            g['  うち全部 0'] += (const2(Q) and Q[0][2] == 0)
            g['  うち全部 1'] += (const2(Q) and Q[0][2] > 0)
            g['⛔ 行2が混在(NC-1)'] += mixed2(Q)
            g['末尾行1 = 根'] += (Q[-1][1] == Q[0][1])
        if res and mixed2(Q):
            ex.setdefault('mix', []).append(Q)
    print('  [%s]' % tag)
    print('     %-20s %8s %11s %10s %10s %14s %12s' % (
        '群', '分母', '★行2が一定', '全部0', '全部1', '⛔行2が混在', '末尾行1=根'))
    for kk in ('全', '★ 残差B', '★ 残差B srow=1', '★ 残差B srow=2', '⚠ 対照（親あり）'):
        g = G.get(kk)
        if not g: continue
        n = g['n']
        print('     %-20s %8d %10.4f%% %9.4f%% %9.4f%% %13.4f%% %11.4f%%'
              % (kk, n, pct(g['★ 行2が一定'], n), pct(g['  うち全部 0'], n), pct(g['  うち全部 1'], n),
                 pct(g['⛔ 行2が混在(NC-1)'], n), pct(g['末尾行1 = 根'], n)))
    # 混在かつ残差の中で「末尾が根とタイ」
    g = G.get('★ 残差B')
    if g:
        mm = Counter()
        for Q in ex.get('mix', []):
            mm['n'] += 1
            mm['末尾行1 = 根'] += (Q[-1][1] == Q[0][1])
            mm['srow=%d' % srow(Q, len(Q) - 1)] += 1
        if mm['n']:
            print('     ⟹ ★★ 本当の残核（残差B ∧ 行2混在）: %d 件、末尾行1=根 %.4f%%、srow=1 %.4f%% / srow=2 %.4f%%'
                  % (mm['n'], pct(mm['末尾行1 = 根'], mm['n']), pct(mm['srow=1'], mm['n']), pct(mm['srow=2'], mm['n'])))
        for Q in sorted(ex.get('mix', []), key=len)[:3]:
            print('       ★ 最小例: |Q|=%d srow=%d  %s' % (len(Q), srow(Q, len(Q) - 1), ' '.join('(%d,%d,%d)' % q for q in Q)))
    return G


t0 = time.time()
SH = [[tuple(v) for v in M] for M in load()]
scan([M for M in SH], '(i) シート行列そのもの %d 本' % len(SH))
scan(list(windows(SH)), '(ii) ★ シートの窓（健全 W_drop+W_take）')
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
scan([list(x) for x in RC], '(iii) Reach 行列そのもの %d 本' % len(RC))
scan(list(windows([list(x) for x in RC], cap=200000)), '(iv) ★ Reach の窓（健全）')
COL = [(a, b, z) for a in range(0, 4) for b in range(0, 3) for z in (0, 1)]
scan([list(t) for t in itertools.product(COL, repeat=3)], '(v) ⛔ 負の対照: 人工 3 列')
print('（%.1f 秒）' % (time.time() - t0))
