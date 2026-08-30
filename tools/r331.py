# -*- coding: utf-8 -*-
"""**(R-C10) —— 測度の第 2 成分は `d` か。`(e, d)` の辞書式で止まるか。**

## ★★★★★ 機構（`oper` の逐語、`Trio.lean:106-114`）

    `d' := if 0 < sr then entry T 0 t - entry T 0 c else 0`
    `e' := if 1 < sr then entry T 1 t - entry T 1 c else 0`
    ⟹ ★ **`sr = 2`** … `d'`, `e'` とも実差
    ⟹ ★ **`sr = 1`** … **`e' = 0`**（`e` が落ちる）
    ⟹ ★ **`sr = 0`** … **`d' = 0` かつ `e' = 0`**（両方落ちる）
    ⟹ ⟹ ★★★ そして **`d = 0` ⟹ ブロック根が塔の根と同じ行 0 ⟹ 孤児 ⟹ 終了**

⟹ ★ ですから候補は **`(e, d)` の辞書式**。⟹ 全数で確認する。

## ⚠ 母集団

    Reach の窓（健全）200 本 ／ ⛔ 人工 3 列・4 列 各 200 本 ／ ★ 段差 >= 2 の人工 150 本
    `d0 <= min(段差,4)`、`e0 ∈ {0..4}`、`n0, k ∈ {1..4}`、15 段。**所属の判定はしません**。
"""
import sys, itertools, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, sh, mTower
from r260 import reach
from r315 import windows, hr0s
from r329 import step, span

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def run(QS, tag, DS=None, ES=(0, 1, 2, 3, 4), NS=(1, 2, 3, 4)):
    c = Counter(); ex = []
    for Q0 in QS:
        sp0 = span(Q0)
        for d0 in (DS or range(1, min(sp0, 4) + 1)):
            if d0 > sp0: continue
            for e0 in ES:
                for n0 in NS:
                    for k in NS:
                        Q, d, e, n = Q0, d0, e0, n0
                        for i in range(15):
                            st, lab, sr, cc = step(Q, d, e, n)
                            if st is None: break
                            Q2, d2, e2 = st
                            c['遷移'] += 1
                            c['srow=%d' % sr] += 1
                            c['★ e 非増加'] += (e2 <= e)
                            c['★★ (e,d) 辞書式で狭義減少'] += ((e2, d2) < (e, d))
                            c['  うち e が減'] += (e2 < e)
                            c['  うち e 同 ∧ d が減'] += (e2 == e and d2 < d)
                            c['⛔ (e,d) が減らない'] += ((e2, d2) >= (e, d))
                            c['|Q| 一定'] += (len(Q2) == len(Q))
                            if (e2, d2) >= (e, d) and len(ex) < 4:
                                ex.append((Q, d, e, n, sr, Q2, d2, e2))
                            Q, d, e, n = Q2, d2, e2, k
    m = c['遷移']
    print('  [%s] 遷移 %d 回' % (tag, m))
    for kk in ('★ e 非増加', '★★ (e,d) 辞書式で狭義減少', '  うち e が減', '  うち e 同 ∧ d が減',
               '⛔ (e,d) が減らない', '|Q| 一定'):
        print('     %-28s %8d  %9.4f%%' % (kk, c[kk], pct(c[kk], m)))
    print('     srow の内訳: 0 が %.4f%% / 1 が %.4f%% / 2 が %.4f%%'
          % (pct(c['srow=0'], m), pct(c['srow=1'], m), pct(c['srow=2'], m)))
    for (Q, d, e, n, sr, Q2, d2, e2) in ex:
        print('     ⛔ 減らない例: (e,d)=(%d,%d) ⟹ (%d,%d) srow=%d n=%d  Q=%s'
              % (e, d, e2, d2, sr, n, ' '.join('(%d,%d,%d)' % q for q in Q[:6])))
    if not ex: print('     ★ 「減らない」遷移は **0 件**')
    return c


t0 = time.time()
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
QS = [Q for Q in windows([list(x) for x in RC], cap=200000) if 2 <= len(Q) <= 12 and hr0s(Q)]
random.seed(1); random.shuffle(QS)
run(QS[:200], 'Reach の窓 200 本（健全）')
COL = [(a, b, z) for a in range(1, 5) for b in range(0, 4) for z in (0, 1)]
ART3 = [[(0, v, z)] + list(t) for v in (0, 1, 2) for z in (0, 1) for t in itertools.product(COL, repeat=2)]
random.shuffle(ART3); run(ART3[:200], '⛔ 人工 3 列 200 本')
ART4 = [[(0, v, z)] + list(t) for v in (0, 1) for z in (0, 1) for t in itertools.product(COL[:16], repeat=3)]
random.shuffle(ART4); run(ART4[:200], '⛔ 人工 4 列 200 本')
COL2 = [(a, b, z) for a in range(2, 6) for b in range(0, 4) for z in (0, 1)]
BIG = [[(0, v, z)] + list(t) for v in (0, 1, 2) for z in (0, 1) for t in itertools.product(COL2, repeat=2)]
BIG = [Q for Q in BIG if span(Q) >= 2]; random.shuffle(BIG)
run(BIG[:150], '★ 段差>=2 の人工 150 本')
print('（%.1f 秒）' % (time.time() - t0))
