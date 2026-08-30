# -*- coding: utf-8 -*-
"""**(LT-1) —— `LiftTieCoreRow2` の「前提が本物」の最小事例を探す。**

## 逐語（`L105Cap.lean:2074`）

    def LiftTieCoreRow2 : Prop :=
      ∀ (v z : N) (R : TrioSeq), argOK R → (∃ p ∈ R, p.2.1 = v) →
        ¬ (1 <= v ∧ TieFree (((0, v, z)) :: R)) →
        (∃ p ∈ (((0, v, z)) :: R), 0 < p.2.2) →
        (((0, v, z)) :: R) ∈ W (2 * v + z) →
        Lift1 (((0, v, z)) :: R) 1 ∈ W (2 * v + z + 2)

## ⚠ なぜ `Reach` を使うか

    ★ **`Reach ⊆ W` は健全**（`Om_mem_W` ＋ `oper_closed` ＋ 接頭辞閉包）
    ⟹ `X ∈ Reach` なら **前提 `X ∈ W (2v+z)` は本物**（`W_root_stage` で段は自己段）
    ⛔ ですが `Reach` の元の根は必ず `(0,0,0)` ⟹ **`v = 0` の核しか作れません**
      （§R306 の空振りの原因。`Lift1 X 1` の根は `(0,1,0)` なので `Reach` に入るはずが無い）
    ⟹ ★ `v = 0` なら `¬(1 <= v ∧ TieFree)` は**自動成立** ⟹ 前提は 4 本とも確認できます

⟹ ★★ **出力は「前提が全部確かめられた、本物の残核事例」**。L3/H12 はこれを直接攻めればよい。
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


def collect(vs, ns, depth):
    RS = reach(vs, ns, depth)
    c = Counter(); core = []
    for X in RS:
        X = list(X)
        if len(X) < 2 or X[0] != (0, 0, 0): continue
        R = X[1:]
        c['根が (0,0,0)'] += 1
        if not all(p[0] > 0 for p in R): continue
        c['argOK R'] += 1
        strict = all(p[1] > 0 for p in R)          # 狭義（v=0 なので 0 < p[1]）
        tie = any(p[1] == 0 for p in R)
        row2 = any(p[2] > 0 for p in X)
        if strict: c['1 狭義（緑）'] += 1; continue
        if not tie: c['2 無タイ（緑）'] += 1; continue
        # v = 0 ⟹ ¬(1<=v ∧ TieFree) は自動
        if not row2: c['4 行2≡0（緑）'] += 1; continue
        c['★ 5 核（LiftTieCoreRow2）'] += 1
        core.append(tuple(X))
    return c, core


print('== `v = 0` の残核: 前提が全部確かめられた事例 ==')
allcore = set(); tot = Counter()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5),
                      ((1, 2, 3, 4), (1, 2, 3, 4), 5),
                      ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6),
                      ((1, 2, 3, 4, 5, 6, 7, 8), (1, 2), 6)):
    c, core = collect(vs, ns, depth)
    n = c['argOK R']
    print('  [Reach v<=%d ns=%s d%d] argOK %6d | 狭義 %6.2f%% 無タイ %6.2f%% 行2≡0 %6.2f%% | ★ 核 %6.2f%%（%d 件）'
          % (vs[-1], ns, depth, n, pct(c['1 狭義（緑）'], n), pct(c['2 無タイ（緑）'], n),
             pct(c['4 行2≡0（緑）'], n), pct(c['★ 5 核（LiftTieCoreRow2）'], n), c['★ 5 核（LiftTieCoreRow2）']))
    allcore.update(core)
    for k, v in c.items(): tot[k] += v

print()
print('  ★ 相異なる核事例: %d 件' % len(allcore))
srt = sorted(allcore, key=lambda X: (len(X), max(p[0] for p in X), max(p[1] for p in X)))
print()
print('== ★★★★★ 最小の核事例（L3/H12 が直接攻める的）==')
for X in srt[:8]:
    L = Lift1(list(X), 1)
    print('   |X|=%d  X = %s' % (len(X), ' '.join('(%d,%d,%d)' % q for q in X)))
    print('           R の行 1 = 0 の列: %s' % [i for i, q in enumerate(X) if i > 0 and q[1] == 0])
    print('           ⟹ 示すべき: Lift1 X 1 = %s ∈ W 2' % ' '.join('(%d,%d,%d)' % q for q in L))
print()
print('== 核事例の形（%d 件）==' % len(allcore))
cc = Counter()
for X in allcore:
    cc['|X| = %d' % min(len(X), 9)] += 1
    cc['行 1 = 0 の列が 1 本'] += (sum(1 for q in X[1:] if q[1] == 0) == 1)
    cc['行 2 = 1 の列が 1 本'] += (sum(1 for q in X if q[2] > 0) == 1)
    cc['タイ列が最終列'] += (X[-1][1] == 0)
    cc['タイ列が行 2 正'] += any(q[1] == 0 and q[2] > 0 for q in X[1:])
n = len(allcore)
for k in sorted(cc):
    print('   %-22s %6d  %7.4f%%' % (k, cc[k], pct(cc[k], n)))
