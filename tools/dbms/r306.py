# -*- coding: utf-8 -*-
"""**(LT-1) —— `LiftTieCoreZero`（`v=0` の残核）を `Reach` で実測する。**

## 逐語（`L105Cap.lean:4499`）

    def LiftTieCoreZero : Prop :=
      ∀ (R : TrioSeq), argOK R → (∃ p ∈ R, p.2.1 = 0) →
        (((0, 0, 0) : N x N x N) :: R) ∈ W 0 →
        Lift1 (((0, 0, 0) : N x N x N) :: R) 1 ∈ W 2

    `argOK R := ∀ p ∈ R, 0 < p.1`（`Wset.lean:1314`）

## ⚠ 方法と、その限界

    ★ **`Reach ⊆ W` は健全な下からの近似**（`reach` は `D_v` を `expand` で閉じたもの）
    ⟹ `X ∈ Reach` なら `X ∈ W` は**確か**。⟹ 前提は本物。
    ⛔ ですが `Lift1 X 1 ∉ Reach` は **`∉ W` の証明にはなりません**（下からの近似なので）。
    ⟹ ★ ですから「入る」は**陽性の証拠**、「入らない」は**未定**として報告します。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r113 import Lift1
from r260 import reach

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def run(vs, ns, depth):
    t0 = time.time()
    RS = reach(vs, ns, depth)
    S = set(RS)
    c = Counter(); ex = []
    for X in RS:
        X = list(X)
        if len(X) < 2: continue
        if X[0] != (0, 0, 0): continue
        R = X[1:]
        c['根が (0,0,0)'] += 1
        if not all(p[0] > 0 for p in R):
            c['⛔ argOK 破れ（除外）'] += 1; continue
        c['argOK R'] += 1
        if not any(p[1] == 0 for p in R):
            c['無タイ（既に緑）'] += 1; continue
        c['★ 核の場面（タイあり）'] += 1
        if all(p[2] == 0 for p in X):
            c['  うち 行2≡0（既に緑）'] += 1
        L = tuple(tuple(q) for q in Lift1(X, 1))
        if L in S:
            c['★★ Lift1 X 1 が Reach に入る'] += 1
        else:
            c['⚠ Lift1 X 1 は Reach に無い（未定）'] += 1
            if len(ex) < 4: ex.append((X, list(L)))
    print('== Reach v<=%d ns=%s depth=%d （%d 本、%.1f 秒）==' % (vs[-1], ns, depth, len(RS), time.time() - t0))
    n = c['★ 核の場面（タイあり）']
    for k in ('根が (0,0,0)', '⛔ argOK 破れ（除外）', 'argOK R', '無タイ（既に緑）',
              '★ 核の場面（タイあり）', '  うち 行2≡0（既に緑）',
              '★★ Lift1 X 1 が Reach に入る', '⚠ Lift1 X 1 は Reach に無い（未定）'):
        if k in c:
            print('   %-34s %8d  %s' % (k, c[k], ('%.4f%%' % pct(c[k], n)) if n and k.startswith(('★★', '⚠', '  ')) else ''))
    for (X, L) in ex:
        print('   ⚠ 例: X=%s' % (X[:8],))
        print('        Lift1 X 1=%s' % (L[:8],))
    return c


for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5),
                      ((1, 2, 3, 4), (1, 2, 3, 4), 5),
                      ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    run(vs, ns, depth)
    print()
