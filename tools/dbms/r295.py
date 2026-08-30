# -*- coding: utf-8 -*-
"""**(PCO-2) ＋ (PCO-1) —— `PrefixCopiesOpen`（`L53Subst:3801`）。**

## ⚠ 定義（逐語）

    PrefixCopiesOpen := ∀ u n A Q, A ∈ W u → Q ∈ W u →
      **(∀ q ∈ Q, entry Q 0 0 ≤ q.1)**        -- (P1) `Q` の全列が `Q` の根以上
      → **(∃ q ∈ A, q.1 < entry Q 0 0)**       -- (P2) `A` に `Q` の根より浅い列がある（★ 開いている側）
      → A ++ (Q を n 個並べたもの) ∈ W u        -- ★ 持ち上げ 0

## (PCO-2) 実際の場面で「開いている側」にどれくらい落ちるか

    場面 ＝ **`A = C.take j0`、`Q = C.drop j0`**（`L105Cap §20.3`）
    ⟹ ★ **`j0` ごとに (P1)(P2) がそれぞれ何 %** か。⟹ **`j0 = 0` は自明に閉じるはず**。

## (PCO-1) 反例探索

    ★ `Reach ⊆ W`（健全）を使い、**`A`・`Q` がともに `Reach` の元**で (P1)(P2) を満たすものを取り、
      **`A ++ Q^n` が `Reach` に入るか**を見る。
    ⚠ **`Reach` は下からの近似**なので、「入らない」は **`∉ W` の証明にはなりません**。
    ⟹ ★ ですから **非単調な穴**（`n` で入ったり入らなかったり）を手がかりにします。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r263 import load
from r260 import reach


def pco2():
    c = Counter(); ex = []
    for C in load():
        X = [tuple(v) for v in C]
        for j0 in range(0, len(X)):
            A = X[:j0]; Q = X[j0:]
            if not Q: continue
            p1 = all(Q[0][0] <= q[0] for q in Q)
            p2 = any(q[0] < Q[0][0] for q in A)
            c['★ 分母（C, j0）'] += 1
            c[f'   j0={min(j0,3)} 分母'] += 1
            if p1: c[f'   j0={min(j0,3)} (P1) 真'] += 1
            if p2: c[f'   j0={min(j0,3)} (P2) 真'] += 1
            if p1 and p2:
                c['⛔ **(P1)∧(P2) ＝ 開いている側**'] += 1
                c[f'   j0={min(j0,3)} ★開いている'] += 1
                if len(ex) < 3: ex.append((X, j0, A, Q))
            elif p1:
                c['★ (P1) だが (P2) 偽 ＝ `rsum` が通る（無料）'] += 1
    d = c['★ 分母（C, j0）']
    print(f'### (PCO-2) シート 1,637 行列  ★ 分母（C, j0）{d}')
    print(f'   ⛔ **(P1)∧(P2) ＝ 開いている側** {c["⛔ **(P1)∧(P2) ＝ 開いている側**"]} '
          f'({100*c["⛔ **(P1)∧(P2) ＝ 開いている側**"]/max(d,1):8.4f}%)')
    print(f'   ★ (P1) だが (P2) 偽（無料） {c["★ (P1) だが (P2) 偽 ＝ `rsum` が通る（無料）"]} '
          f'({100*c["★ (P1) だが (P2) 偽 ＝ `rsum` が通る（無料）"]/max(d,1):8.4f}%)')
    print('   ★★ `j0` 別（j0>=3 はまとめて）:')
    for k in ('0', '1', '2', '3'):
        dd = c[f'   j0={k} 分母']
        if not dd: continue
        print(f'      j0={k}: 分母 {dd:7d}  (P1) {100*c[f"   j0={k} (P1) 真"]/dd:7.3f}%  '
              f'(P2) {100*c[f"   j0={k} (P2) 真"]/dd:7.3f}%  '
              f'⛔ **開いている** {100*c[f"   j0={k} ★開いている"]/dd:7.3f}%')
    for x in ex:
        print(f'      ⛔ 開いている例: C={x[0][:6]}... j0={x[1]} A={x[2][:4]} Q={x[3][:4]}')
    print()


def pco1():
    t0 = time.time()
    for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4), (1, 2, 3), 6)):
        R = reach(vs, ns, depth)
        RS = set(R)
        c = Counter(); ex = []
        Rl = [list(x) for x in R if 2 <= len(x) <= 5]
        for Q in Rl[:200]:
            if not all(Q[0][0] <= q[0] for q in Q): continue      # (P1)
            for A in Rl[:200]:
                if not any(q[0] < Q[0][0] for q in A): continue   # (P2)
                if len(A) + 3 * len(Q) > 30: continue
                c['★ (P1)∧(P2) を満たす (A,Q)'] += 1
                pat = []
                for n in (1, 2, 3):
                    L = tuple(tuple(v) for v in A) + \
                        tuple(tuple(v) for v in Q) * n
                    pat.append(L in RS)
                c[f'   Reach 所属パターン n=1,2,3: {tuple(pat)}'] += 1
                if pat[0] and not pat[1] and len(ex) < 3:
                    ex.append((A, Q))
        print(f'### (PCO-1) Reach(depth={depth}) |R|={len(R)}  [{time.time()-t0:.1f}s]')
        print(f'   ★ (P1)∧(P2) を満たす (A,Q) の組 {c["★ (P1)∧(P2) を満たす (A,Q)"]}')
        for k in sorted(c):
            if k.startswith('   Reach'): print(f'      {k}: {c[k]}')
        for x in ex:
            print(f'      ⚠ 非単調（n=1 は入り n=2 は入らない）: A={x[0]} Q={x[1]}')
        print()


if __name__ == '__main__':
    pco2()
    pco1()
