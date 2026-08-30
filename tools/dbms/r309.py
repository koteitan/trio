# -*- coding: utf-8 -*-
"""**(ROW2-1)(ROW2-2)(ROW2-3) —— `MTowerClosedRow2` の本当の残差はどれくらいか。**

## ⚠ 逐語（`L105Cap.lean:5794`）

    def MTowerClosedRow2 : Prop :=
      ∀ (u d e n : N) (Q : TrioSeq), Q ∈ W u →
        (∀ j, 1 <= j → j < Q.length → entry Q 0 0 < entry Q 0 j) →   -- (a) 狭義 hr0
        (∃ p ∈ Q, 0 < p.2.2) →                                        -- (b) 行 2 に非零
        mTower Q d e n ∈ W u

    残差表（`L105Cap.lean:5836` §77.1）:
      n <= 1                      … 無料
      Q の行 2 ≡ 0                … 無料
      Q の末尾列が段内に親を持つ  … 1 文（MTowerStep）
      **Q の末尾列が段内で孤児**  … ★ 残差

    HasParentInBlock N := hasParent N (srow N (N.length - 1)) (N.length - 1)   -- `L53Subst:914`
    ⟹ **(c) 孤児 := ¬ HasParentInBlock Q**

## ⚠ 母集団（除外条件）

    シート `psiI.json` の行列 1,637 本（重複除去）の **全接頭辞 `Q = M[:k]`（`2 <= k <= |M|`）**、
    列の組で重複除去。**`W_take` により `M ∈ W u ⟹ M[:k] ∈ W u`** なので **母集団は健全**。
    ⚠ `|Q| <= 1` は無料なので除外（`mTower_mem_of_le_one` / `n <= 1` も無料）。
    ⚠ **`W` の判定は不要**（3 条件はすべて列の計算）。

## ⚠ 測る前の見積もり

    (a) 狭義 hr0 …… 20〜40%
    (b) 行 2 に非零 …… 50〜60%
    (c) 末尾が孤児 …… 15〜25%
    ★ **3 つとも …… 5〜10%** と見ます。
    ⚠ 残差の形の予想: **`D_v` 型の対角接頭辞**（末尾がいちばん深く、親が無い）。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r263 import load
from r126 import srow

pct = lambda a, b: 100.0 * a / b if b else float('nan')

hr0s = lambda Q: all(Q[0][0] < Q[j][0] for j in range(1, len(Q)))
row2 = lambda Q: any(p[2] > 0 for p in Q)


def orphan(Q):
    j = len(Q) - 1
    return trio.parent(Q, srow(Q, j), j) is None


def prefixes():
    seen = set(); out = []
    for M in load():
        X = [tuple(v) for v in M]
        for k in range(2, len(X) + 1):
            Q = tuple(X[:k])
            if Q not in seen:
                seen.add(Q); out.append(list(Q))
    return out


def main():
    t0 = time.time()
    QS = prefixes()
    print('== 母集団: シート 1,637 本の全接頭辞（|Q| >= 2、重複除去）= %d 本 ==' % len(QS))
    c = Counter()
    core = []
    for Q in QS:
        a = hr0s(Q); b = row2(Q); o = orphan(Q)
        c['n'] += 1
        c['(a) 狭義 hr0'] += a
        c['(b) 行 2 に非零'] += b
        c['(c) 末尾が孤児'] += o
        c['(a)∧(b)'] += (a and b)
        c['(a)∧(c)'] += (a and o)
        c['(b)∧(c)'] += (b and o)
        c['★ (a)∧(b)∧(c) ＝ 残差'] += (a and b and o)
        if a and b and o:
            core.append(Q)
            c['残差/srow=%d' % srow(Q, len(Q) - 1)] += 1
        if a and b:
            c['(a)∧(b) の中で 孤児'] += o
    n = c['n']
    print()
    print('== (ROW2-1) 3 条件 ==')
    for k in ('(a) 狭義 hr0', '(b) 行 2 に非零', '(c) 末尾が孤児',
              '(a)∧(b)', '(a)∧(c)', '(b)∧(c)', '★ (a)∧(b)∧(c) ＝ 残差'):
        print('   %-26s %7d  %8.4f%%' % (k, c[k], pct(c[k], n)))
    print('   ⟹ ★ (a)∧(b) を分母にすると 孤児は %.4f%%（%d / %d）'
          % (pct(c['(a)∧(b) の中で 孤児'], c['(a)∧(b)']), c['(a)∧(b) の中で 孤児'], c['(a)∧(b)']))

    print()
    print('== (ROW2-2) 残差群の `srow` 分布 ==')
    m = c['★ (a)∧(b)∧(c) ＝ 残差']
    for s in (0, 1, 2):
        k = '残差/srow=%d' % s
        print('   srow=%d  %7d  %8.4f%%' % (s, c[k], pct(c[k], m)))
    print('   ⚠ 対照: 残差でない群（全体）の srow 分布')
    cc = Counter()
    for Q in QS: cc[srow(Q, len(Q) - 1)] += 1
    for s in (0, 1, 2):
        print('     srow=%d  %7d  %8.4f%%' % (s, cc[s], pct(cc[s], n)))

    print()
    print('== (ROW2-3) 残差群の形 ==')
    f = Counter()
    for Q in core:
        L = len(Q)
        f['|Q| = %s' % (L if L <= 6 else '>=7')] += 1
        ps = [j for j in range(L) if Q[j][2] > 0]
        f['行2列との距離 %s' % (min(L - 1 - max(ps), 4) if L - 1 - max(ps) <= 3 else '>=4')] += 1
        f['行 2 列の数 %s' % (len(ps) if len(ps) <= 2 else '>=3')] += 1
        f['⛔ 末尾が行 2 正'] += (Q[L - 1][2] > 0)
        f['⛔ D_v 型 (i,i,1) の列がある'] += any(q[0] == q[1] and q[2] > 0 for q in Q)
        f['行 0 が 0,1,2,… の階段'] += all(Q[j][0] == j for j in range(L))
    for k in sorted(f):
        print('   %-28s %7d  %8.4f%%' % (k, f[k], pct(f[k], m)))
    print()
    print('   ★ 残差の例（|Q| 小さい順に 6 件）:')
    for Q in sorted(core, key=len)[:6]:
        print('     |Q|=%d srow=%d  %s' % (len(Q), srow(Q, len(Q) - 1), ' '.join('(%d,%d,%d)' % q for q in Q)))
    print()
    print('（%.1f 秒）' % (time.time() - t0))


if __name__ == '__main__':
    main()
