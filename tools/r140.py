# -*- coding: utf-8 -*-
"""**課題 R140 —— 残った 25.6%（末尾列の親が `A` の中）の展開。**

**場面**（§R150 と同じ。側条件も課す）: `T = shTower Q e n`、`j0' >= 1`、
`A = T.take j0'`、`D = T.drop j0'`、**`∀ q ∈ D, entry D 0 0 <= q.1`**、`S = A ++ D^m`。
**そのうち `S` の末尾列の親 `j0` が `|A|` 未満（＝ `A` の中）のものだけ。**

## ★ 反例の形と (s4) の予想を先に書く（教訓 45 ＋ L3 の §105.2）

**まず導出できる部分:**

    `oper M 1` は写しが 1 個（`k = 0`、ずらし 0）なので **`M.take j0 ++ M[j0:last] = M.dropLast`**。
    孤児でも `Pred M = M.dropLast`。⟹ **`S⟦1⟧ = S.dropLast` は常に。**
    同様に **`|D| >= 2` なら `D⟦1⟧ = D.dropLast`** ⟹
    **`A ++ D^(m-1) ++ D⟦1⟧ = S.dropLast`** ⟹ **`m' = 1` は常に見立てが成立する。**
    （`|D| = 1` なら `oper` は恒等で `D⟦1⟧ = D` ⟹ 破れる。§R150 と同じ理由。）

> **★ (s4) の予想: 「成立している 9.17〜13.11%」の正体は
> **`m' = 1` かつ `|D| >= 2`** の場合、**それだけ**。**
> **⚠ 充足率の見積もり: `m' ∈ {1,2,3}` を振っているので `1/3 × (|D|>=2 の割合)`。
> 実測が 9.17〜13.11% なら `|D|>=2` の割合は 28〜39% のはず。⟹ **成立は 10 〜 15%** と見積もる。**
>
> **⚠ 反例の形: `m' >= 2` の全部（親が `A` の中のとき）。**

**(s1) の予想**: §R146 の一般形が当たるはず ——
**`S⟦m'⟧ = S.take j0 ++ mTower (S[j0:j0+Lb]) d0 d1 m'`、`Lb = last − j0 = |A| + m*|D| − 1 − j0`**。
⟹ **写す窓は `A` の一部 ＋ `D^m` 全体（末尾列を除く）をまたぐ。**

**箱と単位**: 単位 `(Q, e, n, j0', m, m')`。箱 = 行0 ∈ 1..3、行1 < 3、行2 = 0、
`|Q| = 2..4`、`e ∈ 1..3`、`n ∈ 1..3`、`m ∈ 1..5`、`m' ∈ 1..4`。
**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r98 import oper_lean
from r113 import mTower


def shTower(Q, e, n):
    return [(c[0] + k * e, c[1], c[2]) for k in range(n) for c in Q]


def run(L, ES, NS, MS, MPS, R1):
    COL = [(a, b, 0) for a in range(1, 4) for b in range(R1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for v in range(R1):
        for t in itertools.product(COL, repeat=L - 1):
            Q = [(0, v, 0)] + list(t)
            for e in ES:
                for n in NS:
                    T = shTower(Q, e, n)
                    for j0p in range(1, len(T)):
                        A = T[:j0p]; D = T[j0p:]
                        if not D or not all(D[0][0] <= p[0] for p in D):
                            continue
                        for m in MS:
                            S = list(A) + D * m
                            last = len(S) - 1
                            sr = srow(S, last)
                            j0 = trio.parent(S, sr, last)
                            if j0 is None or j0 >= len(A):
                                continue                 # 親が `A` の中のものだけ
                            c['★ 母集団（親が A の中）'] += 1
                            Lb = last - j0
                            c[('(s2) Lb == last - j0', Lb == len(A) + m * len(D) - 1 - j0)] += 1
                            c[('(s3) j0 / |A|', '先頭 (j0=0)' if j0 == 0 else
                               ('末尾寄り' if j0 >= len(A) - 1 else '中間'))] += 1
                            c[('(s3) |A| - j0', min(len(A) - j0, 4))] += 1
                            c[('|D|', min(len(D), 4))] += 1
                            d0 = (S[last][0] - S[j0][0]) if sr > 0 else 0
                            d1 = (S[last][1] - S[j0][1]) if sr > 1 else 0
                            for mp in MPS:
                                lhs = oper_lean(S, mp)
                                # (s1) §R146 の一般形
                                gen = list(S[:j0]) + [tuple(x) for x in
                                                      mTower(S[j0:j0 + Lb], d0, d1, mp)]
                                c[('(s1) §R146 の一般形', lhs == gen)] += 1
                                if lhs != gen:
                                    ex.setdefault('s1 破れ', (Q, e, n, j0p, m, mp, j0, Lb))
                                # (s4) L3 の見立て
                                mit = list(A) + D * (m - 1) + oper_lean(D, mp)
                                ok = (lhs == mit)
                                c[('(s4) 見立て', ok)] += 1
                                c[('(s4) 見立てを (m\', |D|>=2) 別',
                                   mp, len(D) >= 2, ok)] += 1
    tot = c['★ 母集団（親が A の中）']
    print(f'### |Q|={L} 行1<{R1}  母集団 {tot:8d}  [{time.time()-t0:.1f}s]')
    if not tot:
        print('  （0 件）\n'); return
    y = c[('(s1) §R146 の一般形', True)]; nn = c[('(s1) §R146 の一般形', False)]
    print(f'  **(s1) `S⟦m\'⟧ = S.take j0 ++ mTower B d0 d1 m\'`: '
          f'{y} / {y+nn} ({100*y/max(y+nn,1):6.2f}%)**  破れ {nn}')
    print(f'  **(s2) `Lb = |A| + m*|D| − 1 − j0`: {c[("(s2) Lb == last - j0", True)]} / {tot} '
          f'({100*c[("(s2) Lb == last - j0", True)]/tot:6.2f}%)**')
    print('  **(s3) `j0` の位置**: ', dict(sorted((k[1], c[k]) for k in c
                                           if isinstance(k, tuple) and k[0] == '(s3) j0 / |A|')),
          '   `|A| - j0`: ', dict(sorted((k[1], c[k]) for k in c
                                     if isinstance(k, tuple) and k[0] == '(s3) |A| - j0')))
    print('  `|D|` の分布: ', dict(sorted((k[1], c[k]) for k in c
                                    if isinstance(k, tuple) and k[0] == '|D|')))
    y2 = c[('(s4) 見立て', True)]; n2 = c[('(s4) 見立て', False)]
    print(f'  **(s4) L3 の見立て: {y2} / {y2+n2} ({100*y2/max(y2+n2,1):6.2f}%)**')
    print('      (m\', |D|>=2) 別の成立: ', {(k[1], k[2]): c[k] for k in c
                                       if isinstance(k, tuple) and len(k) == 4
                                       and k[0] == "(s4) 見立てを (m', |D|>=2) 別" and k[3]})
    print('      (m\', |D|>=2) 別の破れ: ', {(k[1], k[2]): c[k] for k in c
                                       if isinstance(k, tuple) and len(k) == 4
                                       and k[0] == "(s4) 見立てを (m', |D|>=2) 別" and not k[3]})
    for k in sorted(ex):
        print(f'      {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for R1 in (3,):
        for L in range(2, a.L + 1):
            run(L, (1, 2, 3), (1, 2, 3), (1, 2, 3, 4, 5), (1, 2, 3, 4), R1)
