# -*- coding: utf-8 -*-
"""**R113 の続き —— L3 に残る「唯一の穴」を切り分ける。**

H12 の §231 の補題案:
> **「`operTower` の第 `k` ブロックの `le1` 錐は、そのブロック単体の錐と一致する」**（`k >= 1`）

H12 の見立て:「`Wset.le1_Lift1`（`:1213`）＋ `Core.le1_shiftr01`（`:3470`）の合成で出るのでは」

★ **これを 2 段に割ると、片方は既存の緑 2 本で出て、もう片方が穴である**はず:

    (A) `le1 (ブロック k を単体で見たもの) 0 i  ↔  le1 Q 0 i`
        ブロック k ＝ `Lift1 (shiftr01 (k*d) 0 Q) (k*e)` なので
        **`le1_Lift1` ＋ `le1_shiftr01` の合成そのもの** ⟹ **出るはず**
    (B) `le1 T 0 (k*|Q| + i)  ↔  le1 (ブロック k を単体で見たもの) 0 i`
        **塔全体の根から見た錐と、ブロック単体の根から見た錐が一致するか**
        ⚠ **これは接頭辞局所性でも一様シフト不変性でも出ない。ここが穴のはず**

⚠ しきい値が違うことに注意: 塔 `T` の根の行 1 は `v`、ブロック `k` の根の行 1 は `v + k*e`。
   ⟹ 「ブロッカー」の意味が両者で違う。(B) が非自明なのはそのため。

`operTower` の定義は **`L105Cap.lean:3407` から写した**（教訓 25）:
    `0 => []` / `n+1 => Q ++ shiftr01 d 0 (Lift1 (operTower Q d e n) e)`
"""
import sys, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r113 import Lift1, sh, operTower, scene_gen


def run(COL, VS, ZS, Ls, NS, label, sample_from=5, sample=40000):
    a_cnt = Counter(); b_cnt = Counter(); ex = {}
    for Q, d, e, hb in scene_gen(COL, VS, ZS, Ls, sample_from, sample):
        for n in NS:
            T = operTower(Q, d, e, n)
            if not T:
                continue
            for k in range(n):
                Bk = Lift1(sh(Q, k * d), k * e)       # ブロック k（単体）
                seg = T[k * len(Q):(k + 1) * len(Q)]
                a_cnt['ブロック k の中身が一致/' +
                      ('ok' if seg == Bk else '**不一致**')] += 1
                for i in range(len(Q)):
                    # (A) ブロック単体の錐 ⟷ Q の錐
                    lhs = trio.is_ancestor(Bk, 1, 0, i)
                    rhs = trio.is_ancestor(Q, 1, 0, i)
                    a_cnt['(A) 単体ブロックの錐 = Q の錐/' +
                          ('ok' if lhs == rhs else '**不一致**')] += 1
                    if lhs != rhs:
                        ex.setdefault('A 破れ', (Q, d, e, n, k, i))
                    # (B) 塔全体の錐 ⟷ ブロック単体の錐
                    lt = trio.is_ancestor(T, 1, 0, k * len(Q) + i)
                    tag = 'k=0' if k == 0 else 'k>=1'
                    b_cnt[f'(B) 塔の錐 = 単体ブロックの錐 [{tag}]/' +
                          ('ok' if lt == lhs else '**不一致**')] += 1
                    if lt != lhs:
                        ex.setdefault(f'B 破れ [{tag}]', (Q, d, e, n, k, i))
    print(f'### {label}')
    for c in (a_cnt, b_cnt):
        for k in sorted(c):
            print(f'  {k:48s} {c[k]:11d}')
    for k in sorted(ex):
        print(f'  ★ {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=5)
    ap.add_argument('--n', type=int, default=6)
    a = ap.parse_args()
    COL = [(d, b, c) for d in (1, 2) for b in (0, 1, 2) for c in (0, 1)]
    run(COL, (0, 1, 2), (0, 1), tuple(range(2, a.L + 1)),
        tuple(range(2, a.n + 1)),
        f'R114 (A)/(B) の切り分け（H12 の箱）|R|<={a.L}, n=2..{a.n}')
