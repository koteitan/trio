# -*- coding: utf-8 -*-
"""**課題 R107/(c1)-(c4) ＋ (s4) —— ブロッカーの割合（＝ 残核の大きさ）。**

⚠ 教訓 24（測る前に `grep`）: 潰れの補題は**既にある** ——
`Wtower2.liftStage_of_window`（`:128`）が「窓条件が全列で成り立つ ⟹
`Lift1 X d = shiftr01 0 d X`（一様シフト）」で、`Wslift.ulift_mem_W` で無料。
`L51Lift.liftTower`（`:41`）も既存。**ここで測るのは補題ではなく「その条件が成り立つ割合」。**

母集団 = `TowerExpBigRow2`（`L105Cap:2880`）の前提を全部満たすもの **かつ `srow = 2`**:
    `argOK R` ∧ `2 <= |R|` ∧ `z <= 1` ∧ `domT R m` ∧
    `hasParent ((0,v,z)::R) (srow R (|R|-1)) |R|` ∧ `∃ p ∈ R.dropLast, p.2.2 ≠ z`
⚠ `R.dropLast ∈ Wstar` だけは有限で判定できない（R94）ので落とす ＝ **上位集合**。

    `Q := (0,v,z) :: R.dropLast`（周期の 1 単位）
    **ブロッカー** := `Q` の根以外の列で行 1 <= `v` のもの（`Lcone.le1_zero_iff` の窓条件を壊す列）

  (c1) ブロッカーがある割合（＝ **残核の大きさ**）。分母を必ず
  (c2) ブロッカーの本数の分布
  (c3) `|R|` を伸ばすと割合はどう動くか
  (c4) ブロッカーが無いとき `Lift1 (X⟦n⟧) e` は本当に一様シフトか
  (s4) (y8) の「周期 2 のブロック」は `shTower` の形か（周期の 1 単位は `Q` か）
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r98 import oper_lean


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def Lift1(X, dd):
    return [(c[0], c[1] + (dd if trio.is_ancestor(X, 1, 0, i) else 0), c[2])
            for i, c in enumerate(X)]


def run(DS, BS, CS, VS, ZS, LS, NS, label):
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    tot = Counter(); blkn = Counter(); c4 = Counter(); ex = {}
    t0 = time.time()
    for L in LS:
        for Rt in itertools.product(COL, repeat=L):
            R = list(Rt)
            if any(p[0] < 1 for p in R):
                continue
            j = len(R) - 1
            i1 = srow(R, j)
            if i1 != 2:
                continue                                    # srow = 2 の枝だけ
            if trio.parent(R, i1, j) is not None or lev(R[j]) - 1 < 0:
                continue                                    # domT
            for v in VS:
                for z in ZS:
                    X = [(0, v, z)] + R
                    if trio.parent(X, i1, len(R)) is None:
                        continue                            # hasParent
                    if not any(p[2] != z for p in R[:-1]):
                        continue                            # 追加前提
                    Q = [(0, v, z)] + R[:-1]
                    nb = sum(1 for p in R[:-1] if p[1] <= v)
                    tot[(L, 'ブロッカーあり' if nb else 'ブロッカーなし')] += 1
                    blkn[nb] += 1
                    if nb == 0:
                        e = R[j][1] - v
                        ok = True
                        for nn in NS:
                            T = oper_lean(X, nn)
                            if Lift1(T, e) != [(c[0], c[1] + e, c[2]) for c in T]:
                                ok = False; break
                        c4['ブロッカーなし ⟹ 一様/' +
                           ('ok' if ok else '**破れる**')] += 1
                        if not ok:
                            ex.setdefault('c4 破れ', (R, v, z))
    dt = time.time() - t0
    n = sum(tot.values())
    print(f'### {label}  ({dt:.1f}s)  **母数 {n}**（`R.dropLast ∈ Wstar` は落とした上位集合）')
    if n == 0:
        print('  ⚠ 0 件'); return
    nb_yes = sum(c for (L, k), c in tot.items() if k == 'ブロッカーあり')
    print(f'  -- (c1) ★ ブロッカーがある割合 ＝ **{nb_yes} / {n} = {100*nb_yes/n:.2f}%** --')
    print('  -- (c3) `|R|` 別 --')
    for L in sorted({x[0] for x in tot}):
        a = tot[(L, 'ブロッカーあり')]; b = tot[(L, 'ブロッカーなし')]
        if a + b:
            print(f'     |R|={L}: あり {a:9d} / 全 {a+b:9d} = **{100*a/(a+b):5.2f}%**')
    print('  -- (c2) ブロッカーの本数 --')
    for k in sorted(blkn):
        print(f'     {k} 本 : {blkn[k]:9d}  ({100*blkn[k]/n:5.2f}%)')
    print('  -- (c4) ブロッカーなし ⟹ `Lift1` は一様シフトか --')
    for k in sorted(c4):
        print(f'     {k:32s} {c4[k]:9d}')
    for k in sorted(ex):
        print(f'  ⚠ {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    run((1, 2, 3), (0, 1, 2, 3), (0, 1), (0, 1, 2, 3), (0, 1),
        tuple(range(2, a.L + 1)), (1, 2, 3, 4),
        f'R107 ブロッカーの割合（断片 行2<=1, `srow=2`）|R|<={a.L}')
