# -*- coding: utf-8 -*-
"""**課題 H62: `LiftTieCoreRow2` の構造測定 —— `Lift1 X 1` と一様シフトの差分。**

    def LiftTieCoreRow2（`L105Cap.lean:2056`、`towerOK_of_liftTieCoreRow2` は緑）
      ∀ v z R, argOK R → (∃ p ∈ R, p.2.1 = v) →
        ¬ (1 <= v ∧ TieFree ((0,v,z) :: R)) →
        **(∃ p ∈ ((0,v,z) :: R), 0 < p.2.2)**            ← 行 2 に非零
        ((0,v,z) :: R) ∈ W (2v+z) →
        **Lift1 ((0,v,z) :: R) 1 ∈ W (2v+z + 2)**

`liftStage_of_zeroRow2`（`L105Cap.lean:2036`、**仮定ゼロ**・緑）で
「行 2 ≡ 0 なら (WL) は無料」なので、残るのは**行 2 に非零がある場合だけ**。

⚠ **これは所属の判定ではなく構造の測定**なので、R94/R95 の射程の問題を受けない
（`inW` は使わない。使うのは `Lift1` / `shiftr01` / 行 0 祖先鎖という**構文**だけ）。

## 測るもの

    (g1) 母集団を「行 2 ≡ 0」と「行 2 に非零あり」に割る
         前者は `liftStage_of_zeroRow2` で**もう片づいている**
    (h2) **`Lift1 X 1` と一様シフト `shiftr01 0 1 X` はどこが違うか**
         一致するなら `ulift_mem_W` で無料 ← **本題**
    (h3) 食い違う列の性質: 行 0 祖先鎖のどこにいるか、行 1 の値
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, argOK, Lift1, shiftr01
from collections import Counter


def anc0(S, j):
    """行 0 祖先（自身を含む）の添字。"""
    out = []
    while j is not None:
        out.append(j)
        j = trio.parent(list(S), 0, j)
    return out


def coneV(S, v, j):
    """`Cgraft.lean:301` —— 行 0 祖先が全部 行 1 > v。"""
    return all(S[y][1] > v for y in anc0(S, j))


def tieFree(S):
    """`Wtower2.lean:33` —— `coneV X (entry X 1 0 - 1)` の錐が `le1 X 0 ·` に収まる。"""
    w = entry(S, 1, 0) - 1 if entry(S, 1, 0) >= 1 else 0
    for j in range(len(S)):
        if coneV(S, w, j) and not trio.is_ancestor(list(S), 1, 0, j):
            return False
    return True


def main(lens=(1, 2, 3), vmax=4, dmax=4, bmax=4):
    cols = [(d, b, c) for d in range(1, dmax) for b in range(bmax)
            for c in range(2)]
    print('## 母集団: `LiftTieCore` の前提を満たす `((0,v,z) :: R)`')
    print()
    print('列 = 行0∈[1,%d]・行1<%d・行2<2、`|R|` = %s、`v < %d`、`z <= 1`'
          % (dmax - 1, bmax, list(lens), vmax))
    print()
    print('⚠ 前提 `((0,v,z) :: R) ∈ W (2v+z)` は**ここでは課さない**。'
          '所属の判定は R94/R95 で射程外なので、')
    print('　課すと母集団が計器の都合で歪む。**構文の前提だけで取り、'
          'あとで Lean 証明ずみの族に絞った表も出す。**')
    print()

    shape = Counter()
    diffs = Counter()
    poscnt = Counter()
    nz_where = Counter()
    ex = []
    exsame = []
    for L in lens:
        for R in itertools.product(cols, repeat=L):
            R = list(R)
            for v in range(vmax):
                if not any(p[1] == v for p in R):      # タイあり
                    continue
                for z in range(2):
                    X = [(0, v, z)] + R
                    if 1 <= v and tieFree(X):          # ¬(1<=v ∧ TieFree)
                        shape['`TieFree` で落ちる（`liftTie_case_tieFree` で無料）'] += 1
                        continue
                    zero2 = all(p[2] == 0 for p in X)
                    if zero2:
                        shape['**行 2 ≡ 0**（`liftStage_of_zeroRow2` で**無料**）'] += 1
                        continue
                    shape['**残る: 行 2 に非零あり**'] += 1
                    # ---- (g2) 行 2 の非零はどこか
                    at_root = z > 0
                    at_tail = R[-1][2] > 0
                    at_mid = any(p[2] > 0 for p in R[:-1])
                    nz_where['z=%d / 根%s 末尾%s 中%s'
                             % (z, '有' if at_root else '無',
                                '有' if at_tail else '無',
                                '有' if at_mid else '無')] += 1
                    # ---- (h2) Lift1 と一様シフトの差
                    A = Lift1(X, 1)
                    B = shiftr01(0, 1, X)
                    d = [j for j in range(len(X)) if A[j] != B[j]]
                    diffs['差 %d 本' % len(d)] += 1
                    if not d and len(exsame) < 3:
                        exsame.append(X)
                    for j in d:
                        # ---- (h3) 食い違う列の性質
                        onchain = 0 in anc0(X, j)
                        poscnt['根の行 0 祖先鎖の上か: %s' % ('**はい**' if onchain else 'いいえ')] += 1
                        poscnt['行 1 が根以下（`entry X 1 j <= v`）: %s'
                               % ('**はい**' if X[j][1] <= v else 'いいえ')] += 1
                        poscnt['位置: %s' % ('末尾' if j == len(X) - 1
                                             else '根' if j == 0 else '中')] += 1
                    if d and len(ex) < 6:
                        ex.append((X, d, A, B))
    wref.tally(shape, '(g1) 母集団の割れ方')
    wref.tally(nz_where, '(g2) 行 2 の非零がどこにいるか（`z` 別）')
    wref.tally(diffs, '(h2) **`Lift1 X 1` と一様シフト `shiftr01 0 1 X` の差の本数**')
    wref.tally(poscnt, '(h3) 食い違う列の性質（列ごとに 1 票）')
    for X, d, A, B in ex:
        print('    例: X=`%s`' % fmt(X))
        print('        Lift1 =`%s`' % fmt(A))
        print('        一様  =`%s`   差の位置 %s' % (fmt(B), d))
    if exsame:
        print()
        print('    差 0 の例（`ulift_mem_W` で無料）:')
        for X in exsame:
            print('        `%s`' % fmt(X))
    print()


if __name__ == '__main__':
    main(lens=(1, 2, 3))
    print()
    print('## ⚠ 教訓 21: 上で 100% が出たものを `|R| = 4` で壊す')
    print()
    main(lens=(4,), vmax=3, dmax=3, bmax=3)
