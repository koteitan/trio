# -*- coding: utf-8 -*-
"""**課題 H62 の (h3) 本体: `Lift1` と一様シフトの差を 3 つに割る。**

`h70` で分かったこと:

    **`Lift1 X 1` と `shiftr01 0 1 X` は 1 件も一致しない**（差 1〜4 本、|R|=1..4 とも）
    ⟹ `ulift_mem_W` で無料になる事例は**この母集団には無い**

⚠ `h70` の「食い違う列は 100% 根の行 0 祖先鎖の上」は**自明**だった（教訓 21 を自分に適用）:
`argOK R` より根だけが深さ 0 なので、**根はどの列の行 0 祖先でもある**。測る意味がない。

## 本当に情報のある割り方

差が出る列は定義から `¬ le1 X 0 j`（`Lift1` は `le1` 錐の上でだけ持ち上げる）。
これを **`coneV`**（`Cgraft.lean:301`: 行 0 祖先が全部 行 1 > v）で 3 つに割る:

    (A) `行 1 j <= v`              … 錐に入りようがない（最初の `nextrel1` が立たない）
    (B) `行 1 j > v` かつ `¬coneV` … **行 0 祖先鎖の上に「低い列」がいて塞いでいる**
    (C) `行 1 j > v` かつ `coneV`  … **`coneV \\ le1` の隙間**。`TieFree` が主張する当のもの
                                     （`coneV_of_le1` は無条件・緑。逆が `TieFree`）

**(C) が空なら `TieFree` が成り立ち、`liftTie_case_tieFree` で片づく。**
**(C) が残るのが本当の核。その本数と位置が L3 の「行 0 の祖先鎖に沿って切る」の材料。**

⚠ これは構文の測定であって所属の判定ではないので、R94/R95 の射程の問題を受けない。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, Lift1, shiftr01
from h70 import anc0, coneV, tieFree
from collections import Counter


def main(lens=(1, 2, 3), vmax=4, dmax=4, bmax=4, tag=''):
    cols = [(d, b, c) for d in range(1, dmax) for b in range(bmax)
            for c in range(2)]
    print('### 母集団%s（列 = 行0∈[1,%d]・行1<%d・行2<2、`|R|` = %s、`v < %d`）'
          % (tag, dmax - 1, bmax, list(lens), vmax))
    print()
    cls = Counter()
    perX = Counter()
    cpos = Counter()
    ncols = 0
    nX = 0
    exC = []
    for L in lens:
        for R in itertools.product(cols, repeat=L):
            R = list(R)
            for v in range(vmax):
                if not any(p[1] == v for p in R):
                    continue
                for z in range(2):
                    X = [(0, v, z)] + R
                    if 1 <= v and tieFree(X):
                        continue
                    if all(p[2] == 0 for p in X):     # 行 2 ≡ 0 は無料
                        continue
                    nX += 1
                    A = Lift1(X, 1)
                    B = shiftr01(0, 1, X)
                    dif = [j for j in range(len(X)) if A[j] != B[j]]
                    nC = 0
                    w = v - 1 if v >= 1 else 0     # ← `TieFree` の閾値（v-1）
                    for j in dif:
                        ncols += 1
                        if X[j][1] < v:
                            cls['(A) `行1 j < v`（閾値 v-1 の錐にも入れない）'] += 1
                        elif not coneV(X, w, j):
                            cls['(B) `¬coneV(v-1)`（行 0 祖先鎖の低い列が塞ぐ）'] += 1
                        else:
                            cls['**(C) `coneV(v-1)` かつ `¬le1`'
                                '（= `TieFree` の隙間。本当の核）**'] += 1
                            nC += 1
                            cpos['(C) の位置: %s'
                                 % ('末尾' if j == len(X) - 1 else '中')] += 1
                            cpos['(C) の行 1 − v = %d' % (X[j][1] - v)] += 1
                    perX['(C) が %d 本' % nC] += 1
                    if nC and len(exC) < 6:
                        exC.append((X, v, dif))
    print()
    print('母集団 `X`: **%d** 本、差の出た列 のべ **%d** 本' % (nX, ncols))
    print()
    wref.tally(cls, '差の出た列の 3 分割')
    wref.tally(perX, '**`X` 1 本あたりの (C) の本数**')
    wref.tally(cpos, '(C) の位置と行 1 の高さ')
    for X, v, dif in exC:
        print('    (C) を持つ例: X=`%s`  v=%d  差の位置 %s' % (fmt(X), v, dif))
    print()


if __name__ == '__main__':
    main(lens=(1, 2, 3), tag='（`|R|` = 1..3）')
    print('## ⚠ 教訓 21: `|R| = 4` で壊れないか')
    print()
    main(lens=(4,), vmax=3, dmax=3, bmax=3, tag='（`|R|` = 4）')
