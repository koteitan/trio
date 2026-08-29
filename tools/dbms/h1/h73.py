# -*- coding: utf-8 -*-
"""**課題 H62 の帰結: 候補補題 `coneV(v) ⊆ le1 ⊆ coneV(v-1)` を全数で当てる。**

`h71` で (C) を閾値 `v` で割ったとき **`coneV(v) かつ ¬le1` が 0 件**だった
（差の出た列 122352 + 261299 本すべてで例外なし）。これは偶然ではなく
**候補補題**である可能性が高い:

    **(左) `coneV X v j → le1 X 0 j`**       ← 未証明。ここで測る
    (右) `le1 X 0 j → coneV X (v-1) j`       ← **`coneV_of_le1`（証明ずみ・無条件）**

（`coneV X w j` = `Cgraft.lean:301`: `j` の行 0 祖先が全部 行 1 > `w`。
　`v = entry X 1 0` は根の行 1。）

もし (左) が真なら:

    `mlift X v d`（閾値 `v` のマスクリフト）と `Lift1 X d` は
    **`coneV(v)` の上で一致**し、**差はちょうど `coneV(v-1) \\ coneV(v)`**
    ＝「行 0 祖先鎖の上に 行 1 がちょうど `v` の列がいる」列だけ。
    ⟹ **H11 の `MliftR`（閾値の off-by-one）の正体がこれ。**

⚠ 構文の測定のみ（`inW` は使わない）。**母集団は `LiftTieCore` の形に限らず
一般の列で取る**（候補補題は無条件の主張なので、限ると弱い検査になる）。
⚠ 教訓 21: 長さと列の範囲を**それぞれ独立に**振って、100% が壊れないか見る。
"""
import sys, itertools, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry
from h70 import anc0, coneV
from collections import Counter


def sweep(lens, dmax, bmax, cmax=2, argok=True, tag=''):
    cols = [(d, b, c) for d in range(1 if argok else 0, dmax)
            for b in range(bmax) for c in range(cmax)]
    n = 0
    ex = []
    cnt = Counter()
    for L in lens:
        for R in itertools.product(cols, repeat=L):
            X = [(0, R[0][1], 0)] + list(R) if False else None
            # 一般の列: 根は (0, v, z) で v, z は独立に振る
            for v in range(bmax + 1):
                for z in range(cmax):
                    X = [(0, v, z)] + list(R)
                    w = v - 1 if v >= 1 else 0
                    for j in range(len(X)):
                        le1 = trio.is_ancestor(list(X), 1, 0, j)
                        cv = coneV(X, v, j)
                        cw = coneV(X, w, j)
                        n += 1
                        if cv and not le1:
                            cnt['**(左) の反例: `coneV(v)` かつ `¬le1`**'] += 1
                            if len(ex) < 5:
                                ex.append(('左', X, v, j))
                        if le1 and not cw:
                            cnt['(右) の反例（証明ずみなので 0 のはず）'] += 1
                            if len(ex) < 5:
                                ex.append(('右', X, v, j))
                        if cw and not le1:
                            cnt['隙間 `coneV(v-1) \\ le1`（`TieFree` が主張するもの）'] += 1
                        if le1 and not cv:
                            cnt['`le1 \\ coneV(v)`'] += 1
    print('| %s | %d | %d | %d | %d |'
          % (tag, n,
             cnt['**(左) の反例: `coneV(v)` かつ `¬le1`**'],
             cnt['(右) の反例（証明ずみなので 0 のはず）'],
             cnt['隙間 `coneV(v-1) \\ le1`（`TieFree` が主張するもの）']))
    return cnt, ex


def main():
    print('## 候補補題 `coneV X v j → le1 X 0 j` を全数で当てる')
    print()
    print('| 母集団 | 検査した (X,j) | **(左) の反例** | (右) の反例 | 隙間 `coneV(v-1)\\le1` |')
    print('|---|--:|--:|--:|--:|')
    allex = []
    for lens, dmax, bmax, tag in [
            ((1, 2), 4, 4, '`|R|`=1..2 行0<4 行1<4'),
            ((3,), 4, 4, '`|R|`=3 行0<4 行1<4'),
            ((3,), 3, 5, '`|R|`=3 行0<3 **行1<5**'),
            ((4,), 3, 3, '`|R|`=4 行0<3 行1<3'),
            ((4,), 4, 3, '`|R|`=4 **行0<4** 行1<3'),
            ((5,), 3, 3, '**`|R|`=5** 行0<3 行1<3'),
    ]:
        c, e = sweep(lens, dmax, bmax, tag=tag)
        allex += e
    print()
    print('**行 0 に 0 を許す（`argOK` を落とす）版**（無条件の主張なので広く取る）:')
    print()
    print('| 母集団 | 検査した (X,j) | **(左) の反例** | (右) の反例 | 隙間 |')
    print('|---|--:|--:|--:|--:|')
    for lens, dmax, bmax, tag in [
            ((2, 3), 3, 4, '`|R|`=2..3 行0<3（0 込み）行1<4'),
            ((4,), 3, 3, '`|R|`=4 行0<3（0 込み）行1<3'),
    ]:
        c, e = sweep(lens, dmax, bmax, argok=False, tag=tag)
        allex += e
    print()
    if allex:
        print('**反例:**')
        for k, X, v, j in allex:
            print('    (%s) X=`%s` v=%d j=%d' % (k, fmt(X), v, j))
    else:
        print('> **⟹ 両向きとも反例ゼロ。(左) は候補補題として生き残った。**')
    print()


if __name__ == '__main__':
    main()
