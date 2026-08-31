# -*- coding: utf-8 -*-
"""**課題 H62 の続き: `le1` 錐の形と、非自明な隙間の「塞いでいる列」。**

`h71` で残ったのは (C) の非自明部分（**根より行 1 が狭義に高いのに `le1` に入らない列**、
`|R|<=3` で 4038 件、`|R|=4` で 4743 件）。L3 が「切るなら**行 0 の祖先鎖に沿って**」と
言っているので、そこと突き合わせる。測るのは 3 つ:

    (i)  **`le1` 錐の形**: 連結か、接尾辞か、いくつの区間に割れるか
         （`Lift1` は錐の上でだけ持ち上げるので、**錐が接尾辞なら「切る」は自明に 1 点**）
    (ii) 非自明な (C) の列 `j` を**塞いでいる列** `j'`
         （`nextrel1` の最小性条件を破る `j'`: `le0 j' j` かつ `行1 j < 行1 j'`）
         その位置・行 1・**一意かどうか**
    (iii) `X` ごとに**切断点が一意か**（塞ぐ列が 1 本なら、そこで切れば済む）

⚠ 構文の測定のみ。`inW` は使わない（R94/R95 の射程の問題を受けない）。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, Lift1, shiftr01
from h70 import anc0, coneV, tieFree
from collections import Counter


def le0(S, a, b):
    """行 0 祖先関係（反射推移）。"""
    return a in anc0(S, b)


def runs(idx, n):
    """添字集合が何本の連続区間に割れるか。"""
    s = sorted(idx)
    if not s:
        return 0
    r = 1
    for a, b in zip(s, s[1:]):
        if b != a + 1:
            r += 1
    return r


def main(lens=(1, 2, 3), vmax=4, dmax=4, bmax=4, tag=''):
    cols = [(d, b, c) for d in range(1, dmax) for b in range(bmax)
            for c in range(2)]
    print('### 母集団%s' % tag)
    print()
    shape = Counter()
    blk = Counter()
    nblk = Counter()
    ex = []
    nX = 0
    nC2 = 0
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
                    if all(p[2] == 0 for p in X):
                        continue
                    nX += 1
                    n = len(X)
                    cone = [j for j in range(n)
                            if trio.is_ancestor(list(X), 1, 0, j)]
                    # ---- (i) 錐の形
                    shape['錐の区間の本数 = %d' % runs(cone, n)] += 1
                    shape['錐が接尾辞（{0} ∪ 末尾から連続）: %s'
                          % ('はい' if set(cone) == {0} | set(
                              range(n - (len(cone) - 1), n)) else 'いいえ')] += 1
                    shape['錐の大きさ = %d / %d' % (len(cone), n)] += 1
                    # ---- (ii)(iii) 非自明な (C) を塞ぐ列
                    w = v - 1 if v >= 1 else 0
                    cut = set()
                    for j in range(n):
                        if j in cone or X[j][1] <= v:
                            continue
                        if not coneV(X, w, j):
                            continue
                        nC2 += 1
                        # `nextrel1` の最小性: ∀ y, j0 < y ∧ le0 y j1 → 行1 j1 <= 行1 y
                        # ⟹ 破るのは **行1 が j より低い** 中間列（前版は不等号が逆だった）
                        bs = [jp for jp in range(1, n)
                              if jp != j and le0(X, jp, j)
                              and X[jp][1] < X[j][1]]
                        blk['塞ぐ列の本数 = %d' % len(bs)] += 1
                        for jp in bs:
                            cut.add(jp)
                            blk['塞ぐ列は末尾か: %s'
                                % ('はい' if jp == n - 1 else 'いいえ')] += 1
                            blk['塞ぐ列の 行1 − v = %d' % (X[jp][1] - v)] += 1
                            blk['塞ぐ列の 行1 が **ちょうど v**: %s'
                                % ('はい' if X[jp][1] == v else 'いいえ')] += 1
                        if not bs:
                            blk['**塞ぐ列が無い（最小性以外の理由で弾かれた）**'] += 1
                            if len(ex) < 6:
                                ex.append((X, v, j, cone))
                    if nC2:
                        nblk['`X` ごとの切断点の個数 = %d' % len(cut)] += 1
    print('母集団 `X`: **%d** 本、非自明な (C) の列 のべ **%d** 本' % (nX, nC2))
    print()
    wref.tally(shape, '(i) `le1` 錐の形')
    wref.tally(blk, '(ii) 非自明な (C) を塞ぐ列')
    wref.tally(nblk, '(iii) `X` ごとの切断点の個数')
    for X, v, j, cone in ex:
        print('    塞ぐ列が無い例: X=`%s` v=%d j=%d 錐=%s' % (fmt(X), v, j, cone))
    print()


if __name__ == '__main__':
    main(lens=(1, 2, 3), tag='（`|R|` = 1..3）')
    print('## ⚠ 教訓 21: `|R| = 4` で壊れないか')
    print()
    main(lens=(4,), vmax=3, dmax=3, bmax=3, tag='（`|R|` = 4）')
