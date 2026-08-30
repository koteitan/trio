# -*- coding: utf-8 -*-
"""**課題 (p1) —— `gexp_zero_eq_mTower` の `j0 > 0` 版が、`j0` と `Lb` のどの範囲で成り立つか。**

**索引から逐語で写した（教訓 2）:**

    `L105Cap:5220` **`gexp_zero_eq_mTower {M} {L d0 d1 n} (hL : L <= M.length)`**
      `: gexp M 0 L d0 d1 n = mTower (M.take L) d0 d1 n`
      ⟹ **前提は `L <= |M|` だけ。`hlen : j0 + Lb + 1 = |M|` ではない。**
    `Column:290` **`le1_append_right (A T) (j0 j1) : le1 (A ++ T) (|A|+j0) (|A|+j1) ↔ le1 T j0 j1`**
      ⟹ **無条件**
    `Wset:909` **`le1_take {X} {l a b} (hl : l <= |X|) (hb : b < l) : le1 (X.take l) a b ↔ le1 X a b`**

⚠ **team-lead の見立て「`hlen : j0 + Lb + 1 = |M|` が要る」は、`j0=0` 版の前提と合わない。**

**定義（逐語）:**

    `Gtrans:19`  `gexp M j0 Lb d0 d1 n = M.take j0 ++ gcopies M j0 Lb d0 d1 n`
    `Gcopy:31`   `gcopies M r L d0 d1 n = (range n).flatMap fun k => gcopy M r L d0 d1 k`
    `Gcopy:24`   `gcopy M r L d0 d1 k = (range' r L).map fun j =>
                   (entry M 0 j + k*d0, entry M 1 j + (if le1 M r j then k*d1 else 0), entry M 2 j)`
    `Wset:927`   `Lift1 X d = (range |X|).map fun i =>
                   (entry X 0 i, entry X 1 i + (if le1 X 0 i then d else 0), entry X 2 i)`
    `L105Cap:4177` `mTower Q d0 d1 n = (range n).flatMap fun k => Lift1 (shiftr01 (d0*k) 0 Q) (d1*k)`

**⚠ `entry M i j` は `j >= |M|` で 0**（`getD` の既定値 `(0,0,0)`）。

## ★ 反例の形を先に書く（教訓 45）＋ 充足率の見積もり

> **予想: 等式 `gexp M j0 Lb d0 d1 n = M.take j0 ++ mTower ((M.drop j0).take Lb) d0 d1 n` は
> **`j0 + Lb <= |M|` のとき成立、超えると破れる**。**
> 理由: `gcopy` は `range' j0 Lb` を走るので `j0+Lb > |M|` だと範囲外を 0 として読むが、
> `(M.drop j0).take Lb` は短くなるので長さが合わない。
> **⚠ 充足率の見積もり: 試す格子のうち破れるのは 25 〜 40%。**
"""
import sys, itertools, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter

Z = (0, 0, 0)


def entry(M, i, j):
    c = M[j] if j < len(M) else Z
    return c[i]


def le1(M, a, b):
    """`le1 M a b` = `a < |M| ∧ b < |M| ∧ RTG (nextrel1 M) a b`。"""
    if a >= len(M) or b >= len(M):
        return False
    return trio.is_ancestor(M, 1, a, b)


def gcopy(M, r, L, d0, d1, k):
    return [(entry(M, 0, j) + k * d0,
             entry(M, 1, j) + (k * d1 if le1(M, r, j) else 0),
             entry(M, 2, j)) for j in range(r, r + L)]


def gexp(M, j0, Lb, d0, d1, n):
    out = list(M[:j0])
    for k in range(n):
        out += gcopy(M, j0, Lb, d0, d1, k)
    return out


def shiftr01(d0, d1, Q):
    return [(c[0] + d0, c[1] + d1, c[2]) for c in Q]


def Lift1(X, d):
    return [(entry(X, 0, i), entry(X, 1, i) + (d if le1(X, 0, i) else 0), entry(X, 2, i))
            for i in range(len(X))]


def mTower(Q, d0, d1, n):
    out = []
    for k in range(n):
        out += Lift1(shiftr01(d0 * k, 0, Q), d1 * k)
    return out


def run(cm, L, DS, NS):
    COL = [(a, b, c) for a in range(3) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    for Mt in itertools.product(COL, repeat=L):
        M = list(Mt)
        for j0 in range(L + 1):
            for Lb in range(L + 2):
                for d0 in DS:
                    for d1 in DS:
                        for n in NS:
                            lhs = gexp(M, j0, Lb, d0, d1, n)
                            rhs = list(M[:j0]) + mTower(M[j0:j0 + Lb], d0, d1, n)
                            ok = (lhs == rhs)
                            key = '★ j0+Lb <= |M|' if j0 + Lb <= L else 'j0+Lb > |M|'
                            c[(key, ok)] += 1
                            if not ok:
                                ex.setdefault(key, (M, j0, Lb, d0, d1, n))
    print(f'### 行2<={cm} |M|={L}  `j0 ∈ 0..{L}`, `Lb ∈ 0..{L+1}`, `d0,d1 ∈ {tuple(DS)}`, `n ∈ {tuple(NS)}`')
    for key in ('★ j0+Lb <= |M|', 'j0+Lb > |M|'):
        ok = c[(key, True)]; ng = c[(key, False)]
        if ok + ng:
            print(f'  {key:18s}: 分母 {ok+ng:9d}  成立 {ok:9d} ({100*ok/(ok+ng):6.2f}%)  '
                  f'**破れ {ng:8d}**')
        if key in ex:
            print(f'      破れの例: M={ex[key][0]} j0={ex[key][1]} Lb={ex[key][2]} '
                  f'd0={ex[key][3]} d1={ex[key][4]} n={ex[key][5]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for cm in (1,):
        for L in range(2, a.L + 1):
            run(cm, L, (0, 1, 2), (0, 1, 2, 3))
