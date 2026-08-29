# -*- coding: utf-8 -*-
"""**(C2) の核心: 錐の外の 行 2 正の列は、塔の中でも孤児か（＝ snoc は無料か）。**

§251 で前提は `hr0` と `hstep` だけになった。`hstep` は「塔に 1 列足す」。
錐の外の列では `hstep` の窓の仮定が**空虚**なので、無条件に足せないといけない。

⚠ ところが `L105Cap.snoc_of_open`（`L105Cap.lean:166`、緑）:

    `snoc_of_open p (hC : C ∈ W u) (hCne : C ≠ [])
      (hopen : hasParent (C ++ [p]) (srow (C ++ [p]) |C|) |C| →
               (∃ q ∈ C, 0 < q.2.2) → C ++ [p] ∈ W u) : C ++ [p] ∈ W u`

⟹ **足す列が親を持たなければ `hopen` は空虚に真 ⟹ snoc は無料。**

⟹ **測るべきはただ 1 つ: 錐の外の 行 2 正の列は、塔の中でも親を持たないか。**
持つなら「復活」＝ (C2) の本体。持たないなら **(C2) は消える**。

⚠ `d`, `e` は `L105Cap.oper_eq_mTower`（`L105Cap.lean:5228`）から逐語:
    `M = Lift1 ((0,v,z)::R) t`,  `srow M (|M|-1) = 2` なので
    `d = entry M 0 (|M|-1) - entry M 0 0`,  `e = entry M 1 (|M|-1) - entry M 1 0`
    `Q = M.dropLast`
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, srow, has_parent, dom_m, argOK, Lift1, shiftr01
from collections import Counter

ref = wref.Ref(maxnodes=4000)


def le1(S, a, b):
    return trio.is_ancestor(list(S), 1, a, b)


def mTower(Q, d, e, n):
    """`L105Cap.lean:4159`。"""
    out = []
    for k in range(n):
        out += Lift1(shiftr01(d * k, 0, Q), e * k)
    return out


def run(cmax, lens, ns=(1, 2, 3), tmax=2, vmax=3):
    cols = [(a, b, c) for a in range(1, 3) for b in range(3) for c in range(cmax)]
    print('### 箱: 行2 < %d、`v<%d`、`t<%d`、`z = 0`、`n ∈ %s`'
          % (cmax, vmax, tmax, list(ns)))
    print()
    print('| `|R|` | `n` | **分母（錐の外の行2正の列 (Q,j) の組）** |'
          ' **塔の中で親を持つ（＝復活）** | 割合 | `Q` の中で孤児 |')
    print('|--:|--:|--:|--:|--:|--:|')
    ex = []
    for L in lens:
        for n in ns:
            den = rev = orphQ = 0
            for R in itertools.product(cols, repeat=L):
                R = list(R)
                if not argOK(R) or dom_m(R) is None:
                    continue
                if srow(R, len(R) - 1) != 2:
                    continue
                z = 0
                for v in range(vmax):
                    if not has_parent([(0, v, z)] + R, 2, len(R)):
                        continue
                    for t in range(tmax):
                        M = Lift1([(0, v, z)] + R, t)
                        Q = M[:-1]
                        if ref.inW(Q, 2 * (v + t) + z) is not True:
                            continue
                        d = entry(M, 0, len(M) - 1) - entry(M, 0, 0)
                        e = entry(M, 1, len(M) - 1) - entry(M, 1, 0)
                        bad = [j for j in range(1, len(Q))
                               if entry(Q, 2, j) > 0 and not le1(Q, 0, j)]
                        if not bad:
                            continue
                        T = mTower(Q, d, e, n)
                        B = Lift1(shiftr01(d * n, 0, Q), e * n)
                        for j in bad:
                            C1 = T + B[:j + 1]
                            p = len(T) + j
                            den += 1
                            if has_parent(C1, srow(C1, p), p):
                                rev += 1
                                if len(ex) < 4:
                                    ex.append((R, v, t, n, j, Q, d, e))
                            if not has_parent(Q[:j + 1], 2, j):
                                orphQ += 1
            print('| %d | %d | **%d** | **%d** | **%.1f%%** | %d (%.1f%%) |'
                  % (L, n, den, rev, 100.0 * rev / max(den, 1),
                     orphQ, 100.0 * orphQ / max(den, 1)))
    print()
    if ex:
        print('**⛔ 塔の中で親を持つ（復活する）例:**')
        for R, v, t, n, j, Q, d, e in ex:
            print('    R=`%s` v=%d t=%d n=%d j=%d  Q=`%s` d=%d e=%d'
                  % (fmt(R), v, t, n, j, fmt(Q), d, e))
    else:
        print('> **★ 復活ゼロ ⟹ `snoc_of_open` で (C2) は無料。**')
    print()


if __name__ == '__main__':
    print('## (C2): 錐の外の行 2 正の列は塔の中でも孤児か')
    print()
    run(2, (2, 3))
