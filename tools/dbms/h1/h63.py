# -*- coding: utf-8 -*-
"""**課題 H57-f: 陰性対照 —— 「その核の場面で計器が実際に鳴るか」。**

`h61` は 8 本の核で違反ゼロだったが、**陰性対照が無い**。
「違反ゼロ」は、その場面で計器が鳴りうることを示して初めて意味がある。

そこで各核を**わざと 1 目盛り壊した版**を同じ母集団・同じ予算で測る。
壊し方は「段を 1 下げる」か「不等式の向きを逆にする」だけで、
**壊した版は偽であるはず** ⟹ **違反が出なければ計器はその場面で死んでいる。**

    `LiftStage−1`    `Lift1 X d ∈ W (m+2d−1)`         段を 1 下げた
    `Row1MonoUp`     行 1 を**上げて**も `∈ W a`       向きを逆にした
    `WCat−1`         `A ++ B ∈ W (u−1)`               段を 1 下げた
    `ShiftTower−1`   `shTower Q e n ∈ W (u−1)`        段を 1 下げた
    `Row0Free`       （壊さない。**元から `Row0Free` 自身が対照**）
    `TowerOK−1`      `((0,v,z)::R)⟦n⟧ ∈ W (2v+z−1)`   段を 1 下げた
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
import h61
from wref import Ref, fmt, entry, argOK, Lift1, srow, has_parent, dom_m
from collections import Counter

AMAX = 12


def verd(r):
    return '**違反**' if r is False else 'OK' if r is True else '未判定'


def main(lens=(1, 2, 3)):
    ref = Ref(ns=(1, 2, 3), maxdepth=9, maxlen=34, maxnodes=60000)
    wref.print_controls(ref)
    cols = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]
    pool = []
    for L in lens:
        for S in itertools.product(cols, repeat=L):
            pool.append(list(S))
    dec = [(S, ref.minstage(S, AMAX)) for S in pool]
    dec = [(S, u) for S, u in dec if u is not None]
    print('## 母集団: 長さ %s ⟹ 候補 %d 本、段が確定 **%d** 本'
          % (list(lens), len(pool), len(dec)))
    print()

    res = {}

    def note(name, r):
        res.setdefault(name, Counter())[verd(r)] += 1

    for S, u in dec:
        for d in (1, 2):
            L = Lift1(S, d)
            if u + 2 * d >= 1:
                note('`LiftStage−1`（段を 1 下げた）',
                     ref.inW(L, u + 2 * d - 1))
        for M2 in h61.variants_row1_up(S):
            note('`Row1MonoUp`（行 1 を上げた）', ref.inW(M2, u))
        if S and all(entry(S, 0, j) > entry(S, 0, 0) for j in range(1, len(S))):
            for e in (1, 2):
                for n in (2, 3):
                    T = h61.shTower(S, e, n)
                    if len(T) <= 9 and u >= 1:
                        note('`ShiftTower−1`（段を 1 下げた）',
                             ref.inW(T, u - 1))
    # ---- WCat−1
    short = [(S, u) for S, u in dec if len(S) <= 2]
    for A, mA in short[:400]:
        for B, mB in short[:400]:
            u = max(mA, mB)
            if u >= 1 and len(A) + len(B) <= 6:
                note('`WCat−1`（段を 1 下げた）', ref.inW(A + B, u - 1))
    # ---- TowerOK−1
    rcols = [(a, b, c) for a in range(1, 4) for b in range(3) for c in range(2)]
    for L in (1, 2, 3):
        for R in itertools.product(rcols, repeat=L):
            R = list(R)
            if dom_m(R) is None:
                continue
            s = srow(R, len(R) - 1)
            for v in range(3):
                for z in range(2):
                    M = [(0, v, z)] + R
                    if not has_parent(M, s, len(R)):
                        continue
                    a = 2 * v + z
                    if a < 1:
                        continue
                    out = 'OK'
                    for n in (1, 2, 3):
                        r = ref.inW(trio.expand(list(M), n), a - 1)
                        if r is False:
                            out = 'F'
                            break
                        if r is None:
                            out = 'N'
                    note('`TowerOK−1`（段を 1 下げた）',
                         False if out == 'F' else (None if out == 'N' else True))
    for name in sorted(res):
        wref.tally(res[name], name + ' —— **違反が出るべき**')


if __name__ == '__main__':
    main(lens=(1, 2))
    print()
    main(lens=(3,))
