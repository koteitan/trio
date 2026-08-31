# -*- coding: utf-8 -*-
"""**課題 H49-0 —— `TowerOK2` の場面で `v >= 1` は本当に無いか。**

条件（`lean/Wset.lean:4365` / `L53Subst.lean:1122`）:

    argOK R              全列の行 0 が > 0
    R != []
    srow R (|R|-1) = 2   末尾の行 2 が > 0
    domT R               末尾が **R の中で孤児**、lev > 0
    hasParent ((0,v,z) :: R) 2 |R|    根を付けると行 2 の親ができる

`v` は `Wstar_closed` で**全称**なので `R` とは独立に振ってよい。
**`R` は人工的に持ち上げず、自然に出てくるものだけを使う。**
"""
import sys, io, contextlib, itertools, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter

VMAX = 8


def srow(S, j):
    c = S[j]
    return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)


def hp(S, j):
    return trio.parent([tuple(c) for c in S], srow(S, j), j) is not None


def ok_scene(R, v, z=0):
    """`(0,v,z) :: R` が `TowerOK2` の場面か。"""
    j = len(R) - 1
    if not R or not all(p[0] > 0 for p in R):
        return False
    if srow(R, j) != 2:
        return False
    if 2 * R[j][1] + R[j][2] == 0:
        return False
    if hp(R, j):
        return False                      # domT: R の中で孤児
    M = [(0, v, z)] + list(R)
    return trio.parent([tuple(c) for c in M], 2, len(R)) is not None


def vset(R):
    """この `R` で場面になる `v` の集合（z=0 と z=1 の両方）。"""
    return {(v, z) for v in range(VMAX + 1) for z in (0, 1) if ok_scene(R, v, z)}


if __name__ == '__main__':
    print('**(A) 小さい `R` の全数**（行 0 は 1..4、行 1 は 0..4、行 2 は 0..1）')
    COLS = [(a, b, c) for a in range(1, 5) for b in range(5) for c in range(2)]
    print('   柱 %d 本' % len(COLS))
    cnt = Counter()
    ex = {}
    tot = 0
    for L in (1, 2, 3):
        for R in itertools.product(COLS, repeat=L):
            R = list(R)
            S = vset(R)
            if not S:
                continue
            tot += 1
            for v, z in S:
                cnt[(v, z)] += 1
                if (v, z) not in ex:
                    ex[(v, z)] = R
    print('   場面になる `R` は %d 本（長さ 1..3 の全数 %d 本から）'
          % (tot, sum(len(COLS) ** L for L in (1, 2, 3))))
    print('   | `v` | `z` | 件数 | 最小の例 |')
    print('   |--:|--:|--:|---|')
    for k in sorted(cnt):
        print('   | %d | %d | %d | `%s` |'
              % (k[0], k[1], cnt[k],
                 ''.join('(%d,%d,%d)' % q for q in ex[k])))
    if not any(k[0] >= 1 for k in cnt):
        print('   ⟹ **`v >= 1` は 0 件**')
    print()

    print('**(B) 長さ 4 の `R` を無作為に**')
    rng = random.Random(20260829)
    cnt2 = Counter()
    ex2 = {}
    for _ in range(400000):
        R = [rng.choice(COLS) for _ in range(4)]
        for v, z in vset(R):
            cnt2[(v, z)] += 1
            if (v, z) not in ex2:
                ex2[(v, z)] = list(R)
    print('   | `v` | `z` | 件数 | 最小の例 |')
    print('   |--:|--:|--:|---|')
    for k in sorted(cnt2):
        print('   | %d | %d | %d | `%s` |'
              % (k[0], k[1], cnt2[k],
                 ''.join('(%d,%d,%d)' % q for q in ex2[k])))
    if not any(k[0] >= 1 for k in cnt2):
        print('   ⟹ **`v >= 1` は 0 件**')
    print()

    print('**(C) 自然な標準形プール（`trio.diag(3,v)` からの展開閉包）の接尾辞**')
    seen, fr = set(), []
    for v in range(5):
        S = tuple(tuple(c) for c in trio.diag(3, v, zcap=1))
        if S:
            seen.add(S)
            fr.append(S)
    while fr and len(seen) < 60000:
        S = fr.pop()
        for n in (1, 2, 3):
            T = tuple(tuple(c) for c in trio.expand(list(S), n))
            if T and len(T) <= 10 and T not in seen:
                seen.add(T)
                fr.append(T)
    P = list(seen)
    print('   標準形 %d 本。その**接尾辞** `M[j:]`（`argOK` なもの）を `R` にする' % len(P))
    cnt3 = Counter()
    ex3 = {}
    nR = 0
    for M in P:
        for j in range(1, len(M)):
            R = list(M[j:])
            if not all(p[0] > 0 for p in R):
                continue
            S = vset(R)
            if not S:
                continue
            nR += 1
            for v, z in S:
                cnt3[(v, z)] += 1
                if (v, z) not in ex3:
                    ex3[(v, z)] = (M, j, R)
    print('   場面になる (M, j) は %d 件' % nR)
    print('   | `v` | `z` | 件数 | 最小の例 |')
    print('   |--:|--:|--:|---|')
    for k in sorted(cnt3):
        M, j, R = ex3[k]
        print('   | %d | %d | %d | `M=%s` の `j=%d` 以降 |'
              % (k[0], k[1], cnt3[k], ''.join('(%d,%d,%d)' % q for q in M), j))
    if not any(k[0] >= 1 for k in cnt3):
        print('   ⟹ **`v >= 1` は 0 件**')
