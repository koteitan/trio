# -*- coding: utf-8 -*-
"""**課題 H57-d: 残りの核のうち「仮定が純 `∈ W`」のものを一括で測る。**

    `LiftStage`        `Wtower2:36`    `X ∈ W m → Lift1 X d ∈ W (m+2d)`
    `LiftTie`          `L53Subst:2337` 根にタイがある場合の (WL)
    `Row1Mono`         `Wtower2:151`   行 1 を下げても段は上がらない
    `WConvex`          `Wtower2:450`   `A ∈ W a, C ∈ W a, A ≤1 B ≤1 C → B ∈ W a`
    `Row1DownLocal`    `L53Subst:2574` `mlift X (v0-1) d ∈ W a → Lift1 X d ∈ W a`
    `Row1DownRoot0`    `L53Subst:2579` `v0 = 0` の場合、台は一様シフト
    `Row0Free`         `Wtower2:262`   ⚠ 強すぎ（`mem_W_of_row0free`）。**測って確かめる**
    `ShiftTowerClosedS``Wtower2:1771`  `Q ∈ W u`（狭義深さ）→ `shTower Q e n ∈ W u`

どれも仮定が `∈ W` と決定可能な構文条件だけなので、**反証は健全**。
"""
import sys, itertools, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import Ref, fmt, entry, levM, argOK, Lift1, shiftr01
from collections import Counter

AMAX = 12


def anc0(S, j):
    """行 0 祖先（自身を含む）の添字集合。"""
    out = []
    while j is not None:
        out.append(j)
        j = trio.parent(list(S), 0, j)
    return out


def coneV(S, v, j):
    """lean/Cgraft.lean:301 —— 行 0 祖先が全部 行 1 > v。"""
    return all(S[y][1] > v for y in anc0(S, j))


def mlift(S, v, d):
    return [(c[0], c[1] + (d if coneV(S, v, i) else 0), c[2])
            for i, c in enumerate(S)]


def shTower(Q, e, n):
    out = []
    for k in range(n):
        out += shiftr01(k * e, 0, Q)
    return out


def verd(r):
    return '**違反**' if r is False else 'OK' if r is True else '未判定'


def main(lens=(1, 2, 3), tag=''):
    ref = Ref(ns=(1, 2, 3), maxdepth=9, maxlen=34, maxnodes=60000)
    wref.print_controls(ref)
    cols = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]
    pool = []
    for L in lens:
        for S in itertools.product(cols, repeat=L):
            pool.append(list(S))
    print('## 母集団%s' % tag)
    print()
    print('列 = 行0<3・行1<3・行2<2、長さ %s ⟹ **%d** 本' % (list(lens), len(pool)))
    dec = [(S, ref.minstage(S, AMAX)) for S in pool]
    dec = [(S, u) for S, u in dec if u is not None]
    print('うち段が確定したもの: **%d**' % len(dec))
    print()

    res = {}
    exs = {}

    def note(name, r, wit):
        res.setdefault(name, Counter())[verd(r)] += 1
        if r is False:
            exs.setdefault(name, [])
            if len(exs[name]) < 4:
                exs[name].append(wit)

    rows = []
    for S, u in dec:
        # ---------------- LiftStage / LiftTie / Row1Down*
        for d in (1, 2):
            L = Lift1(S, d)
            r = ref.inW(L, u + 2 * d)
            note('`LiftStage`', r, (S, u, d))
            if d == 1:
                rows.append((verd(r), S))
            # LiftTie: 根つきで、行 1 に根とのタイがある場合だけ
            if S and S[0][0] == 0 and argOK(S[1:]) and \
               any(q[1] == S[0][1] for q in S[1:]):
                note('`LiftTie`（タイのある根）', r, (S, u, d))
            # Row1DownLocal: 台は `mlift X (v0-1) d ∈ W a`
            v0 = entry(S, 1, 0)
            if v0 >= 1:
                base = mlift(S, v0 - 1, d)
                for a in range(u, u + 2 * d + 1):
                    if ref.inW(base, a) is True:
                        note('`Row1DownLocal`', ref.inW(L, a), (S, a, d))
                        break
            else:
                base = shiftr01(0, d, S)
                for a in range(u, u + 2 * d + 1):
                    if ref.inW(base, a) is True:
                        note('`Row1DownRoot0`', ref.inW(L, a), (S, a, d))
                        break
        # ---------------- Row1Mono / WConvex / Row0Free
        for M2 in variants_row1(S):
            note('`Row1Mono`', ref.inW(M2, u), (S, M2, u))
        for M2 in variants_row0(S):
            note('`Row0Free` ⚠', ref.inW(M2, u), (S, M2, u))
        # ---------------- ShiftTowerClosedS（狭義に深い場合だけ）
        if S and all(entry(S, 0, j) > entry(S, 0, 0)
                     for j in range(1, len(S))):
            for e in (1, 2):
                for n in (2, 3):
                    T = shTower(S, e, n)
                    if len(T) <= 9:
                        note('`ShiftTowerClosedS`', ref.inW(T, u), (S, e, n, u))
    # ---------------- WConvex: A ≤1 B ≤1 C の三つ組
    conv = Counter()
    exc = []
    for S, u in dec:
        for C2 in variants_row1_up(S):
            rC = ref.inW(C2, u)
            if rC is not True:
                continue
            for B in between_row1(S, C2):
                r = ref.inW(B, u)
                conv[verd(r)] += 1
                if r is False and len(exc) < 4:
                    exc.append((S, B, C2, u))
    res['`WConvex`'] = conv
    if exc:
        exs['`WConvex`'] = exc

    for name in sorted(res):
        wref.tally(res[name], name)
        for w in exs.get(name, []):
            print('    反例: %s' % (tuple(fmt(x) if isinstance(x, list) else x
                                        for x in w),))
        if exs.get(name):
            print()
    wref.degeneracy(rows)


def variants_row1(S):
    """行 1 を 1 本だけ 1 下げた列（`Row1Mono` の前提を満たす）。"""
    out = []
    for j in range(len(S)):
        if S[j][1] > 0:
            T = list(S)
            T[j] = (T[j][0], T[j][1] - 1, T[j][2])
            out.append(T)
    return out


def variants_row1_up(S):
    """行 1 を 1 本だけ 1 上げた列（`WConvex` の上端の候補）。"""
    out = []
    for j in range(len(S)):
        T = list(S)
        T[j] = (T[j][0], T[j][1] + 1, T[j][2])
        out.append(T)
    return out


def between_row1(A, C):
    """`Le1 A B` かつ `Le1 B C` の `B`（A と C の行 1 の間）。"""
    diff = [j for j in range(len(A)) if A[j][1] != C[j][1]]
    out = []
    for j in diff:
        for v in range(A[j][1] + 1, C[j][1] + 1):
            T = list(A)
            T[j] = (T[j][0], v, T[j][2])
            out.append(T)
    return out


def variants_row0(S):
    """行 1・行 2 を保ったまま行 0 だけ動かした列（`Row0Free` の前提）。"""
    out = []
    for j in range(len(S)):
        for dd in (-1, 1):
            if S[j][0] + dd < 0:
                continue
            T = list(S)
            T[j] = (T[j][0] + dd, T[j][1], T[j][2])
            out.append(T)
    # 深さを全部 0 に潰した列（docstring の `mem_W_of_row0free` の台）
    out.append([(0, c[1], c[2]) for c in S])
    return out


if __name__ == '__main__':
    main(lens=(1, 2), tag='（長さ 1..2）')
    print()
    main(lens=(3,), tag='（長さ 3 だけ）')
