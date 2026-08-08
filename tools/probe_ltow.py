"""(LTOW) — the lifted copy tower, the suspected COMMON core of the two residues.

Both remaining residues produce the same object:

  * `(SNOC)` with `i1 = 2`: `(C ++ [p])[n] = C.take j0 ++ (copies of C.drop j0)`,
    copy `k` shifted by `k*d0` in row 0 and lifted by `k*d1` on the row-1 cone of
    the copy root.
  * `TowerExp2`: `((0,v,z) :: R)[n]` with `j0 = 0` is literally that, with
    window `M.dropLast`.

With `X` the re-based window, copy `k` is `shiftr01 (k*d0) 0 (Lift1 X (k*d1))`,
so both reduce to

    (LTOW)  X in W u  ->  concat_{k<n} shiftr01 (k*d0) 0 (Lift1 X (k*d1))  in W u

`d1 = 0` is the already-isolated `(TOW) ShiftTowerClosed`.  The genuine content
is `d1 > 0`, which is exactly what `(CAT)` cannot reach (copy `k` alone sits at
stage `u + 2*k*d1`).

Side conditions read off the expansion rule:
  (a) `X` is based: `entry X 0 0 = 0`
  (b) the guard column sits at depth `d0 > 0` with no dip, so every non-root
      column of `X` is at depth `>= d0`
  (c) `d1` is the row-1 gap between the guard column and the copy root

This probe measures (LTOW) under (a)+(b), over all `d1`, and reports which
extra condition (if any) the `d1 > 0` case needs.
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXDEPTH = 9
MAXLEN = 44
AMAX = 12


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    if S[j][2] > 0:
        return 2
    if S[j][1] > 0:
        return 1
    return 0


def inW(S, a, depth, memo):
    S = tuple(tuple(c) for c in S)
    key = (S, a)
    if key in memo:
        return memo[key]
    if len(S) == 0:
        return True
    if len(S) == 1:
        r = lev(S[0]) <= a
        memo[key] = r
        return r
    if depth <= 0 or len(S) > MAXLEN:
        return None
    memo[key] = None
    out = True
    for n in NS:
        r = inW(trio.expand(list(S), n), a, depth - 1, memo)
        if r is False:
            memo[key] = False
            return False
        if r is None:
            out = None
    memo[key] = out
    return out


def minstage(S, memo):
    for a in range(AMAX + 1):
        r = inW(S, a, MAXDEPTH, memo)
        if r is True:
            return a
        if r is None:
            return None
    return None


def cone0(X):
    return [j for j in range(len(X)) if trio.is_ancestor(X, 1, 0, j)]


def lift1(X, d):
    C = set(cone0(X))
    return [(c[0], c[1] + d, c[2]) if j in C else c for j, c in enumerate(X)]


def tower(X, d0, d1, n):
    out = []
    for k in range(n):
        Y = lift1(X, k * d1)
        out += [(c[0] + k * d0, c[1], c[2]) for c in Y]
    return out


def main():
    memo = {}
    tot = Counter()
    ex = []
    COLS = [(x, b, c) for x in range(1, 4) for b in range(3) for c in range(2)]
    ROOTS = [(0, b, c) for b in range(3) for c in range(2)]
    for r in ROOTS:
        for L in (0, 1, 2):
            for tail in itertools.product(COLS, repeat=L):
                X = [r] + list(tail)
                u = minstage(X, memo)
                if u is None:
                    tot['X undecided'] += 1
                    continue
                for d0 in (1, 2):
                    if any(c[0] < d0 for c in X[1:]):
                        continue                     # side condition (b)
                    for d1 in (0, 1, 2):
                        for n in (2, 3):
                            T = tower(X, d0, d1, n)
                            if len(T) > MAXLEN:
                                continue
                            s = minstage(T, memo)
                            tag = 'd1=0' if d1 == 0 else 'd1>0'
                            if s is None:
                                tot[tag + '/undecided'] += 1
                            elif s <= u:
                                tot[tag + '/ok'] += 1
                            else:
                                tot[tag + '/FAIL'] += 1
                                if len(ex) < 8:
                                    ex.append((X, u, d0, d1, n, s, T))
    for k in sorted(tot):
        print(f'  {k:18s} {tot[k]:8d}')
    for X, u, d0, d1, n, s, T in ex:
        print(f'  FAIL X={X} u={u} d0={d0} d1={d1} n={n} -> stage {s}')
        print(f'       T={T}')


if __name__ == '__main__':
    main()
