"""(TB) `tbAll X u -> tbAll (X[n]) u`, hardened.

`tbAll X u  :=  every column of `X` that has no parent (in its own `srow`) has
level `< u`.  Equivalently `u0(X) < u` where

    u0(X) := max { lev X j | j parentless in X }        (0 if none)

so (TB) is exactly **`u0 (X[n]) <= u0 X`**.  That is what this probe measures.

Why it matters: with the `natDom` guard on `Aop` clause 2, `Wstar` needs the
side condition `tbAll R a` (otherwise the guard is refuted -- see
GRAFTALL-PLAN 4.5).  The condition has to survive the three recursive sites of
`Wstar_closed`:

    R.dropLast   -- `tbAll_take`   (proved)
    graft R y    -- `tbAll_graft`  (proved; needs `y in W m -> tbAll y m`)
    R[n]         -- **this probe**  (= the old `Wset.TbOper`)

Structural reason to expect it: a copy's row 1 is lifted by `k*d1`, and
`d1 > 0` only when `i1 = srow X (|X|-1) = 2`, in which case the copy root `j0`
is the row-2 parent of the last column, so `entry X 2 j0 = 0`.  Any row-2
column in `j0`'s row-1 cone therefore HAS a row-2 parent (`j0` or nearer), i.e.
parentless row-2 columns are never inside the lifted cone.  Parentless row-1
columns are in nobody's row-1 cone by definition.  So no parentless column is
ever lifted.

Checks:
 (A) exhaustive short blocks, one step, n = 1..4
 (B) random longer/deeper blocks, one step, n = 1..4
 (C) iterated descent (apply oper repeatedly) from standard-looking matrices
 (D) how many hosts actually exercise the risky case (i1 = 2, d1 > 0)
"""
import sys
import random
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

MAXLEN = 60


def lev(c):
    return 2 * c[1] + c[2]


def srow(c):
    return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)


def u0(X):
    """max level over parentless columns (0 if there are none)."""
    best = 0
    for j in range(len(X)):
        if lev(X[j]) == 0:
            continue
        if trio.parent(X, srow(X[j]), j) is None:
            best = max(best, lev(X[j]))
    return best


def risky(X):
    """does this host lift its copies (i1 = 2 with a genuine d1)?"""
    j1 = len(X) - 1
    if j1 <= 0:
        return False
    i1 = srow(X[j1])
    if i1 != 2:
        return False
    j0 = trio.parent(X, i1, j1)
    if j0 is None:
        return False
    return X[j1][1] > X[j0][1]


def check(X, tot, ex, ns=(1, 2, 3, 4)):
    b = u0(X)
    tot['host'] += 1
    if risky(X):
        tot['host/lifted-copies'] += 1
    for n in ns:
        E = trio.expand(list(X), n)
        if len(E) > MAXLEN:
            tot['skip/too-long'] += 1
            continue
        tot['inst'] += 1
        e = u0(E)
        if e > b:
            tot['VIOLATION'] += 1
            if len(ex) < 5:
                ex.append((X, n, b, e, E))
        elif e < b:
            tot['drop'] += 1
        else:
            tot['equal'] += 1


def main():
    tot = Counter()
    ex = []
    rng = random.Random(20260809)

    # (A) exhaustive short blocks
    cols = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]
    for L in (2, 3):
        for X in itertools.product(cols, repeat=L):
            check(list(X), tot, ex)
    print('(A) after exhaustive L=2,3 :', tot['inst'], 'inst,',
          tot['VIOLATION'], 'violations')

    # (B) random longer blocks
    for _ in range(40000):
        L = rng.randint(2, 8)
        X = [(rng.randint(0, 5), rng.randint(0, 4), rng.randint(0, 1))
             for _ in range(L)]
        check(X, tot, ex)
    print('(B) after random blocks    :', tot['inst'], 'inst,',
          tot['VIOLATION'], 'violations')

    # (C) iterated descent from standard-looking matrices
    seeds = []
    for v in range(4):
        for z in range(2):
            seeds.append(trio.diag(3, v, z))
    base = [(0, 0, 0)]
    for a in range(1, 4):
        for b in range(3):
            for c in range(2):
                seeds.append(base + [(1, b, c), (a, b, c)])
    for S in seeds:
        X = list(S)
        for _ in range(14):
            if len(X) < 2 or len(X) > MAXLEN:
                break
            check(X, tot, ex, ns=(1, 2))
            X = trio.expand(list(X), 2)
    print('(C) after iterated descent :', tot['inst'], 'inst,',
          tot['VIOLATION'], 'violations')

    print()
    for k in sorted(tot):
        print(f'  {k:24s} {tot[k]:9d}')
    for X, n, b, e, E in ex:
        print(f'  CEX X={X} n={n} u0(X)={b} -> u0(X[n])={e}')
        print(f'      X[n]={E}')


if __name__ == '__main__':
    main()
