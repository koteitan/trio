"""Does the ambient root lift raise the `W`-stage by exactly `2d`?

The yapss (pair-sequence) proof closes `Wstar_closed` with NO context, NO lift
and NO cores, because there

    Wstar = {R | argOK R -> forall v, (0,v) :: R  in  W v}

and the only tower is the row-1 one, whose data come straight from `Aop`'s
clause 3 (`W_mono` lifts `tow k in W v` to `tow k in W m` using `v <= m`).

Trio needs the ambient lift `Lift1 . t` because the ROW-2 collapse's copies
ascend in row 1, i.e. the tower data appear ROOT-LIFTED.  The clean way to
absorb that would be

    (WL)   X in W m   ->   Lift1 X d  in  W (m + 2*d)

("the root lift costs exactly `2d` stages", matching `lev = 2*row1 + row2`).
`oper` does NOT commute with `Lift1` (the lifted composite's inner tower heads
sit at `v+d` while `Lift1 (X[n]) d` keeps them at `v`), so (WL) cannot be got by
naive transport — hence this measurement.

`W a` is characterised exactly (Lean: `Wchar.lean`) by

    |S| = 0            -> in W a
    |S| = 1            -> in W a  <->  lev <= a
    |S| >= 2           -> in W a  <->  forall n >= 1, S[n] in W a

so `minstage(S)` = least `a` with the expansion tree closing on roots of level
<= a.  Reported: instances where `minstage(Lift1 X d) > minstage(X) + 2d`.
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXDEPTH = 8
MAXLEN = 24
AMAX = 14


def lev(col):
    return 2 * col[1] + col[2]


def lift1(S, d):
    return [(c[0], c[1] + (d if trio.is_ancestor(S, 1, 0, i) else 0), c[2])
            for i, c in enumerate(S)]


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
    """Least a <= AMAX with S in W a, or None if undecided / not found."""
    for a in range(AMAX + 1):
        r = inW(S, a, MAXDEPTH, memo)
        if r is True:
            return a
        if r is None:
            return None
    return 'over'


COLS = [(d, b, c) for d in range(0, 3) for b in range(3) for c in range(2)]

tot = Counter()
ex = {}
memo = {}

for L in (1, 2, 3):
    for X in itertools.product(COLS, repeat=L):
        X = list(X)
        m = minstage(X, memo)
        if not isinstance(m, int):
            tot['base/undecided'] += 1
            continue
        tot['base/ok'] += 1
        for d in range(1, 4):
            Y = lift1(X, d)
            m2 = minstage(Y, memo)
            if not isinstance(m2, int):
                tot[f'lift/undecided'] += 1
                continue
            key = 'lift/d=%d' % d
            tot[key] += 1
            if m2 > m + 2 * d:
                tot[key + '/VIOL'] += 1
                ex.setdefault(key, (X, d, m, m2, Y))
            elif m2 < m + 2 * d:
                tot[key + '/slack'] += 1

print(f"{'case':22s} {'count':>9s}")
for k in sorted(tot):
    print(f"{k:22s} {tot[k]:9d}")
for k, e in sorted(ex.items()):
    print(f"  ex {k}: {e}")
