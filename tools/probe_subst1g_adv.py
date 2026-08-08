"""ADVERSARIAL hunt for a counterexample to `(SUBST1g)` — the single core.

`probe_subst1g.py` (210201 instances, 0 violations) was CONFIRMATORY: exhaustive
short hosts with a fixed list of toy tails.  `audit_subst1g_stts.py` showed that
genuine ST_TS matrices are simply not decidable by `inW` (deciding them IS the
termination problem), so a deep confirmatory audit is not available.

So this probe tries to REFUTE instead, and aims at the danger zone that
`probe_subst1_ind.py` identified: the cases the host's own datum does NOT close,

  * `p >= badroot S`   — the insertion lands inside the copied region
  * `p = |S|-1` with `R`'s bad root left of `p` — the context revives a column
    that is an orphan inside its own block
  * `badroot S = None` but the insertion creates a parent for `S`'s last column

Those are exactly the shapes that killed A_x1 == 1, W2ok, spanOK and dichOK.
Hosts and blocks are drawn at random over a much wider column range than the
exhaustive probe, with dips allowed, and only the residue cases are counted.
"""
import sys
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXDEPTH = 11
MAXLEN = 44
AMAX = 16
SAMPLES = 400000


def lev(col):
    return 2 * col[1] + col[2]


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


def badroot(S):
    if not S:
        return None
    x = len(S) - 1
    Y = len(S[0])
    if all(val == 0 for val in S[x]):
        return None
    t = max(y for y in range(Y) if S[x][y] > 0)
    return trio.parent(S, t, x)


def subst(X, p, C):
    return list(X[:p]) + list(C) + list(X[p + 1:])


def rand_host(rng):
    L = rng.randint(2, 5)
    S = [(0, rng.randint(0, 4), rng.randint(0, 1))]
    for _ in range(L - 1):
        S.append((rng.randint(1, 5), rng.randint(0, 4), rng.randint(0, 1)))
    return S


def rand_block(rng, x):
    """A block rooted at depth `x`, every other column strictly deeper."""
    L = rng.randint(1, 4)
    C = [(x, rng.randint(0, 4), rng.randint(0, 1))]
    for _ in range(L - 1):
        C.append((x + rng.randint(1, 5), rng.randint(0, 4), rng.randint(0, 1)))
    return C


def main():
    rng = random.Random(20260809)
    memo = {}
    tot = Counter()
    ex = []
    for _ in range(SAMPLES):
        S = rand_host(rng)
        p = rng.randrange(len(S))
        C = rand_block(rng, S[p][0])
        R = subst(S, p, C)
        if len(R) > MAXLEN:
            continue
        # classify first: only the residue shapes are interesting
        j0S = badroot(S)
        j0R = badroot(R)
        if p < len(S) - 1:
            mirror = all(len(trio.expand(list(S), n)) > p
                         and trio.expand(list(R), n)
                         == subst(trio.expand(list(S), n), p, C)
                         for n in (1, 2, 3))
            if mirror:
                tot['skip/(MIRROR)'] += 1
                continue
        else:
            inner = all(trio.expand(list(R), n)
                        == list(S[:p]) + trio.expand(list(C), n)
                        for n in (1, 2, 3))
            if inner:
                tot['skip/(INNER)'] += 1
                continue
        if p == len(S) - 1:
            shape = 'residue/context-revives'
        elif j0S is None:
            shape = 'residue/insertion-creates-parent'
        elif p >= j0S:
            shape = 'residue/inside-copied-region'
        else:
            shape = 'residue/other'
        # now the hypotheses
        stages = [a for a in range(AMAX + 1) if inW(S, a, MAXDEPTH, memo) is True]
        if not stages:
            tot['host/no-decided-stage'] += 1
            continue
        if inW(C, lev(S[p]), MAXDEPTH, memo) is not True:
            tot['block/not in W(lev)'] += 1
            continue
        for a in stages:
            r = inW(R, a, MAXDEPTH, memo)
            if r is None:
                tot[shape + '/undecided'] += 1
                continue
            tot[shape] += 1
            if r is False:
                tot[shape + '/VIOLATION'] += 1
                if len(ex) < 8:
                    ex.append((S, a, p, C, R, j0S, j0R))
    for k in sorted(tot):
        print(f'  {k:38s} {tot[k]:10d}')
    for S, a, p, C, R, j0S, j0R in ex:
        print(f'  VIOLATION a={a} p={p} badroot S={j0S} badroot R={j0R}')
        print(f'    S={S}')
        print(f'    C={C}')
        print(f'    R={R}')


if __name__ == '__main__':
    main()
