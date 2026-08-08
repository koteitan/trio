"""Is `W u` closed under plain concatenation, with NO side condition?

`Wset.W_add` needs `rsum A B` ("B's root is the shallowest column of A ++ B"),
which is what its `XA_closed` PROOF needs: with B shallowest, the bad root of
`A ++ B` cannot escape B, so the expansion stays `A ++ B[j]`.  The first pass of
`probe_wadd.py` found no violation of

    (CAT)   A in W u  ->  B in W u  ->  A ++ B in W u

on 23600 pairs even without any hypothesis.  If (CAT) really is unconditional it
closes `(TOW)` (`shTower Q e (n+1) = shTower Q e n ++ shiftr01 (n*e) 0 Q`, and
`W_shift` gives the second summand) and with it the last `(WL)` branch.

A claim this strong needs a harder look before it is believed, so this script
re-runs it with a deeper decision procedure (MAXDEPTH/MAXLEN raised), a richer
column set, longer operands, and a randomised sweep over sequences well outside
the exhaustive range.  Reported in minstage form:

    minstage(A ++ B) <= max(minstage A, minstage B)

`undecided` counts pairs the bounded search could not settle; those are NOT
evidence either way.
"""
import sys
import random
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXDEPTH = 10
MAXLEN = 40
AMAX = 16


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


def minstage(S, memo):
    for a in range(AMAX + 1):
        r = inW(S, a, MAXDEPTH, memo)
        if r is True:
            return a
        if r is None:
            return None
    return None


COLS = [(a, b, c) for a in range(4) for b in range(3) for c in range(2)]


def check(A, B, memo, tot, ex, tag):
    mA = minstage(A, memo)
    mB = minstage(B, memo)
    if mA is None or mB is None:
        tot[tag + '/undecided'] += 1
        return
    m = minstage(A + B, memo)
    if m is None:
        tot[tag + '/undecided'] += 1
        return
    tot[tag] += 1
    if m > max(mA, mB):
        tot[tag + '/VIOL'] += 1
        if len(ex) < 5:
            ex.append((tag, A, B, mA, mB, m))
    elif m < max(mA, mB):
        tot[tag + '/slack'] += 1


def st_ts_population(limit=400):
    """Sequences actually reachable by BM4 from the z<2 generators."""
    seen, frontier = set(), []
    for v in range(5):
        S = tuple(trio.diag(3, v, zcap=1))
        seen.add(S)
        frontier.append((S, 0))
    while frontier and len(seen) < limit:
        S, dep = frontier.pop()
        if dep >= 5:
            continue
        for n in NS:
            T = tuple(trio.expand(list(S), n))
            if T and len(T) <= 12 and T not in seen:
                seen.add(T)
                frontier.append((T, dep + 1))
    out = set(seen)
    for S in list(seen):
        for k in range(1, len(S)):
            out.add(S[:k])
    return [list(s) for s in out]


def main():
    memo = {}
    tot = Counter()
    ex = []
    # (1) exhaustive over short sequences, richer columns than the first pass
    short = []
    for L in (1, 2):
        for S in itertools.product(COLS, repeat=L):
            short.append(list(S))
    print('exhaustive operands:', len(short))
    for A in short:
        for B in short:
            check(A, B, memo, tot, ex, 'exh')
    # (2) longer operands, randomised
    rng = random.Random(20260808)
    long3 = [[rng.choice(COLS) for _ in range(rng.randint(3, 5))]
             for _ in range(600)]
    for A in long3:
        for B in rng.sample(short, 40):
            check(A, B, memo, tot, ex, 'rnd')
        for B in rng.sample(long3, 6):
            check(A, B, memo, tot, ex, 'rnd')
    # (3) real BM4 sequences (ST_TS and their prefixes)
    pop = st_ts_population()
    print('ST_TS operands:', len(pop))
    for A in pop:
        for B in pop:
            check(A, B, memo, tot, ex, 'stts')
    print(f"{'case':18s} {'count':>10s}")
    for k in sorted(tot):
        print(f"{k:18s} {tot[k]:10d}")
    for e in ex:
        print('  ex', e)


if __name__ == '__main__':
    main()
