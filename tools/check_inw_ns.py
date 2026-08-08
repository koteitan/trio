"""Is the `NS = (1,2)` approximation inside every probe's `inW` sound?

`Wchar` says `M in W a  <->  forall n >= 1, M[n] in W a` (for |M| >= 2), but every
probe in this campaign decides `W` by expanding only `n in {1,2}`.  That is an
OVER-approximation: it can only ACCEPT too much, so a "0 violations" result
could in principle be an artefact.

This check compares the verdicts of `inW` with NS = (1,2), (1,2,3) and (1,2,3,4)
on the same population, and reports every sequence/stage where they differ.
Disagreement would invalidate the probe results; agreement is evidence (not
proof) that the truncation is harmless.
"""
import sys
import itertools
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

MAXDEPTH = 10
MAXLEN = 60
AMAX = 10


def lev(c):
    return 2 * c[1] + c[2]


def inW(S, a, depth, memo, ns):
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
    for n in ns:
        r = inW(trio.expand(list(S), n), a, depth - 1, memo, ns)
        if r is False:
            memo[key] = False
            return False
        if r is None:
            out = None
    memo[key] = out
    return out


def main():
    variants = [(1, 2), (1, 2, 3), (1, 2, 3, 4)]
    memos = [dict() for _ in variants]
    tot = Counter()
    ex = []

    pop = []
    COLS = [(x, b, z) for x in range(3) for b in range(3) for z in range(2)]
    for L in (1, 2, 3):
        for S in itertools.product(COLS, repeat=L):
            S = list(S)
            if S[0][0] != 0:
                continue
            pop.append(S)
    rng = random.Random(20260809)
    for _ in range(4000):                      # wider random tail
        L = rng.randint(2, 5)
        S = [(0, rng.randint(0, 4), rng.randint(0, 1))]
        for _ in range(L - 1):
            S.append((rng.randint(1, 5), rng.randint(0, 4), rng.randint(0, 1)))
        pop.append(S)
    print('population:', len(pop))

    for S in pop:
        for a in range(AMAX + 1):
            rs = [inW(S, a, MAXDEPTH, memos[i], v) for i, v in enumerate(variants)]
            if any(r is None for r in rs):
                tot['undecided by some variant'] += 1
                continue
            tot['decided by all'] += 1
            if rs[0] == rs[1] == rs[2]:
                tot['agree'] += 1
            else:
                tot['DISAGREE'] += 1
                if len(ex) < 8:
                    ex.append((S, a, rs))
    for k in sorted(tot):
        print(f'  {k:26s} {tot[k]:9d}')
    for S, a, rs in ex:
        print(f'  DISAGREE a={a} S={S} verdicts(n<=2, n<=3, n<=4) = {rs}')


if __name__ == '__main__':
    main()
