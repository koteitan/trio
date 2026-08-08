"""Does (CAT) reduce to appending ONE column?

Running `A2'` on `S = {B | A ++ B in W u}` with the `rsum`-free append identity

    (AP)  2 <= |B| /\ hasParent B (srow B (|B|-1)) (|B|-1)
          ->  (A ++ B)[n] = A ++ B[n]                      [probe_capstack: 0 viol]

every clause reduces to appending a single column:

  clause 2, B parented   : (AP) + mem_of_oper_mem                      -- done
  clause 2, B an orphan  : B[n] = Pred B = B.dropLast, so
                           A ++ B.dropLast in W u, and
                           A ++ B = (A ++ B.dropLast) ++ [last]        -- (SNOC)
  clause 3               : graft B [] = B.dropLast, same as above      -- (SNOC)
  clause 1 (|B| <= 1)    : B = [] trivial, B = [p]                     -- (SNOC)

and when the appended column is STILL an orphan in `C ++ [p]` the expansion is
just `Pred`, so that half is free.  What is left is the atomic statement

    (SNOC)  C in W u -> C /= [] -> hasParent (C ++ [p]) (srow ..) |C|
            ->  C ++ [p] in W u

"appending one column that finds a parent does not raise the stage".  Note this
is NOT subsumed by a level bound on `p`: e.g. C = [(0,0,0)], p = (1,5,0) has
lev 10 yet C ++ [p] is in W 0, because the parent turns it into a tower of C's
window.

Measured: (SNOC) in minstage form, plus the orphan half as a control.
"""
import sys
import random
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXDEPTH = 9
MAXLEN = 34
AMAX = 16


def lev(col):
    return 2 * col[1] + col[2]


def srow(S, j):
    if S[j][2] > 0:
        return 2
    if S[j][1] > 0:
        return 1
    return 0


def has_parent(S, j):
    return trio.parent(S, srow(S, j), j) is not None


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


COLS = [(a, b, c) for a in range(4) for b in range(4) for c in range(2)]


def main():
    memo = {}
    tot = Counter()
    ex = []
    rng = random.Random(20260808)
    pool = []
    for L in (1, 2, 3):
        for S in itertools.product(COLS[:16], repeat=L):
            pool.append(list(S))
    pool += [[rng.choice(COLS) for _ in range(rng.randint(2, 5))]
             for _ in range(700)]
    print('C candidates:', len(pool))
    for C in pool:
        mC = minstage(C, memo)
        if mC is None:
            tot['C/undecided'] += 1
            continue
        for p in rng.sample(COLS, 10):
            S = C + [p]
            tag = 'snoc' if has_parent(S, len(C)) else 'orph'
            m = minstage(S, memo)
            if m is None:
                tot[tag + '/undecided'] += 1
                continue
            tot[tag] += 1
            if m > mC:
                tot[tag + '/VIOL'] += 1
                if len(ex) < 8:
                    ex.append((tag, C, p, mC, m))
            elif m < mC:
                tot[tag + '/slack'] += 1
    print(f"{'case':18s} {'count':>10s}")
    for k in sorted(tot):
        print(f"{k:18s} {tot[k]:10d}")
    for e in ex:
        print('  ex', e)


if __name__ == '__main__':
    main()
