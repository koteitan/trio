"""Is `TowerExp2` actually TRUE?

`TowerExp2` (Wset.TowerExp restricted to `srow R (|R|-1) = 2`):

    argOK R, R /= [], z <= 1, 2v+z <= a,
    domT R m, srow R (|R|-1) = 2,
    (forall n >= 1, R[n] in Wstar),                     -- R[n] = Pred R = R.dropLast
    hasParent ((0,v,z) :: R) (srow R (|R|-1)) |R|       -- the root revives the orphan
    ==> forall n >= 1, ((0,v,z) :: R)[n] in W a

It is the last residue besides `(SNOC)`, and it has never been measured.
`Wchar` makes the conclusion equivalent to `M = (0,v,z) :: R in W a` whenever
`|M| >= 2`, so we test

    hypothesis:  minstage ((0,v',z') :: R.dropLast) <= 2v'+z'   on a grid of (v',z')
    conclusion:  minstage ((0,v,z) :: R)            <= 2v+z

`inW` decides the UNGUARDED `W` through `Wchar` (`|S|>=2  <->  all S[n] in W a`),
so it is an approximation: `None` = undecided within the search bounds.
Undecided instances are reported separately and never counted as passes.
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXDEPTH = 10
MAXLEN = 40
AMAX = 14
GRID = [(vp, zp) for vp in range(3) for zp in range(2)]


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


def le_stage(S, a, memo):
    """True / False / None for `S in W a`."""
    return inW(S, a, MAXDEPTH, memo)


def main():
    memo = {}
    tot = Counter()
    ex = []
    COLS = [(x, b, c) for x in range(1, 4) for b in range(4) for c in range(2)]
    for v in range(3):
        for z in range(2):
            for L in (1, 2, 3):
                for R in itertools.product(COLS, repeat=L):
                    R = list(R)
                    x = len(R) - 1
                    if srow(R, x) != 2:
                        continue
                    if lev(R[x]) == 0:
                        continue
                    if trio.parent(R, 2, x) is not None:
                        continue                      # need domT R m
                    M = [(0, v, z)] + R
                    if trio.parent(M, 2, len(R)) is None:
                        continue                      # need the root to revive it
                    tot['row-2 revival host'] += 1
                    # hypothesis: R.dropLast in Wstar, tested on the grid
                    D = R[:-1]
                    hyp = True
                    for (vp, zp) in GRID:
                        r = le_stage([(0, vp, zp)] + D, 2 * vp + zp, memo)
                        if r is False:
                            hyp = False
                            break
                        if r is None:
                            hyp = None
                            break
                    if hyp is None:
                        tot['hyp undecided'] += 1
                        continue
                    if hyp is False:
                        tot['hyp fails'] += 1
                        continue
                    tot['hyp holds'] += 1
                    c = le_stage(M, 2 * v + z, memo)
                    if c is True:
                        tot['CONCLUSION ok'] += 1
                    elif c is None:
                        tot['concl undecided'] += 1
                    else:
                        tot['CONCLUSION FAIL'] += 1
                        if len(ex) < 8:
                            ex.append((v, z, R, 2 * v + z))
    for k in sorted(tot):
        print(f'  {k:22s} {tot[k]:8d}')
    for v, z, R, a in ex:
        M = [(0, v, z)] + R
        print(f'  FAIL v={v} z={z} a={a}  M={M}')
        print(f'       M[1]={trio.expand(list(M), 1)}')
        print(f'       M[2]={trio.expand(list(M), 2)}')


if __name__ == '__main__':
    main()
