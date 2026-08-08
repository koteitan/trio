"""(SUBST1g) — the GRAFT-AT-A-POSITION form of `(SUBST1)`.

`(SUBST1)` (measured: 62151 instances, 0 violations) replaces the column at
position `p` of a host by a block whose HEAD IS THAT COLUMN.  `graft` (the
`Aop` clause-3 operation) is more liberal: it replaces the LAST column by a
based block shifted to that column's depth, and the block's head is arbitrary
below the stage.  The position-general version of that is

    (SUBST1g)  S in W u,  p < |S|,  C in W (lev S p),
               (C 0).0 = (S p).0,  every other column of C deeper than (S p).0
               ==>  S.take p ++ C ++ S.drop (p+1)  in W u

(the head condition `head C = S p` of `(SUBST1)` is dropped; `C in W (lev S p)`
already forces `lev (C 0) <= lev (S p)` by `lev_root_le_of_mem_W`).

If `(SUBST1g)` holds it also absorbs `(CAT)`'s consumers: the shifted-copy tower
`(TOW)` is `(SUBST1g)` over the constant diagonal `[(k*e, b, c)]_{k<n}` (which is
in `W (2b+c)` because every column is a permanent orphan), with block `k` the
`k*e`-shift of `Q`.

`inW` decides the UNGUARDED `W` through `Wchar` (`|S|>=2 <-> all S[n] in W a`),
so `None` = undecided within the search bounds; undecided instances are never
counted as passes.
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXDEPTH = 10
MAXLEN = 40
AMAX = 12


def lev(c):
    return 2 * c[1] + c[2]


def inW(S, a, d, memo):
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
    if d <= 0 or len(S) > MAXLEN:
        return None
    memo[key] = None
    out = True
    for n in NS:
        r = inW(trio.expand(list(S), n), a, d - 1, memo)
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


def main():
    memo = {}
    tot = Counter()
    ex = []
    COLS = [(x, b, c) for x in range(3) for b in range(3) for c in range(2)]
    HEADS = [(b, c) for b in range(3) for c in range(2)]
    TAILS = [[], [(1, 0, 0)], [(1, 1, 0)], [(1, 0, 1)], [(1, 1, 1)],
             [(1, 1, 0), (2, 2, 0)], [(1, 2, 0)], [(1, 2, 1)],
             [(1, 1, 1), (2, 2, 1)], [(2, 1, 0)], [(1, 1, 0), (2, 1, 1)]]
    hosts = []
    for L in (1, 2, 3):
        for S in itertools.product(COLS, repeat=L):
            S = list(S)
            if S[0][0] != 0:
                continue                          # based hosts only
            u = minstage(S, memo)
            if u is None:
                continue
            hosts.append((S, u))
    print('decided hosts:', len(hosts))

    for S, u in hosts:
        for p in range(len(S)):
            x = S[p][0]
            for (b, c) in HEADS:
                for T in TAILS:
                    C = [(x, b, c)] + [(x + t[0], t[1], t[2]) for t in T]
                    sc = minstage(C, memo)
                    if sc is None or sc > lev(S[p]):
                        continue                  # hypothesis: C in W (lev S p)
                    R = S[:p] + C + S[p + 1:]
                    if len(R) > MAXLEN:
                        continue
                    same = (b, c) == (S[p][1], S[p][2])
                    tot['inst'] += 1
                    if not same:
                        tot['inst/head-differs'] += 1
                    r = inW(R, u, MAXDEPTH, memo)
                    if r is True:
                        tot['ok'] += 1
                    elif r is None:
                        tot['undecided'] += 1
                    else:
                        tot['FAIL'] += 1
                        if not same:
                            tot['FAIL/head-differs'] += 1
                        if len(ex) < 8:
                            ex.append((S, u, p, C, sc, R))
    for k in sorted(tot):
        print(f'  {k:20s} {tot[k]:8d}')
    for S, u, p, C, sc, R in ex:
        print(f'  FAIL S={S} u={u} p={p} C={C} (stage {sc} <= lev {lev(S[p])})')
        print(f'       R={R}  minstage={minstage(R, memo)}')


if __name__ == '__main__':
    main()
