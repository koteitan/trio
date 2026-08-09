"""(GC) — does `Aop` clause-3 closure come free from membership plus `domT`?

    (GC)  S in W u,  domT S m   ==>   forall z in W m, based z -> graft S z in W u

`Aop` clause 3 is one of three ways into `W u`; a given `S` may have entered by
clause 2 instead, in which case the graft closure is NOT on hand.  (GC) asks
whether it holds anyway.

It matters now because `W_shiftl0` (new) re-bases a block to depth 0, so the
residue's `lev C 0 < lev (S last)` half is EXACTLY a clause-3 graft:
`graft S (shiftl0 x C) = S.dropLast ++ C`.  If (GC) is true, that half is free.

An old memory note says (GC) was "ruled out", but the formulation there was
inside the `Wstar`/`GX` machinery, not this `W u` one, and at `|S| = 1` the
`W u` version is immediate (`graft [c] z = shift z` and `W_shift`).  So it is
re-measured here.

`inW` decides the UNGUARDED `W` through `Wchar`, so `None` = undecided; those
are never counted as passes.
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


def srow(S, j):
    if S[j][2] > 0:
        return 2
    if S[j][1] > 0:
        return 1
    return 0


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


def graft(S, z):
    """Replace S's last column by z, shifted to that column's depth."""
    x = S[-1][0]
    return list(S[:-1]) + [(q[0] + x, q[1], q[2]) for q in z]


def main():
    memo = {}
    tot = Counter()
    ex = []
    COLS = [(x, b, c) for x in range(3) for b in range(3) for c in range(2)]
    ZS = []
    for L in (0, 1, 2, 3):
        for z in itertools.product(COLS, repeat=L):
            z = list(z)
            if z and z[0][0] != 0:
                continue                       # based only
            ZS.append(z)
    for L in (1, 2, 3):
        for S in itertools.product(COLS, repeat=L):
            S = list(S)
            if S[0][0] != 0:
                continue
            x = len(S) - 1
            if lev(S[x]) == 0:
                continue                       # domT needs lev = m+1 > 0
            if trio.parent(S, srow(S, x), x) is not None:
                continue                       # domT needs a parentless terminal
            m = lev(S[x]) - 1
            stages = [a for a in range(AMAX + 1) if inW(S, a, MAXDEPTH, memo) is True]
            if not stages:
                continue
            tot['domT hosts'] += 1
            for z in ZS:
                if inW(z, m, MAXDEPTH, memo) is not True:
                    continue
                G = graft(S, z)
                if len(G) > MAXLEN:
                    continue
                for a in stages:
                    r = inW(G, a, MAXDEPTH, memo)
                    if r is None:
                        tot['undecided'] += 1
                        continue
                    tot['decided'] += 1
                    if r is False:
                        tot['VIOLATION'] += 1
                        if len(ex) < 8:
                            ex.append((S, a, m, z, G))
    for k in sorted(tot):
        print(f'  {k:14s} {tot[k]:9d}')
    for S, a, m, z, G in ex:
        print(f'  VIOL S={S} a={a} m={m} z={z}')
        print(f'       graft={G}')


if __name__ == '__main__':
    main()
