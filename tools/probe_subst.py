"""(SUBST) — the substitution closure that `TowerExp2Root` needs for `|R| >= 2`.

GRAFTALL-PLAN 4.15: `M[n]` is the (already proved) diagonal
`[(k*d0, v + k*d1, z)]_{k<n}` with a lifted `R.dropLast` inserted UNDER each
column, and `(WL)` puts each inserted block in `W (lev c_k)` — exactly the level
of the diagonal column it hangs under.  So what is missing is

    (SUBST)  Q in W u,  and for each column j of Q a block B_j with
             head B_j = Q[j] and every other column of B_j strictly deeper
             than (Q[j]).0,  and  B_j in W (lev (Q[j]))
             ==>  concat_j B_j  in W u

This probe measures it: enumerate small `Q` with a known `minstage`, attach
small deeper blocks whose own `minstage` is at most the host column's level, and
check the concatenation.

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
    # hosts: short blocks whose stage we can decide
    COLS = [(x, b, c) for x in range(3) for b in range(3) for c in range(2)]
    TAILS = [[], [(1, 0, 0)], [(1, 1, 0)], [(1, 0, 1)], [(1, 1, 1)],
             [(1, 1, 0), (2, 2, 0)], [(1, 2, 0)]]
    hosts = []
    for L in (1, 2, 3):
        for Q in itertools.product(COLS, repeat=L):
            Q = list(Q)
            if Q[0][0] != 0:
                continue                      # based hosts only
            u = minstage(Q, memo)
            if u is None:
                continue
            hosts.append((Q, u))
    print('decided hosts:', len(hosts))

    for Q, u in hosts:
        # attach one tail under column j (all other columns keep themselves)
        for j in range(len(Q)):
            for T in TAILS:
                B = [Q[j]] + [(Q[j][0] + t[0], t[1], t[2]) for t in T]
                sb = minstage(B, memo)
                if sb is None or sb > lev(Q[j]):
                    continue                  # the datum (WL) supplies needs B in W (lev)
                R = []
                for i, c in enumerate(Q):
                    R += B if i == j else [c]
                if len(R) > MAXLEN:
                    continue
                tot['inst'] += 1
                r = inW(R, u, MAXDEPTH, memo)
                if r is True:
                    tot['ok'] += 1
                elif r is None:
                    tot['undecided'] += 1
                else:
                    tot['FAIL'] += 1
                    if len(ex) < 8:
                        ex.append((Q, u, j, T, B, sb, R))
    for k in sorted(tot):
        print(f'  {k:12s} {tot[k]:8d}')
    for Q, u, j, T, B, sb, R in ex:
        print(f'  FAIL Q={Q} u={u} j={j} B={B} (stage {sb} <= lev {lev(Q[j])})')
        print(f'       R={R}')


if __name__ == '__main__':
    main()
