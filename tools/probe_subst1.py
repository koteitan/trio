"""(SUBST1) — ONE-COLUMN substitution, the single-block form of `(SUBST)`.

`(SUBST)` substitutes a block under EVERY column of the host at once.  But the
substitutions are independent and they can be done one at a time FROM THE RIGHT,
because replacing the column at position `p` never disturbs positions `< p`:

    Q  ->  Q.take (L-1) ++ B(L-1)  ->  Q.take (L-2) ++ B(L-2) ++ B(L-1)  -> ...

So `(SUBST)` follows from the single-block statement

    (SUBST1)  S in W u,  p < |S|,  C in W (lev S p),
              head C = S p,  every other column of C deeper than (S p).0
              ==>  S.take p ++ C ++ S.drop (p+1)  in W u

which is a far better induction target (one block, no `flatMap`).

This probe measures `(SUBST1)` and, separately, reports whether the host needs
to be a row-0 chain (`(SUBST)` assumes it; `(SUBST1)` might not need it).

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


def is_chain(S):
    return all(S[k][0] < S[k + 1][0] for k in range(len(S) - 1))


def main():
    memo = {}
    tot = Counter()
    ex = []
    exchain = []
    COLS = [(x, b, c) for x in range(3) for b in range(3) for c in range(2)]
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
            for T in TAILS:
                C = [S[p]] + [(S[p][0] + t[0], t[1], t[2]) for t in T]
                sc = minstage(C, memo)
                if sc is None or sc > lev(S[p]):
                    continue                      # (SUBST1) hypothesis: C in W (lev S p)
                R = S[:p] + C + S[p + 1:]
                if len(R) > MAXLEN:
                    continue
                ch = is_chain(S)
                tot['inst'] += 1
                if ch:
                    tot['inst/chain'] += 1
                r = inW(R, u, MAXDEPTH, memo)
                if r is True:
                    tot['ok'] += 1
                elif r is None:
                    tot['undecided'] += 1
                else:
                    tot['FAIL'] += 1
                    if ch:
                        tot['FAIL/chain'] += 1
                        if len(exchain) < 6:
                            exchain.append((S, u, p, C, sc, R))
                    elif len(ex) < 6:
                        ex.append((S, u, p, C, sc, R))
    for k in sorted(tot):
        print(f'  {k:14s} {tot[k]:8d}')
    for tag, lst in (('CHAIN-HOST FAIL', exchain), ('non-chain FAIL', ex)):
        for S, u, p, C, sc, R in lst:
            print(f'  {tag} S={S} u={u} p={p} C={C} (stage {sc} <= lev {lev(S[p])})')
            print(f'       R={R}  minstage={minstage(R, memo)}')


if __name__ == '__main__':
    main()
