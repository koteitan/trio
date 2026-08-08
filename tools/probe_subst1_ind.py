"""Induction design for `(SUBST1g)`: which cases does the HOST's datum close?

`(SUBST1g)`'s natural proof is `A2'` on the host `S ∈ W u`, with

    R := S.take p ++ C ++ S.drop (p+1)        (the substituted object)

The clause-2 step needs `R⟦n⟧` expressed through the induction hypothesis.  Two
identities are conjectured:

  (MIRROR)  when the insertion sits strictly LEFT of `S`'s bad root,
            `R⟦n⟧ = subst (S⟦n⟧) p C`      -- IH on the host closes it

  (INNER)   when `p = |S|-1` (nothing after the block) and `R`'s bad root lies
            inside `C`,
            `R⟦n⟧ = S.take p ++ C⟦n⟧`      -- a NESTED induction on `C`'s datum

Everything else is the residue: the context revives a column that is an orphan
inside its own block.  This probe measures the three shares and checks both
identities exactly.

The point of the measurement is NOT the truth of `(SUBST1g)` (already measured,
`probe_subst1g.py`, 210201 instances 0 violations) but the SHAPE of the
induction: how much of it is mechanical, and what exactly is left.
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2, 3)
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
    for n in (1, 2):
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


def badroot(S):
    """The index `oper` copies from, or None when `oper` is `Pred`."""
    if not S:
        return None
    X = len(S)
    x = X - 1
    Y = len(S[0])
    if all(val == 0 for val in S[x]):
        return None
    t = max(y for y in range(Y) if S[x][y] > 0)
    return trio.parent(S, t, x)


def subst(X, p, C):
    return list(X[:p]) + list(C) + list(X[p + 1:])


def main():
    memo = {}
    tot = Counter()
    ex_mirror = []
    ex_inner = []
    ex_res = []
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
                continue
            u = minstage(S, memo)
            if u is None:
                continue
            hosts.append((S, u))
    print('decided hosts:', len(hosts))

    for S, u in hosts:
        j0S = badroot(S)
        for p in range(len(S)):
            x = S[p][0]
            for (b, c) in HEADS:
                for T in TAILS:
                    C = [(x, b, c)] + [(x + t[0], t[1], t[2]) for t in T]
                    sc = minstage(C, memo)
                    if sc is None or sc > lev(S[p]):
                        continue
                    R = subst(S, p, C)
                    if len(R) > MAXLEN:
                        continue
                    tot['inst'] += 1
                    j0R = badroot(R)
                    mirror = (p < len(S) - 1
                              and all(len(trio.expand(list(S), n)) > p
                                      and trio.expand(list(R), n)
                                      == subst(trio.expand(list(S), n), p, C)
                                      for n in NS))
                    inner = (p == len(S) - 1
                             and all(trio.expand(list(R), n)
                                     == list(S[:p]) + trio.expand(list(C), n)
                                     for n in NS))
                    if mirror:
                        tot['(MIRROR) identity ok'] += 1
                        if j0S is None:
                            tot['  mirror: badroot S = None'] += 1
                        elif p < j0S:
                            tot['  mirror: p < badroot S'] += 1
                        else:
                            tot['  mirror: OTHER'] += 1
                    elif inner:
                        tot['(INNER) identity ok'] += 1
                        if j0R is None:
                            tot['  inner: badroot R = None'] += 1
                        else:
                            tot['  inner: badroot R >= p'] += 1
                    else:
                        tot['RESIDUE'] += 1
                        if p == len(S) - 1:
                            tot['  residue: D empty (context revives)'] += 1
                        elif j0S is None:
                            tot['  residue: S orphan-tailed'] += 1
                        elif p >= j0S:
                            tot['  residue: p >= badroot S'] += 1
                        else:
                            tot['  residue: OTHER'] += 1
                        if len(ex_res) < 8:
                            ex_res.append((S, u, p, C, R, j0S, j0R))
    for k in sorted(tot):
        print(f'  {k:36s} {tot[k]:8d}')
    for tag, lst in (('MIRROR FAIL', ex_mirror), ('INNER FAIL', ex_inner)):
        for S, p, C, R in lst:
            print(f'  {tag} S={S} p={p} C={C} R={R}')
            print(f'      R[1]={trio.expand(list(R),1)}  S[1]={trio.expand(list(S),1)}')
    print('  residue samples:')
    for S, u, p, C, R, j0S, j0R in ex_res:
        print(f'    S={S} u={u} p={p} C={C} badroot S={j0S} badroot R={j0R}')


if __name__ == '__main__':
    main()
