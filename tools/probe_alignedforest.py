"""The aligned lift calculus.

Everything the machine lifts is a block PLANTED AT THE AMBIENT ROOT, possibly
already lifted.  For such data the composite lift has a closed calculus:

  (C)  Lift1 (graft E (Lift1 X d0)) d
         = graft (Lift1 E d) (Lift1 X (d0 (+) d)),     d0 (+) d := 0 if d0 = 0
                                                                  d0 + d else

where E = (0,v,z) :: R (a planted block) and X is ALIGNED with it, i.e. X = []
or X's root is (0,v,z) (same row 1 and row 2 as E's root).

Rationale: an aligned X has root row-1 = v, so it is outside the cone of the
composite root and the lift passes it by (d0 = 0 case); once X carries a lift
d0 >= 1 its root sits at v+d0 > v, and then the mask on it is exactly its own
cone, so the lift parameters add (the d0 >= 1 case, probe_tower2lift's (T)).

Checks:
  (C0) d0 = 0 branch
  (C1) d0 >= 1 branch
  (C2) the same with a NON-aligned X (control; expected to fail)
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio


def cone(X):
    return {i for i in range(len(X)) if trio.is_ancestor(X, 1, 0, i)}


def Lift1(X, t):
    C = cone(X)
    return [(c[0], c[1] + (t if i in C else 0), c[2]) for i, c in enumerate(X)]


def graft(M, y):
    w = M[-1][0]
    return M[:-1] + [(p[0] + w, p[1], p[2]) for p in y]


def plus(d0, d):
    return 0 if d0 == 0 else d0 + d


def lev(c):
    return 2 * c[1] + c[2]


def srow(c):
    return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)


def tower_site(E):
    """the root revives E's trailing orphan (tower1 / tower2)."""
    R = E[1:]
    L = len(R)
    if L == 0 or lev(R[-1]) == 0:
        return None
    if trio.parent(R, srow(R[-1]), L - 1) is not None:
        return None
    p = trio.parent(E, srow(R[-1]), L)
    if p != 0:
        return None
    return 'tower' + str(srow(R[-1]))


def ctxs(maxlen, r0, r1):
    cols = [(a, b, c) for a in range(1, r0) for b in range(r1) for c in range(2)]
    for k in range(1, maxlen):
        for R in itertools.product(cols, repeat=k):
            yield list(R)


def tails(maxlen, r0, r1):
    cols = [(a, b, c) for a in range(0, r0) for b in range(r1) for c in range(2)]
    yield []
    for k in range(0, maxlen):
        for T in itertools.product(cols, repeat=k):
            yield list(T)


RS = list(ctxs(3, 3, 3))
TS = list(tails(3, 3, 3))

tot = Counter(); bad = Counter()
ex = {}

for R in RS:
    for v in range(3):
        for z in range(2):
            E = [(0, v, z)] + R
            site = tower_site(E)
            if site is None:
                continue
            for T in TS:
                for aligned in (True, False):
                    if aligned:
                        X = [] if not T else [(0, v, z)] + T
                    else:
                        # a deliberately misaligned root
                        X = [(0, v + 1, z)] + T
                    if not X:
                        continue
                    for d0 in (0, 1, 2):
                        for d in (1, 2):
                            key = site + '/' + ('aligned' if aligned else 'mis') + \
                                  ('/d0=0' if d0 == 0 else '/d0>0')
                            tot[key] += 1
                            lhs = Lift1(graft(E, Lift1(X, d0)), d)
                            rhs = graft(Lift1(E, d), Lift1(X, plus(d0, d)))
                            if lhs != rhs:
                                bad[key] += 1
                                if key not in ex:
                                    ex[key] = (v, z, R, X, d0, d, lhs, rhs)

print(f"{'class':20s} {'cases':>10s} {'viol':>10s}")
for k in sorted(tot):
    print(f"{k:20s} {tot[k]:10d} {bad[k]:10d}")
for k, e in ex.items():
    print(f"  {k}-ex v={e[0]} z={e[1]} R={e[2]} X={e[3]} d0={e[4]} d={e[5]}")
    print(f"    lhs={e[6]}")
    print(f"    rhs={e[7]}")
