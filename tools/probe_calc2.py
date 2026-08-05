"""The LOW-ORPHAN lift calculus, corrected.

probe_lowcalc showed (NL) is exactly right (0/139244) but (HI) needs more than
"A's root sits above v": the composite row-1 parent of the graft site may be an
INTERMEDIATE low column of R, not the ambient root (counterexample
E=[(0,1,0),(1,0,0),(2,1,0)], A=[(0,2,0),...]: the site's row-1 parent is
column 1, itself an orphan, so the site is outside the ambient cone).

The right hypothesis is the composite cone membership of the graft site itself:

  (CALC) E = (0,v,z) :: R (R argOK), A based, every NON-ROOT row-1 orphan of A
         has row1 <= v.  Then

           Lift1 (graft E A) d
             = graft (Lift1 E d) (if le1 (graft E A) 0 (|E|-1) then Lift1 A d
                                                               else A)

Both branches are then supposed to be exact.  The machine can always decide the
guard: at a beta site the tower step gives `nextrel2 Nb 0 last`, which CONTAINS
`le1 Nb 0 last`, and the graft does not change (row0,row1) at the site; at an
alpha site the grafted root carries row1 = ambient v, so the guard is false.

(GUARD-FREE control) also measured: how often the naive "root row1 > v" guard
disagrees with the true guard.
"""
import sys
import random
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


def orphans(A):
    return [j for j in range(len(A)) if trio.parent(A, 1, j) is None]


RCOLS = [(a, b, c) for a in range(1, 3) for b in range(3) for c in range(2)]
ACOLS = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]

rnd = random.Random(20260805)

tot = Counter()
bad = Counter()
ex = {}
naive_disagree = 0

N = 300000
for _ in range(N):
    v = rnd.randrange(3)
    z = rnd.randrange(2)
    R = [rnd.choice(RCOLS) for _ in range(rnd.randrange(1, 3))]
    E = [(0, v, z)] + R
    w = rnd.randrange(4)
    zeta = rnd.randrange(2)
    A = [(0, w, zeta)] + [rnd.choice(ACOLS) for _ in range(rnd.randrange(0, 3))]
    d = rnd.randrange(1, 3)

    O = orphans(A)
    others_low = all(A[j][1] <= v for j in O if j != 0)
    G = graft(E, A)
    site = len(E) - 1
    guard = trio.is_ancestor(G, 1, 0, site)
    if guard != (A[0][1] > v):
        naive_disagree += 1
    if not others_low:
        cls = 'X'
    else:
        cls = 'HI' if guard else 'NL'

    lhs = Lift1(G, d)
    tot[cls] += 1
    if cls == 'X':
        rhs = graft(Lift1(E, d), Lift1(A, d) if guard else A)
        if lhs != rhs:
            bad[cls] += 1
            if cls not in ex:
                ex[cls] = (v, z, R, A, d, lhs, rhs)
    else:
        rhs = graft(Lift1(E, d), Lift1(A, d) if guard else A)
        if lhs != rhs:
            bad[cls] += 1
            if cls not in ex:
                ex[cls] = (v, z, R, A, d, lhs, rhs)

print(f"samples: {N}   (naive-guard disagreements: {naive_disagree})")
for k in ('NL', 'HI', 'X'):
    print(f"  {k:3s}: {tot[k]:8d} cases, {bad[k]:8d} violations")
for k, e in ex.items():
    print(f"  {k}-ex v={e[0]} z={e[1]} R={e[2]} A={e[3]} d={e[4]}")
    print(f"    lhs={e[5]}")
    print(f"    rhs={e[6]}")
