"""The GENERAL graft cone transfer (no single-tree / HighPar hypothesis).

Claim (MASK).  Let E be a plant (root (0,v,z) strictly shallowest, |E| >= 2),
A based (forests allowed), s = |E|-1, G = graft E A.  Then for every j < |A|

    le1 G 0 (s + j)  <->  le1 E 0 s  and  coneV A v j

  where  coneV A v j  :=  every row-0 ancestor y of j inside A (j included)
                          carries entry A 1 y > v.

Consequently

    Lift1 (graft E A) d
      = graft (Lift1 E d) (if le1 E 0 s then mlift A v d else A)

  where mlift lifts row 1 by d exactly on coneV A v.

This subsumes probe_calc2's (NL)/(HI): under HighPar, coneV A v is the root
cone of A when v < A's root row 1, and empty otherwise.
"""
import sys
import random

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio


def anc0(X, j):
    """row-0 ancestors of j (j included)."""
    out = []
    p = j
    while p is not None:
        out.append(p)
        p = trio.parent(X, 0, p)
    return out


def cone(X):
    return {i for i in range(len(X)) if trio.is_ancestor(X, 1, 0, i)}


def coneV(A, v):
    return {j for j in range(len(A)) if all(A[y][1] > v for y in anc0(A, j))}


def Lift1(X, t):
    C = cone(X)
    return [(c[0], c[1] + (t if i in C else 0), c[2]) for i, c in enumerate(X)]


def mlift(A, v, t):
    C = coneV(A, v)
    return [(c[0], c[1] + (t if i in C else 0), c[2]) for i, c in enumerate(A)]


def graft(M, y):
    w = M[-1][0]
    return M[:-1] + [(p[0] + w, p[1], p[2]) for p in y]


RCOLS = [(a, b, c) for a in range(1, 3) for b in range(3) for c in range(2)]
ACOLS = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]

rnd = random.Random(776655)

tot = 0
bad_cone = 0
bad_calc = 0
mask_ne_cone = 0
ex_cone = None
ex_calc = None
guard_true = 0

N = 200000
for _ in range(N):
    v = rnd.randrange(3)
    z = rnd.randrange(2)
    R = [rnd.choice(RCOLS) for _ in range(rnd.randrange(1, 3))]
    E = [(0, v, z)] + R
    s = len(E) - 1
    w = rnd.randrange(4)
    zeta = rnd.randrange(2)
    A = [(0, w, zeta)] + [rnd.choice(ACOLS) for _ in range(rnd.randrange(0, 3))]
    d = rnd.randrange(1, 3)

    G = graft(E, A)
    # SiteHigh: every row-0 ancestor of the graft point STRICTLY BEFORE it
    # (the point itself excluded -- in G it carries A's root row 1, not E's)
    # sits above the root in row 1.
    guard = all(E[y][1] > v for y in anc0(E, s) if y != 0 and y != s)
    if guard:
        guard_true += 1
    CV = coneV(A, v)
    CG = cone(G)
    tot += 1
    if CV != cone(A):
        mask_ne_cone += 1
    ok = all(((s + j) in CG) == (guard and (j in CV)) for j in range(len(A)))
    if not ok:
        bad_cone += 1
        if ex_cone is None:
            ex_cone = (v, z, R, A, guard, sorted(CV), sorted(CG))
    lhs = Lift1(G, d)
    rhs = graft(Lift1(E, d), mlift(A, v, d) if guard else A)
    if lhs != rhs:
        bad_calc += 1
        if ex_calc is None:
            ex_calc = (v, z, R, A, d, lhs, rhs)

print(f"samples: {tot}  (SiteHigh: {guard_true};"
      f" mask != A's own cone: {mask_ne_cone})")
print(f"  (MASK cone transfer): {bad_cone} violations")
print(f"  (MASK lift calculus): {bad_calc} violations")
if ex_cone:
    print(f"  cone-ex v={ex_cone[0]} z={ex_cone[1]} R={ex_cone[2]} A={ex_cone[3]}")
    print(f"    guard={ex_cone[4]} coneV={ex_cone[5]} coneG={ex_cone[6]}")
if ex_calc:
    print(f"  calc-ex v={ex_calc[0]} z={ex_calc[1]} R={ex_calc[2]} A={ex_calc[3]} d={ex_calc[4]}")
    print(f"    lhs={ex_calc[5]}")
    print(f"    rhs={ex_calc[6]}")
