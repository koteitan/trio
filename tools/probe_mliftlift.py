"""Does the ambient mask lift ABSORB into the root lift?

The alpha residue currently splits as CorePlantCtxLift + CoreMaskLift, and the
mask-lift core ("GX is closed under `mlift`") is the hard half.  But in the
tower induction the datum is never an arbitrary GX element -- it is always
`Lift1 (Nb[i]) d1`, a ROOT LIFT of the previous tower level.  If

    (ML)  mlift (Lift1 X d) v e = Lift1 X (d + e)        (X = (0,v,z)::R, d > 0)

then the mask lift of such a datum is again a root lift of the SAME tower
level, so strengthening the tower induction to

    forall j s, Lift1 (Nb[j]) (d1 + s) in GX

closes it with no mask-lift core at all.

Why it should hold: `Lift1 X d` lifts exactly the root cone by `d`; every
column in that cone then has ancestor-minimum `v + d > v`, and every column
outside it has some ancestor at row 1 <= v, so the `v`-mask of `Lift1 X d` IS
the root cone again.  `d > 0` is needed: at `d = 0` the root itself sits at
`v`, not above it, so the mask misses it.

Also measured: the two ingredients
    (C)  mlift ((0,w,z)::S) v s = (0,w+s,z) :: mlift S v s      (v < w)
    (M2) mlift (mlift R v d) v e = mlift R v (d + e)
"""
import sys
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio


def anc0(X, j):
    out = []
    p = j
    while p is not None:
        out.append(p)
        p = trio.parent(X, 0, p)
    return out


def coneV(A, v):
    return {j for j in range(len(A)) if all(A[y][1] > v for y in anc0(A, j))}


def mlift(A, v, t):
    C = coneV(A, v)
    return [(c[0], c[1] + (t if i in C else 0), c[2]) for i, c in enumerate(A)]


def cone(X):
    return {i for i in range(len(X)) if trio.is_ancestor(X, 1, 0, i)}


def Lift1(X, t):
    C = cone(X)
    return [(c[0], c[1] + (t if i in C else 0), c[2]) for i, c in enumerate(X)]


RCOLS = [(a, b, c) for a in range(1, 4) for b in range(5) for c in range(2)]

rnd = random.Random(606060)
tot = Counter()
bad = Counter()
ex = {}

N = 200000
for _ in range(N):
    v = rnd.randrange(4)
    z = rnd.randrange(2)
    R = [rnd.choice(RCOLS) for _ in range(rnd.randrange(0, 4))]
    X = [(0, v, z)] + R
    d = rnd.randrange(0, 3)
    e = rnd.randrange(0, 3)
    key = 'd>0' if d > 0 else 'd=0'
    tot[key] += 1
    lhs = mlift(Lift1(X, d), v, e)
    rhs = Lift1(X, d + e)
    if lhs != rhs:
        bad[key] += 1
        if key not in ex:
            ex[key] = (X, d, e, lhs, rhs)

    # ingredient (C)
    w = rnd.randrange(5)
    S = [rnd.choice(RCOLS) for _ in range(rnd.randrange(0, 4))]
    s = rnd.randrange(1, 3)
    if v < w:
        tot['(C)'] += 1
        l2 = mlift([(0, w, z)] + S, v, s)
        r2 = [(0, w + s, z)] + mlift(S, v, s)
        if l2 != r2:
            bad['(C)'] += 1
            if '(C)' not in ex:
                ex['(C)'] = (w, S, v, s, l2, r2)

    # ingredient (M2)
    tot['(M2)'] += 1
    l3 = mlift(mlift(R, v, d), v, e)
    r3 = mlift(R, v, d + e)
    if l3 != r3:
        bad['(M2)'] += 1
        if '(M2)' not in ex:
            ex['(M2)'] = (R, v, d, e, l3, r3)

print(f"{'case':8s} {'samples':>9s} {'viol':>8s}")
for k in sorted(tot):
    print(f"{k:8s} {tot[k]:9d} {bad[k]:8d}")
for k, e in ex.items():
    print(f"  ex {k}: {e}")
