"""Does the ambient mask lift commute with the expansion?

CoreMaskLift ("GX is closed under `mlift`") would follow from the machine's own
induction as soon as the mask lift transports the Aop clauses, i.e. as soon as

    (O)  mlift (D[n]) v t  =  (mlift D v t)[n]

(possibly under conditions on the site).  `Lift1` satisfies the analogous law
only conditionally (oper_Lift1_root / oper_Lift1_tower / liftInner), so measure
(O) split by the site type of D's trailing column:

  nil      : |D| <= 1 or a zero trailing column (Pred branch)
  noparent : the trailing column has no parent (Pred branch)
  root     : its parent is the root 0
  inner    : its parent is some j0 >= 1

and also by whether the trailing column / the bad root sit in the mask.
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


def srow(c):
    return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)


def site(D):
    if len(D) <= 1:
        return 'nil'
    j = len(D) - 1
    if D[j] == (0, 0, 0):
        return 'nil'
    p = trio.parent(D, srow(D[j]), j)
    if p is None:
        return 'noparent'
    return 'root' if p == 0 else 'inner'


COLS = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]

rnd = random.Random(31337)
tot = Counter()
bad = Counter()
ex = {}

N = 60000
for _ in range(N):
    D = [(0, rnd.randrange(3), rnd.randrange(2))] + \
        [rnd.choice(COLS) for _ in range(rnd.randrange(1, 4))]
    v = rnd.randrange(3)
    t = rnd.randrange(1, 3)
    n = rnd.randrange(1, 3)
    st = site(D)
    key = st + ('/inmask' if (len(D) - 1) in coneV(D, v) else '/outmask')
    lhs = mlift(trio.expand(D, n), v, t)
    rhs = trio.expand(mlift(D, v, t), n)
    tot[key] += 1
    if lhs != rhs:
        bad[key] += 1
        if key not in ex:
            ex[key] = (D, v, t, n, lhs, rhs)

print(f"{'site/mask':22s} {'cases':>8s} {'viol':>8s}")
for k in sorted(tot):
    print(f"{k:22s} {tot[k]:8d} {bad[k]:8d}")
for k, e in ex.items():
    print(f"  ex {k}: D={e[0]} v={e[1]} t={e[2]} n={e[3]}")
    print(f"    lhs={e[4]}")
    print(f"    rhs={e[5]}")
