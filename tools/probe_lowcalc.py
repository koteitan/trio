"""The LOW-ORPHAN lift calculus (generalises the aligned calculus).

Let E = (0,v,z) :: R be a PLANT (R argOK: every column of R has row 0 >= 1),
and let A be a based block.  Write orph(A) = the row-1 orphans of A (columns
with no row-1 parent inside A; the root is always one).

  (NL)  if every orphan of A has row1 <= v:
            Lift1 (graft E A) d = graft (Lift1 E d) A
        -- the ambient lift passes A by entirely.

  (HI)  if A's root has row1 > v and every NON-root orphan has row1 <= v:
            Lift1 (graft E A) d = graft (Lift1 E d) (Lift1 A d)
        -- the ambient cone meets A exactly in A's own root cone.

  (X)   otherwise (a non-root orphan above v, i.e. a genuine forest branch):
        expected to satisfy neither.

This is the exact abstraction behind probe_alignedsite/probe_alignedforest:
"X aligned single tree" implies LowOrph at v by the plant fact (F1), and
"A = Lift1 X d0" lands in (NL) for d0 = 0 and in (HI) for d0 >= 1.
"""
import sys
import random
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


def orphans(A):
    return [j for j in range(len(A)) if trio.parent(A, 1, j) is None]


RCOLS = [(a, b, c) for a in range(1, 3) for b in range(3) for c in range(2)]
ACOLS = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]

rnd = random.Random(20260805)

tot = Counter()
bad = Counter()
ex = {}

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
    hi_root = A[0][1] > v
    others_low = all(A[j][1] <= v for j in O if j != 0)
    if others_low and not hi_root:
        cls = 'NL'
        okey = graft(Lift1(E, d), A)
    elif others_low and hi_root:
        cls = 'HI'
        okey = graft(Lift1(E, d), Lift1(A, d))
    else:
        cls = 'X'
        okey = None

    lhs = Lift1(graft(E, A), d)
    tot[cls] += 1
    if cls == 'X':
        # control: does either formula happen to hold?
        if lhs == graft(Lift1(E, d), A) or lhs == graft(Lift1(E, d), Lift1(A, d)):
            bad[cls] += 1          # counts *agreements* here, not violations
    else:
        if lhs != okey:
            bad[cls] += 1
            if cls not in ex:
                ex[cls] = (v, z, R, A, d, lhs, okey)

print(f"samples: {N}")
for k in ('NL', 'HI', 'X'):
    label = 'agreements' if k == 'X' else 'violations'
    print(f"  {k:3s}: {tot[k]:8d} cases, {bad[k]:8d} {label}")
for k, e in ex.items():
    print(f"  {k}-ex v={e[0]} z={e[1]} R={e[2]} A={e[3]} d={e[4]}")
    print(f"    lhs={e[5]}")
    print(f"    rhs={e[6]}")
