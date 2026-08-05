"""Does the ambient mask lift distribute over grafts with a CONSTANT threshold?

`Lift1` resets its threshold at every root (it always lifts the root's own
cone), which is why "lift inside a graft" is not expressible -- the campaign's
(e)-wall.  The mask lift `mlift A v d` (lift every column whose row-0 ancestor
chain stays strictly above `v`) has a fixed threshold, so it may distribute:

  (D)  mlift (graft M y) v d
         = graft (mlift M v d) (if SiteV M v then mlift y v d else y)

  SiteV M v := every row-0 ancestor of M's last column, the column itself
               EXCLUDED, sits strictly above `v` in row 1.

If (D) holds, the machine's graft obligations are stable under the mask lift
with the SAME `v`, which is exactly what `Lift1` fails to be.
"""
import sys
import random

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


def graft(M, y):
    w = M[-1][0]
    return M[:-1] + [(p[0] + w, p[1], p[2]) for p in y]


def siteV(M, v):
    s = len(M) - 1
    return all(M[y][1] > v for y in anc0(M, s) if y != s)


MCOLS = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]
YCOLS = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]

rnd = random.Random(4242)
tot = 0
bad = 0
ex = None
site_true = 0

N = 200000
for _ in range(N):
    M = [(0, rnd.randrange(3), rnd.randrange(2))] + \
        [rnd.choice(MCOLS) for _ in range(rnd.randrange(1, 3))]
    y = [(0, rnd.randrange(3), rnd.randrange(2))] + \
        [rnd.choice(YCOLS) for _ in range(rnd.randrange(0, 3))]
    v = rnd.randrange(3)
    d = rnd.randrange(1, 3)
    sv = siteV(M, v)
    if sv:
        site_true += 1
    lhs = mlift(graft(M, y), v, d)
    rhs = graft(mlift(M, v, d), mlift(y, v, d) if sv else y)
    tot += 1
    if lhs != rhs:
        bad += 1
        if ex is None:
            ex = (M, y, v, d, sv, lhs, rhs)

print(f"samples: {tot}  (SiteV true: {site_true})")
print(f"  (D) mask lift distributes over graft: {bad} violations")
if ex:
    print(f"  ex M={ex[0]} y={ex[1]} v={ex[2]} d={ex[3]} siteV={ex[4]}")
    print(f"    lhs={ex[5]}")
    print(f"    rhs={ex[6]}")
