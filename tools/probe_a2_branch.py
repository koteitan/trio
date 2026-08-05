"""(A2) and (G2) split by the expansion branch `i1 = srow M j1`.

The Lean proof of (A2) must split:
  i1 >= 1 : d0 > 0, the copy roots ascend; `gexp_chain_inversion` applies, and
            the side condition is `amin M j0 <= amin M (j0+Lb)` (hrow1).
  i1 = 0  : d0 = d1 = 0, the copies are IDENTICAL; every copy root has the same
            row 0 as j0, so its row-0 parent is j0's own parent.

Measured here:
  - (A2) per branch
  - hrow1 per branch (expected: true for i1>=1, false in general for i1=0)
  - (G2) per branch
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


def amin(X, j):
    return min(X[y][1] for y in anc0(X, j))


def mk_phi(pairs):
    def phi(m):
        return m + sum(s for (v, s) in pairs if m > v)
    return phi


def glift(A, phi):
    return [(c[0], c[1] + phi(amin(A, i)) - amin(A, i), c[2])
            for i, c in enumerate(A)]


COLS = [(a, b, c) for a in range(4) for b in range(5) for c in range(2)]
rnd = random.Random(97531)

tot = Counter()
badA2 = Counter()
badRow1 = Counter()
badG2 = Counter()
ex = {}

N = 80000
for _ in range(N):
    S = [(0, rnd.randrange(4), rnd.randrange(2))] + \
        [rnd.choice(COLS) for _ in range(rnd.randrange(1, 5))]
    n = rnd.randrange(1, 4)
    x = len(S) - 1
    if x == 0 or all(w == 0 for w in S[x]):
        continue
    t = max(y for y in range(3) if S[x][y] > 0)
    r = trio.parent(S, t, x)
    if r is None:
        continue
    Lb = x - r
    E = trio.expand(S, n)
    if len(E) != r + n * Lb:
        continue
    key = f"i1={t}"
    tot[key] += 1

    # (A2)
    ok = True
    for a in range(n):
        for q in range(Lb):
            if amin(E, r + a * Lb + q) != amin(S, r + q):
                ok = False
    if not ok:
        badA2[key] += 1
        if key + "/A2" not in ex:
            ex[key + "/A2"] = (S, n)

    # hrow1
    if not (amin(S, r) <= amin(S, r + Lb)):
        badRow1[key] += 1
        if key + "/row1" not in ex:
            ex[key + "/row1"] = (S, n, r, Lb, amin(S, r), amin(S, r + Lb))

    # (G2)
    pairs = [(rnd.randrange(6), rnd.randrange(1, 4))
             for _ in range(rnd.randrange(1, 4))]
    phi = mk_phi(pairs)
    lhs = glift(E, phi)
    rhs = trio.expand(glift(S, phi), n)
    if lhs != rhs:
        badG2[key] += 1
        if key + "/G2" not in ex:
            ex[key + "/G2"] = (S, n, pairs, lhs, rhs)

print(f"{'branch':10s} {'cases':>8s} {'A2 viol':>9s} {'hrow1 viol':>11s} {'G2 viol':>9s}")
for k in sorted(tot):
    print(f"{k:10s} {tot[k]:8d} {badA2[k]:9d} {badRow1[k]:11d} {badG2[k]:9d}")
for k, e in ex.items():
    print(f"  ex {k}: {e}")
