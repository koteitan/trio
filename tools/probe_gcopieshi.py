"""Does the guarded (d1 > 0) copies block satisfy a ROOT-LIFT graft recursion?

`gcopies_mem_GX` handles `d1 = 0` because
    shiftl0 c (gcopies R p L d0 0 (n+1))
      = graft (cwin R p L d0 c) (shiftl0 c (gcopies R p L d0 0 n)),
i.e. plain iterated grafting over the window.  For `d1 > 0` (a row-2 blocker)
each copy also ascends in row 1, and the conjecture of GRAFTALL-PLAN 1.9.25 is
that the ascension is exactly a ROOT LIFT of the previous stage:

  (H3)  shiftl0 c (gcopies R p L d0 d1 (n+1))
          = shiftl0 c (seg R p L)
            ++ shiftr01 d0 0 (Lift1 (shiftl0 c (gcopies R p L d0 d1 n)) d1)

        (the right-hand side is `graft (cwin R p L d0 c) (Lift1 … d1)`)

If (H3) holds, `CoreBlockedEltHi` reduces — by the same strengthened induction
used in `coreT2EFam_of_plantctx` (with `mlift_Lift1_cons` absorbing the ambient
mask) — to "the window and ALL ITS ROOT LIFTS are in GX", i.e. to a lifted form
of `CoreWindow`.  That would collapse the 3-core residue to 2.

Also measured, as fallbacks:
  (H1) per-copy:  gcopy … (k+1) = Lift1 (shiftr01 d0 0 (gcopy … k)) d1
  (H2) unshifted: gcopies … (n+1)
                    = gcopy … 0 ++ Lift1 (shiftr01 d0 0 (gcopies … n)) d1
"""
import sys
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio


def seg(R, a, L):
    return [tuple(R[j]) for j in range(a, a + L)]


def gcopy(R, r, L, d0, d1, k):
    return [(R[j][0] + k * d0,
             R[j][1] + (k * d1 if trio.is_ancestor(R, 1, r, j) else 0),
             R[j][2])
            for j in range(r, r + L)]


def gcopies(R, r, L, d0, d1, n):
    out = []
    for k in range(n):
        out += gcopy(R, r, L, d0, d1, k)
    return out


def shiftl0(c, X):
    return [(q[0] - c, q[1], q[2]) for q in X]


def shiftr01(d0, d1, X):
    return [(q[0] + d0, q[1] + d1, q[2]) for q in X]


def Lift1(X, t):
    return [(q[0], q[1] + (t if trio.is_ancestor(X, 1, 0, i) else 0), q[2])
            for i, q in enumerate(X)]


COLS = [(a, b, c) for a in range(1, 5) for b in range(4) for c in range(2)]
rnd = random.Random(20260805)

tot = Counter()
bad = Counter()
ex = {}


def note(key, ok, data):
    tot[key] += 1
    if not ok:
        bad[key] += 1
        ex.setdefault(key, data)


def run_random(N):
    for _ in range(N):
        R = [rnd.choice(COLS) for _ in range(rnd.randrange(2, 7))]
        p = rnd.randrange(0, len(R) - 1)
        L = rnd.randrange(1, len(R) - p)
        c = R[p][0]
        if any(R[j][0] <= c for j in range(p + 1, p + L)):
            continue          # the STRICT window condition (window_of_rtg0)
        d0 = rnd.randrange(0, 3)
        d1 = rnd.randrange(0, 3)
        n = rnd.randrange(0, 4)
        key = ('rand/d1>0' if d1 > 0 else 'rand/d1=0') \
            + ('/d0>0' if d0 > 0 else '/d0=0')
        lhs = shiftl0(c, gcopies(R, p, L, d0, d1, n + 1))
        rhs = (shiftl0(c, seg(R, p, L))
               + shiftr01(d0, 0,
                          Lift1(shiftl0(c, gcopies(R, p, L, d0, d1, n)), d1)))
        note(key + '/H3', lhs == rhs, (R, p, L, d0, d1, n, lhs, rhs))

        k = rnd.randrange(0, 3)
        note(key + '/H1',
             gcopy(R, p, L, d0, d1, k + 1)
             == Lift1(shiftr01(d0, 0, gcopy(R, p, L, d0, d1, k)), d1),
             (R, p, L, d0, d1, k))

        note(key + '/H2',
             gcopies(R, p, L, d0, d1, n + 1)
             == gcopy(R, p, L, d0, d1, 0)
             + Lift1(shiftr01(d0, 0, gcopies(R, p, L, d0, d1, n)), d1),
             (R, p, L, d0, d1, n))


def srow(R, j):
    for y in (2, 1, 0):
        if R[j][y] > 0:
            return y
    return 0


def run_real(N):
    """The actual `CoreBlockedEltHi` shape: R = graft M Y with a row-2 blocker
    at `p`, `L = |R| - 1 - p`, `d0/d1` read off the trailing column."""
    for _ in range(N):
        R = [(0, rnd.randrange(3), rnd.randrange(2))] + \
            [rnd.choice(COLS) for _ in range(rnd.randrange(2, 6))]
        x = len(R) - 1
        if all(w == 0 for w in R[x]):
            continue
        t = srow(R, x)
        p = trio.parent(R, t, x)
        if p is None or p >= len(R) - 1:
            continue
        L = len(R) - 1 - p
        if L <= 0:
            continue
        c = R[p][0]
        if any(R[j][0] < c for j in range(p, p + L)):
            continue
        d0 = R[x][0] - R[p][0] if t > 0 else 0
        d1 = R[x][1] - R[p][1] if t > 1 else 0
        n = rnd.randrange(0, 4)
        key = f'real/i1={t}'
        lhs = shiftl0(c, gcopies(R, p, L, d0, d1, n + 1))
        rhs = (shiftl0(c, seg(R, p, L))
               + shiftr01(d0, 0,
                          Lift1(shiftl0(c, gcopies(R, p, L, d0, d1, n)), d1)))
        note(key + '/H3', lhs == rhs, (R, p, L, d0, d1, n, lhs, rhs))


run_random(60000)
run_real(60000)

print(f"{'case':18s} {'samples':>9s} {'viol':>8s}")
for k in sorted(tot):
    print(f"{k:18s} {tot[k]:9d} {bad[k]:8d}")
for k, e in sorted(ex.items()):
    print(f"  ex {k}: {e}")
