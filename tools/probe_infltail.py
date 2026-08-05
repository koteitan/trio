"""Does the ambient root lift restrict to an infix as the infix's OWN root lift?

To thread the new context component `CtxInf` (the context's re-based infixes
are themselves `W`-packages) through the machine, the only non-mechanical step
is the lifted context `Rt = ltail v z R t`.  What is needed is

  (IL)  shiftl0 c (seg Rt p (k+1))
          = mlift (shiftl0 c (seg R p (k+1))) v t   if le1 ((0,v,z)::R) 0 (p+1)
          = shiftl0 c (seg R p (k+1))               otherwise

MEASURED (first run, with `Lift1 ... t` instead of `mlift ... v t`): the naive
root-lift form is FALSE (1911/35973 even under the window condition) because the
ambient root's row-1 value can be BELOW the infix root's, so the ambient cone
restricted to the infix is strictly larger than the infix's own root cone.  The
right object is the AMBIENT MASK LIFT `mlift . v t` = a staircase lift
(`Cgraft.mlift_eq_slift`): under the window condition the row-0 chain from a
column of the infix reaches `p` before leaving it, so
`amin_N(q) = min (amin_infix q) (amin_N p)`, and with `p` in the ambient cone
that is `> v` exactly when `amin_infix q > v`.

i.e. the ambient row-1 cone, restricted to the infix [p, p+k], is exactly the
infix's own root cone (when the infix root is in the ambient cone), and misses
it entirely otherwise.

Danger: a column q of the infix can sit in the ambient cone via a row-1 chain
that SKIPS p and descends below it, in which case `ltail` lifts q but
`Lift1 (infix)` does not.  Measured here, split by whether the infix satisfies
the window condition `entry R 0 p < entry R 0 j` for p < j <= p+k (which is what
a blocker's window always gives).
"""
import sys
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio


def seg(R, a, L):
    return [tuple(R[j]) for j in range(a, a + L)]


def shiftl0(c, X):
    return [(q[0] - c, q[1], q[2]) for q in X]


def Lift1(X, t):
    return [(q[0], q[1] + (t if trio.is_ancestor(X, 1, 0, i) else 0), q[2])
            for i, q in enumerate(X)]


def anc0(X, j):
    out = []
    q = j
    while q is not None:
        out.append(q)
        q = trio.parent(X, 0, q)
    return out


def amin(X, j):
    return min(X[y][1] for y in anc0(X, j))


def mlift(X, v, t):
    """lift row 1 by t on the columns whose ancestor-minimum exceeds v."""
    return [(cc[0], cc[1] + (t if amin(X, i) > v else 0), cc[2])
            for i, cc in enumerate(X)]


def ltail(v, z, R, t):
    """tail of Lift1 ((0,v,z) :: R) t."""
    N = [(0, v, z)] + [tuple(c) for c in R]
    return Lift1(N, t)[1:]


COLS = [(a, b, c) for a in range(1, 6) for b in range(4) for c in range(2)]
rnd = random.Random(8021)

tot = Counter()
bad = Counter()
ex = {}

N = 150000
for _ in range(N):
    R = [rnd.choice(COLS) for _ in range(rnd.randrange(2, 8))]
    v = rnd.randrange(4)
    z = rnd.randrange(2)
    t = rnd.randrange(0, 3)
    p = rnd.randrange(0, len(R) - 1)
    k = rnd.randrange(0, len(R) - 1 - p)
    c = R[p][0]
    win = all(R[j][0] > c for j in range(p + 1, p + k + 1))
    Rt = ltail(v, z, R, t)
    Nn = [(0, v, z)] + [tuple(cc) for cc in R]
    inc = trio.is_ancestor(Nn, 1, 0, p + 1)          # p in the ambient cone?
    lhs = shiftl0(c, seg(Rt, p, k + 1))
    base = shiftl0(c, seg(R, p, k + 1))
    rhs = mlift(base, v, t) if inc else base
    key = ('win' if win else 'nowin') + ('/in' if inc else '/out')
    tot[key] += 1
    if lhs != rhs:
        bad[key] += 1
        ex.setdefault(key, (R, v, z, t, p, k, lhs, rhs))

print(f"{'case':12s} {'samples':>9s} {'viol':>8s}")
for k_ in sorted(tot):
    print(f"{k_:12s} {tot[k_]:9d} {bad[k_]:8d}")
for k_, e in sorted(ex.items()):
    print(f"  ex {k_}: {e}")
