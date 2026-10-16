"""Exact decision of Lean's `Lhd z b a` (FS.lean):
  b < a ∧ ∀ u c, b < c → c ≤ a → Dom (comps u b) (comps u c ++ [z]).
c ranges over all trees (lexicographic `lt`, Term.lean), not only standard ones.

Dom over a total order is max ≤ max.  K_u(c) := max (z :: comps u c).
Failure ⟺ ∃ u, ∃ c ∈ (b, a], K_u(c) < g_u := max (comps u b).
comps u t shrinks as u grows, so for u in an interval between consecutive indices of b
the worst u is the largest one: it suffices to take u among the indices of b.

∃ c ∈ I, K_u(c) < g is decided structurally (ex_K).  c = psi v x r:
  K(c) = max (Kh v x) (K r),  Kh v x = z if v < u else max x (K x) (K v).
"""
import sys
sys.setrecursionlimit(100000)
Z = ()


def lt(x, y):
    if not y: return False
    if not x: return True
    if x[0] != y[0]: return lt(x[0], y[0])
    if x[1] != y[1]: return lt(x[1], y[1])
    return lt(x[2], y[2])


def le(x, y): return x == y or lt(x, y)


def comps(u, t):
    if not t: return []
    v, x, c = t
    r = [] if lt(v, u) else [x] + comps(u, x) + comps(u, v)
    return r + comps(u, c)


def succ(t):
    """Immediate successor in the lexicographic tree order."""
    return (Z, Z, Z) if not t else (t[0], t[1], succ(t[2]))


def tmax(l):
    m = Z
    for g in l:
        if lt(m, g): m = g
    return m


# An interval: (lo, hi); lo is an inclusive lower bound tree (None = z, the least tree),
# hi = None (unbounded) or (tree, inclusive).
def nonempty(I):
    lo, hi = I
    if hi is None: return True
    l = Z if lo is None else lo
    t, inc = hi
    return le(l, t) if inc else lt(l, t)


def meet_lo(a, b):
    if a is None: return b
    if b is None: return a
    return b if lt(a, b) else a


def meet_hi(a, b):
    if a is None: return b
    if b is None: return a
    (s, i), (t, j) = a, b
    if s == t: return (s, i and j)
    return a if lt(s, t) else b


def meet(I, J): return (meet_lo(I[0], J[0]), meet_hi(I[1], J[1]))


FULL = (None, None)
def point(t): return (t, (t, True))


def boxes(I):
    """The psi-part of I as products V × X × R of intervals."""
    lo, hi = I
    if lo is None or lo == Z:
        L = [(FULL, FULL, FULL)]
    else:
        lv, lx, lr = lo
        L = [((succ(lv), None), FULL, FULL),
             (point(lv), (succ(lx), None), FULL),
             (point(lv), point(lx), (lr, None))]
    if hi is None:
        U = [(FULL, FULL, FULL)]
    else:
        t, inc = hi
        if not t:
            return []
        hv, hx, hr = t
        U = [((None, (hv, False)), FULL, FULL),
             (point(hv), (None, (hx, False)), FULL),
             (point(hv), point(hx), (None, (hr, inc)))]
    out = []
    for a in L:
        for b in U:
            bx = tuple(meet(p, q) for p, q in zip(a, b))
            if all(nonempty(c) for c in bx):
                out.append(bx)
    return out


def has_z(I):
    lo, hi = I
    return (lo is None or lo == Z) and nonempty(I)


def ex_K(u, g):
    """Returns f(I): ∃ c ∈ I, K_u(c) < g."""
    busy = set(); memo = {}; hit = [0]

    def f(I):
        if not g or not nonempty(I): return False
        if has_z(I): return True
        if I in memo: return memo[I]
        if I in busy:
            hit[0] += 1
            return False                    # least fixpoint: a witness is finite
        busy.add(I)
        h0 = hit[0]
        res = False
        for V, X, R in boxes(I):
            lowV = Z if V[0] is None else V[0]
            A = lt(lowV, u) or (f(meet(V, (u, None))) and f(meet(X, (None, (g, False)))))
            if A and f(R):
                res = True
                break
        busy.discard(I)
        if res or hit[0] == h0:
            memo[I] = res
        return res
    return f


def indices(t, acc):
    if not t: return
    acc.add(t[0]); indices(t[0], acc); indices(t[1], acc); indices(t[2], acc)


def lhd(b, a):
    """Exact `Lhd z b a`."""
    if not lt(b, a): return False
    us = set(); indices(b, us)
    I = (succ(b), (a, True))
    for u in us:
        g = tmax(comps(u, b))
        if not g: continue
        if ex_K(u, g)(I): return False
    return True


def lhdE(b, a): return b == a or lhd(b, a)
