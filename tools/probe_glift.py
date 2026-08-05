"""The staircase lift `glift` -- the closure of the mask lifts.

For a column j put  mu(j) := min of row 1 over j's row-0 ancestors (j included).
Then  coneV A v = {j | mu j > v}, so `mlift A v s` adds `s` exactly where
mu > v.  Composing mask lifts therefore produces a STAIRCASE

    phi(m) = m + sum_i s_i * [m > v_i]        (finitely many (v_i, s_i))

and `glift A phi` lifts column j by `phi(mu j) - mu j`.  The class of such phi
is closed under composition (phi(m) - m is nondecreasing), so this is the
smallest language containing every `mlift`.

Checks:
  (G2) glift (A[n]) phi = (glift A phi)[n]     -- commutes with expansion
  (G5) glift (glift A phi1) phi2 = glift A (phi2 . phi1)   -- composition
  (G6) mu (glift A phi) j = phi (mu A j)       -- the parameter transforms
  (G3) glift distributes over graft with the SAME phi, guarded by the site:
       glift (graft M y) phi = graft (glift M phi) (glift y phi) when the
       graft point's context ancestors do not lower mu below the split.
"""
import sys, random
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

def anc0(X, j):
    out = []; p = j
    while p is not None:
        out.append(p); p = trio.parent(X, 0, p)
    return out

def mu(X, j):
    return min(X[y][1] for y in anc0(X, j))

def mk_phi(pairs):
    def phi(m):
        return m + sum(s for (v, s) in pairs if m > v)
    return phi

def glift(A, phi):
    return [(c[0], c[1] + phi(mu(A, i)) - mu(A, i), c[2]) for i, c in enumerate(A)]

def graft(M, y):
    w = M[-1][0]
    return M[:-1] + [(p[0] + w, p[1], p[2]) for p in y]

COLS = [(a, b, c) for a in range(3) for b in range(4) for c in range(2)]
rnd = random.Random(555111)

tot = 0
bad2 = bad5 = bad6 = bad3 = 0
ex2 = ex5 = ex3 = None
site_ok = 0

N = 40000
for _ in range(N):
    A = [(0, rnd.randrange(4), rnd.randrange(2))] + \
        [rnd.choice(COLS) for _ in range(rnd.randrange(1, 4))]
    pairs1 = [(rnd.randrange(4), rnd.randrange(1, 3))
              for _ in range(rnd.randrange(1, 3))]
    pairs2 = [(rnd.randrange(6), rnd.randrange(1, 3))
              for _ in range(rnd.randrange(1, 3))]
    phi1 = mk_phi(pairs1); phi2 = mk_phi(pairs2)
    n = rnd.randrange(1, 3)
    tot += 1

    if glift(trio.expand(A, n), phi1) != trio.expand(glift(A, phi1), n):
        bad2 += 1
        if ex2 is None:
            ex2 = (A, pairs1, n)
    comp = lambda m: phi2(phi1(m))
    if glift(glift(A, phi1), phi2) != glift(A, comp):
        bad5 += 1
        if ex5 is None:
            ex5 = (A, pairs1, pairs2)
    G = glift(A, phi1)
    if any(mu(G, j) != phi1(mu(A, j)) for j in range(len(A))):
        bad6 += 1

    # (G3) distributivity over a graft
    M = [(0, rnd.randrange(4), rnd.randrange(2))] + \
        [rnd.choice(COLS) for _ in range(rnd.randrange(1, 3))]
    y = A
    s = len(M) - 1
    # the graft point's context ancestors, the point itself excluded
    ctx_min = min([M[q][1] for q in anc0(M, s) if q != s], default=None)
    lhs = glift(graft(M, y), phi1)
    if ctx_min is None:
        rhs = graft(glift(M, phi1), glift(y, phi1))
        site_ok += 1
    else:
        # the composite's mu on the y-part is min(mu_y, ctx_min)
        rhs = graft(glift(M, phi1),
                    [(c[0], c[1] + phi1(min(mu(y, i), ctx_min))
                      - min(mu(y, i), ctx_min), c[2]) for i, c in enumerate(y)])
    if lhs != rhs:
        bad3 += 1
        if ex3 is None:
            ex3 = (M, y, pairs1, lhs, rhs)

print(f"samples: {tot}")
print(f"  (G2) glift commutes with expansion : {bad2} violations")
print(f"  (G5) glift composes                : {bad5} violations")
print(f"  (G6) mu transforms as phi          : {bad6} violations")
print(f"  (G3) glift over graft (mu-min form): {bad3} violations")
if ex2:
    print(f"  G2-ex A={ex2[0]} pairs={ex2[1]} n={ex2[2]}")
if ex5:
    print(f"  G5-ex A={ex5[0]} p1={ex5[1]} p2={ex5[2]}")
if ex3:
    print(f"  G3-ex M={ex3[0]} y={ex3[1]} p={ex3[2]}")
    print(f"    lhs={ex3[3]}")
    print(f"    rhs={ex3[4]}")
