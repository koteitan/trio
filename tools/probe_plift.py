"""Is the machine's element-lift the ambient-relative mask lift?

At a tower-2 site  Nb = (0,v,z) :: R,  oper gives
    Nb[j+1] = (0,v,z) :: graft R (Lift1 (Nb[j]) d1),   d1 = w1 - v,
where Lift1 X t lifts the le1-cone of X's own root (column 0).

The composite lift acts on a grafted argument through the AMBIENT mask
    coneV X v = {j | every le1-ancestor i of j in X has entry1 i > v}
(probe_ycone / probe_liftplant).  Question:

  (Q1) cone(Nb[j])            ==  coneV(Nb[j], v-1) ?      (mask agreement)
  (Q2) Lift1 (Nb[j]) d1       ==  plift (v-1) d1 (Nb[j]) ?
  (Q3) coneV is lift-stable:  coneV (plift v t X) v == coneV X v ?
       (needed for plift v s . plift v t = plift v (s+t))
  (Q4) same for cone: cone (Lift1 X t) == cone X ?
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio


def lev(c):
    return 2 * c[1] + c[2]


def srow(c):
    return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)


def cone(X):
    return {i for i in range(len(X)) if trio.is_ancestor(X, 1, 0, i)}


def anc1(X, j):
    """all strict le1-ancestors of j in X (the row-1 parent chain)."""
    out = []
    p = trio.parent(X, 1, j)
    while p is not None:
        out.append(p)
        p = trio.parent(X, 1, p)
    return out


def coneV(X, v):
    """{j | j itself and all its le1-ancestors carry entry1 > v}."""
    out = set()
    for j in range(len(X)):
        if X[j][1] > v and all(X[i][1] > v for i in anc1(X, j)):
            out.add(j)
    return out


def liftset(X, C, t):
    return [(c[0], c[1] + (t if i in C else 0), c[2]) for i, c in enumerate(X)]


def Lift1(X, t):
    return liftset(X, cone(X), t)


def plift(v, t, X):
    return liftset(X, coneV(X, v), t)


def graft(M, y):
    w = M[-1][0]
    return M[:-1] + [(p[0] + w, p[1], p[2]) for p in y]


def branch(M):
    R = M[1:]
    L = len(R)
    if L == 0:
        return 'nil'
    if L <= 1 and lev(R[0]) == 0:
        return 'B1'
    if trio.parent(R, srow(R[-1]), L - 1) is not None:
        return 'B2a'
    if lev(R[-1]) == 0:
        return 'B2b-succ'
    p = trio.parent(M, srow(R[-1]), L)
    if p == 0:
        return 'B3-tower' + str(srow(R[-1]))
    if p is not None:
        return 'B3-revive-nonroot'
    return 'B3-dead'


def principal(maxlen, r0, r1):
    cols = [(a, b, c) for a in range(1, r0) for b in range(r1) for c in range(2)]
    for v in range(r1):
        for z in range(2):
            for k in range(1, maxlen):
                for R in itertools.product(cols, repeat=k):
                    yield v, z, list(R)


tot = Counter(); bad1 = Counter(); bad2 = Counter()
ex1 = {}; ex2 = {}
tot3 = 0; bad3 = 0; bad4 = 0
ex3 = None; ex4 = None

for v, z, R in principal(4, 3, 3):
    M = [(0, v, z)] + R
    b = branch(M)
    if b != 'B3-tower2':
        continue
    w1 = R[-1][1]
    d1 = w1 - v
    if d1 <= 0:
        continue
    X = M
    for j in range(4):
        # Nb[j]
        X = trio.expand(M, j) if j else []
        if not X:
            continue
        tot[b] += 1
        c = cone(X)
        cv = coneV(X, v - 1) if v >= 1 else coneV(X, -1)
        if c != cv:
            bad1[b] += 1
            if b not in ex1:
                ex1[b] = (v, z, R, j, X, sorted(c), sorted(cv))
        if Lift1(X, d1) != plift(v - 1 if v >= 1 else -1, d1, X):
            bad2[b] += 1
            if b not in ex2:
                ex2[b] = (v, z, R, j, X)
        # (Q3)/(Q4) stability
        tot3 += 1
        if coneV(plift(v, d1, X), v) != coneV(X, v):
            bad3 += 1
            if ex3 is None:
                ex3 = (v, z, R, j, X)
        if cone(Lift1(X, d1)) != cone(X):
            bad4 += 1
            if ex4 is None:
                ex4 = (v, z, R, j, X)

print(f"tower2 objects checked: {sum(tot.values())}")
print(f"(Q1) cone == coneV(v-1) violations: {sum(bad1.values())}")
print(f"(Q2) Lift1 == plift(v-1) violations: {sum(bad2.values())}")
print(f"(Q3) coneV lift-stable: {tot3} cases, {bad3} violations")
print(f"(Q4) cone  lift-stable: {tot3} cases, {bad4} violations")
for b, e in list(ex1.items())[:2]:
    print(f"  Q1-ex v={e[0]} z={e[1]} R={e[2]} j={e[3]}")
    print(f"    X={e[4]}")
    print(f"    cone={e[5]} coneV={e[6]}")
if ex3:
    print(f"  Q3-ex v={ex3[0]} z={ex3[1]} R={ex3[2]} j={ex3[3]} X={ex3[4]}")
if ex4:
    print(f"  Q4-ex v={ex4[0]} z={ex4[1]} R={ex4[2]} j={ex4[3]} X={ex4[4]}")
