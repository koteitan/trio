"""At a DEAD site, does the graft commute with the composite lift?

Branch (c): N = (0,v,z) :: R whose trailing column is an orphan that even the
root does not revive.  If clause 2 is to carry natDom (the yapss shape), (c)
must go through clause 3, i.e. we must supply

    for all w:   graft (Lift1 N t) w  ==  Lift1 (graft N w) t          (G)

(then the datum's own clause-3 data discharges it).  (G) is the last question
on the "restore tbAll + natDom" route: TbOper is probe-clean (0/11304), and
tbAll bounds the dead orphan's level, so clause 3 is in range at (c).

Also measured:
 (G1) (G) over all dead sites and all based w
 (G2) (G) restricted to w whose levels are <= the dead orphan's level - 1
      (which is what clause 3 actually feeds: w in W m, m = lev - 1)
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


def Lift1(X, t):
    C = cone(X)
    return [(c[0], c[1] + (t if i in C else 0), c[2]) for i, c in enumerate(X)]


def graft(M, y):
    w = M[-1][0]
    return M[:-1] + [(p[0] + w, p[1], p[2]) for p in y]


def dead_site(N):
    """the trailing column is an orphan of N (not revived by the root)."""
    j = len(N) - 1
    if j <= 0 or lev(N[j]) == 0:
        return False
    return trio.parent(N, srow(N[j]), j) is None


def principal(maxlen, r0, r1):
    cols = [(a, b, c) for a in range(1, r0) for b in range(r1) for c in range(2)]
    for v in range(r1):
        for z in range(2):
            for k in range(1, maxlen):
                for R in itertools.product(cols, repeat=k):
                    yield v, z, list(R)


def based_blocks(maxlen, r0, r1):
    cols = [(a, b, c) for a in range(1, r0) for b in range(r1) for c in range(2)]
    yield []
    for vy in range(r1):
        for zy in range(2):
            yield [(0, vy, zy)]
            for k in range(1, maxlen):
                for T in itertools.product(cols, repeat=k):
                    yield [(0, vy, zy)] + list(T)


WS = list(based_blocks(3, 3, 4))

tot1 = 0; bad1 = 0; ex1 = None
tot2 = 0; bad2 = 0; ex2 = None

for v, z, R in principal(4, 3, 3):
    N = [(0, v, z)] + R
    if not dead_site(N):
        continue
    m = lev(N[-1]) - 1
    for t in (1, 2):
        NT = Lift1(N, t)
        for w in WS:
            lhs = graft(NT, w)
            rhs = Lift1(graft(N, w), t)
            tot1 += 1
            okg = (lhs == rhs)
            if not okg:
                bad1 += 1
                if ex1 is None:
                    ex1 = (v, z, R, t, w, lhs, rhs)
            if all(lev(c) <= m for c in w):
                tot2 += 1
                if not okg:
                    bad2 += 1
                    if ex2 is None:
                        ex2 = (v, z, R, t, w, lhs, rhs)

print(f"(G1) all based w      : {tot1} cases, {bad1} violations")
print(f"(G2) w with levels<=m : {tot2} cases, {bad2} violations")
if ex1:
    print(f"  G1-ex v={ex1[0]} z={ex1[1]} R={ex1[2]} t={ex1[3]} w={ex1[4]}")
    print(f"    lhs={ex1[5]}")
    print(f"    rhs={ex1[6]}")
if ex2:
    print(f"  G2-ex v={ex2[0]} z={ex2[1]} R={ex2[2]} t={ex2[3]} w={ex2[4]}")
    print(f"    lhs={ex2[5]}")
    print(f"    rhs={ex2[6]}")
