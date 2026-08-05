"""At GENUINE tower-2 sites, does the composite lift act on the family element
as one more Lift1?

  Nb = (0,v,z) :: R,  site: srow(last)=2, root is the parent (tower2),
  d1 = w1 - v,  Nb[j+1] = (0,v,z) :: graft R (Lift1 (Nb[j]) d1).

  (T)  Lift1 (Nb[j+1]) s == (0,v+s,z) :: graft (ltail v z R s)
                                            (Lift1 (Nb[j]) (d1 + s))

If (T) holds, the family induction can carry "for all s" and close by
Lift1_Lift1 (the element-lift parameter just adds), which kills CoreLift for
the beta branch.

  (T1) the row-1 analogue at tower-1 sites, for the tow tower:
       Lift1 (tow v z R k) s == tow (v+s) z (ltail v z R s) k ?
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


def liftset(X, C, t):
    return [(c[0], c[1] + (t if i in C else 0), c[2]) for i, c in enumerate(X)]


def Lift1(X, t):
    return liftset(X, cone(X), t)


def graft(M, y):
    w = M[-1][0]
    return M[:-1] + [(p[0] + w, p[1], p[2]) for p in y]


def ltail(v, z, R, s):
    return Lift1([(0, v, z)] + R, s)[1:]


def tow(v, z, R, k):
    if k == 0:
        return []
    return [(0, v, z)] + graft(R, tow(v, z, R, k - 1))


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


totT = 0; badT = 0; exT = None
totT1 = 0; badT1 = 0; exT1 = None

for v, z, R in principal(4, 3, 4):
    M = [(0, v, z)] + R
    b = branch(M)
    if b == 'B3-tower2':
        d1 = R[-1][1] - v
        Nb = {0: []}
        for j in range(4):
            Nb[j + 1] = [(0, v, z)] + graft(R, Lift1(Nb[j], d1))
        for j in range(4):
            for s in (1, 2):
                totT += 1
                lhs = Lift1(Nb[j + 1], s)
                rhs = [(0, v + s, z)] + graft(ltail(v, z, R, s),
                                              Lift1(Nb[j], d1 + s))
                if lhs != rhs:
                    badT += 1
                    if exT is None:
                        exT = (v, z, R, j, s, lhs, rhs)
    elif b == 'B3-tower1':
        for k in range(4):
            for s in (1, 2):
                totT1 += 1
                lhs = Lift1(tow(v, z, R, k), s)
                rhs = tow(v + s, z, ltail(v, z, R, s), k)
                if lhs != rhs:
                    badT1 += 1
                    if exT1 is None:
                        exT1 = (v, z, R, k, s, lhs, rhs)

print(f"(T)  tower2 family lift: {totT} cases, {badT} violations")
if exT:
    print(f"  ex: v={exT[0]} z={exT[1]} R={exT[2]} j={exT[3]} s={exT[4]}")
    print(f"    lhs={exT[5]}")
    print(f"    rhs={exT[6]}")
print(f"(T1) tower1 tow lift  : {totT1} cases, {badT1} violations")
if exT1:
    print(f"  ex: v={exT1[0]} z={exT1[1]} R={exT1[2]} k={exT1[3]} s={exT1[4]}")
    print(f"    lhs={exT1[5]}")
    print(f"    rhs={exT1[6]}")
