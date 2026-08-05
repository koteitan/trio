"""Does the composite lift act as the argument's OWN full lift?

N = (0,v,z) :: graft R y,  y based.
(RAISED)  y[0][1] > v :   liftArgN(N,t) =?= (0,v+t,z) :: graft (ltail R t) (Lift1 y t)
(LOW)     y[0][1] <= v:   liftArgN(N,t) =?= (0,v+t,z) :: graft (ltail R t) y   [known]

If (RAISED) holds, `Lift1 (graft E D) t = graft (Lift1 E t) (Lift1 D t)` for the
machine's planted blocks, which closes the beta/alpha lift induction with the
forall-s strengthened hypothesis (Lift1_Lift1).
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


def based_blocks(maxlen, r0, r1):
    cols = [(a, b, c) for a in range(1, r0) for b in range(r1) for c in range(2)]
    yield []
    for vv in range(r1):
        for zz in range(2):
            yield [(0, vv, zz)]
            for k in range(1, maxlen):
                for T in itertools.product(cols, repeat=k):
                    yield [(0, vv, zz)] + list(T)


YS = list(based_blocks(2, 3, 4))

totR = Counter(); badR = Counter()
totL = Counter(); badL = Counter()
exR = {}; exL = {}

for v, z, R in principal(3, 3, 4):
    M = [(0, v, z)] + R
    b = branch(M)
    for t in (1, 2):
        Rt = Lift1(M, t)[1:]
        for y in YS:
            if not y:
                continue
            N = [(0, v, z)] + graft(R, y)
            lhs = Lift1(N, t)
            if y[0][1] > v:
                totR[b] += 1
                rhs = [(0, v + t, z)] + graft(Rt, Lift1(y, t))
                if lhs != rhs:
                    badR[b] += 1
                    if b not in exR:
                        exR[b] = (v, z, R, y, t, lhs, rhs)
            else:
                totL[b] += 1
                rhs = [(0, v + t, z)] + graft(Rt, y)
                if lhs != rhs:
                    badL[b] += 1
                    if b not in exL:
                        exL[b] = (v, z, R, y, t, lhs, rhs)

print(f"{'branch':20s} {'RAISED':>10s} {'viol':>8s} {'LOW':>10s} {'viol':>8s}")
for b in sorted(set(totR) | set(totL)):
    print(f"{b:20s} {totR[b]:10d} {badR[b]:8d} {totL[b]:10d} {badL[b]:8d}")
for b, e in list(exR.items())[:3]:
    print(f"  RAISED-ex {b}: v={e[0]} z={e[1]} R={e[2]} y={e[3]} t={e[4]}")
    print(f"    lhs={e[5]}")
    print(f"    rhs={e[6]}")
for b, e in list(exL.items())[:2]:
    print(f"  LOW-ex {b}: v={e[0]} z={e[1]} R={e[2]} y={e[3]} t={e[4]}")
    print(f"    lhs={e[5]}")
    print(f"    rhs={e[6]}")
