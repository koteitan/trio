"""Does the machine's plant datum sit at or below the ambient root's row 1?

CoreLiftPlant needs  Lift1 ((0,v,z) :: graft M D) t in GX.  Decomposition
(composite-lift formula + gx_graft):

  Lift1 (graft E D) t = graft (Lift1 E t) (plift v t D),   E = (0,v,z)::M

and plift v t D = D exactly when coneV D v = {} , which holds as soon as
every column of D carries entry1 <= v ... but in fact the mask is empty
already when D's ROOT carries entry1 <= v (probe_ycone (B)).

So: at genuine tower sites of a composite (0,v,z) :: graft M Y, how often is
entry Y 1 0 > v (i.e. the element part of the residue is nontrivial)?
Also: how often is coneV (Y.dropLast) v nonempty?
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


def anc1(X, j):
    out = []
    p = trio.parent(X, 1, j)
    while p is not None:
        out.append(p)
        p = trio.parent(X, 1, p)
    return out


def coneV(X, v):
    out = set()
    for j in range(len(X)):
        if X[j][1] > v and all(X[i][1] > v for i in anc1(X, j)):
            out.add(j)
    return out


def graft(M, y):
    w = M[-1][0]
    return M[:-1] + [(p[0] + w, p[1], p[2]) for p in y]


def site(M):
    """branch of the principal block M = (0,v,z) :: R."""
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
        return 'tower' + str(srow(R[-1]))
    if p is not None:
        return 'revive-nonroot'
    return 'dead'


def ctxs(maxlen, r0, r1):
    cols = [(a, b, c) for a in range(1, r0) for b in range(r1) for c in range(2)]
    for k in range(2, maxlen):
        for M in itertools.product(cols, repeat=k):
            yield list(M)


def args(maxlen, r0, r1):
    cols = [(a, b, c) for a in range(1, r0) for b in range(r1) for c in range(2)]
    for vy in range(r1):
        for zy in range(2):
            for k in range(1, maxlen):
                for T in itertools.product(cols, repeat=k):
                    yield [(0, vy, zy)] + list(T)


MS = list(ctxs(4, 3, 3))
YS = list(args(3, 3, 3))

tot = Counter(); hi = Counter(); nonempty = Counter()
ex = {}

for M in MS:
    for Y in YS:
        R = graft(M, Y)
        for v in range(3):
            for z in range(2):
                N = [(0, v, z)] + R
                b = site(N)
                if b not in ('tower1', 'tower2'):
                    continue
                tot[b] += 1
                D = Y[:-1]
                if not D:
                    continue
                if all(q[1] > v for q in D):
                    hi[b] += 1
                else:
                    if b not in ex:
                        ex[b] = (v, z, M, Y, min(q[1] for q in D))
                if len(coneV(D, v)) == len(D):
                    nonempty[b] += 1

print(f"{'site':10s} {'cases':>10s} {'all col>v':>10s} {'coneV=all':>16s}")
for b in sorted(tot):
    print(f"{b:10s} {tot[b]:10d} {hi[b]:10d} {nonempty[b]:16d}")
for b, e in ex.items():
    print(f"  ex {b}: v={e[0]} z={e[1]} M={e[2]} Y={e[3]} coneV={e[4]}")

