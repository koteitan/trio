"""TbOper: does the principal block's tbAll bound survive expansion?

tbAll X u  :=  every prefix X.take k whose trailing column is an orphan
               (no parent inside the prefix) has level < u.

The whole campaign hinges on this: if tbAll of the PRINCIPAL block
N = (0,v,z) :: R is preserved by oper, the W-hierarchy can be re-indexed by
tbAll, clause 2 can carry natDom again (yapss shape), and then every tower
site's datum is forced to clause 3 -- which supplies the graft closure, so the
whole lift residue dissolves.

Checks, over principal blocks N = (0,v,z) :: R:
 (T0) minimal bound u0(N) := 1 + max{lev of prefix-orphans}  (so tbAll N u0)
 (T1) tbAll (N[n]) u0(N)  for n = 1,2,3        <- TbOper
 (T2) tbAll (N[n]) (max u0(N) (2v+z+1))        <- weaker variant
 (T3) same restricted to zle1 blocks (row 2 <= 1), which is the trio fragment
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


def orphan_lev(X):
    """level of X's trailing column if it is an orphan of X, else None."""
    if not X:
        return None
    j = len(X) - 1
    if lev(X[j]) == 0:
        return None
    if trio.parent(X, srow(X[j]), j) is not None:
        return None
    return lev(X[j])


def u0(X):
    """least u with tbAll X u."""
    best = 0
    for k in range(1, len(X) + 1):
        m = orphan_lev(X[:k])
        if m is not None:
            best = max(best, m)
    return best


def tbAll(X, u):
    for k in range(1, len(X) + 1):
        m = orphan_lev(X[:k])
        if m is not None and m > u:
            return False
    return True


def principal(maxlen, r0, r1):
    cols = [(a, b, c) for a in range(1, r0) for b in range(r1) for c in range(2)]
    for v in range(r1):
        for z in range(2):
            for k in range(1, maxlen):
                for R in itertools.product(cols, repeat=k):
                    yield v, z, list(R)


tot = 0
bad1 = 0
bad2 = 0
ex1 = None
ex2 = None
worst = Counter()

for v, z, R in principal(4, 3, 3):
    N = [(0, v, z)] + R
    b = u0(N)
    tot += 1
    for n in (1, 2, 3):
        E = trio.expand(N, n)
        if not tbAll(E, b):
            bad1 += 1
            if ex1 is None:
                ex1 = (v, z, R, n, b, u0(E), E)
            break
    b2 = max(b, 2 * v + z)
    for n in (1, 2, 3):
        E = trio.expand(N, n)
        if not tbAll(E, b2):
            bad2 += 1
            if ex2 is None:
                ex2 = (v, z, R, n, b2, u0(E), E)
            break

print(f"principal blocks checked: {tot}")
print(f"(T1) tbAll N u0 -> tbAll N[n] u0      : {bad1} violations")
print(f"(T2) with u0 raised to max(u0, 2v+z)  : {bad2} violations")
if ex1:
    print(f"  T1-ex v={ex1[0]} z={ex1[1]} R={ex1[2]} n={ex1[3]} u0={ex1[4]} -> u0(E)={ex1[5]}")
    print(f"    E={ex1[6]}")
if ex2:
    print(f"  T2-ex v={ex2[0]} z={ex2[1]} R={ex2[2]} n={ex2[3]} u={ex2[4]} -> u0(E)={ex2[5]}")
    print(f"    E={ex2[6]}")
