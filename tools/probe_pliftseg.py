"""Structure of the ambient mask lift `plift v e D`.

The residue is  plift v e D in GX  for D in GX, where
   plift v e D = D with +e on coneV D v,
   coneV D v = {j | j and all its le1-ancestors in D carry entry1 > v}.

If coneV D v is a union of *subtrees* (maximal contiguous runs whose columns
all sit strictly deeper than the column just before the run), then D splits by
grafts and plift acts on each piece as the UNIFORM row-1 shift `shiftr1 e`,
for which trio already has a full equivariance suite.  Then
   CorePlift  <=  gx_graft (segment recursion) + GX closed under shiftr1.

(S1) coneV runs are contiguous subtrees:
     for a maximal run [a,b] of coneV columns, every k in (a,b] is deeper
     than a, and the column before a (if any) is shallower than a.
(S2) coneV is closed under row-0 descendants that stay above v:
     j in coneV, k a row-0 descendant of j, entry1 k > v  =>  k in coneV.
(S3) plift = shiftr1 on each run (automatic if (S1) holds; checked anyway).
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio


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


def runs(S, n):
    """maximal contiguous runs of S inside range(n)."""
    out = []
    j = 0
    while j < n:
        if j in S:
            k = j
            while k + 1 < n and (k + 1) in S:
                k += 1
            out.append((j, k))
            j = k + 1
        else:
            j += 1
    return out


def based_blocks(maxlen, r0, r1):
    cols = [(a, b, c) for a in range(1, r0) for b in range(r1) for c in range(2)]
    for vy in range(r1):
        for zy in range(2):
            yield [(0, vy, zy)]
            for k in range(1, maxlen):
                for T in itertools.product(cols, repeat=k):
                    yield [(0, vy, zy)] + list(T)


DS = list(based_blocks(4, 3, 4))

tot = 0
bad1 = 0; bad1b = 0; bad2 = 0
ex1 = None; ex1b = None; ex2 = None

for D in DS:
    n = len(D)
    for v in range(4):
        C = coneV(D, v)
        if not C:
            continue
        tot += 1
        # (S1) each run is a subtree: everything inside deeper than its head,
        #      and the head is the shallowest of the run
        ok = True
        for (a, b) in runs(C, n):
            for k in range(a + 1, b + 1):
                if D[k][0] <= D[a][0]:
                    ok = False
            # the run must not be cut short by a deeper non-cone column
            if b + 1 < n and D[b + 1][0] > D[a][0] and (b + 1) not in C:
                ok = False
                if ex1b is None:
                    ex1b = (v, D, sorted(C), (a, b))
        if not ok:
            bad1 += 1
            if ex1 is None:
                ex1 = (v, D, sorted(C), runs(C, n))
        # (S2) descendants above v stay in the cone
        for j in C:
            for k in range(j + 1, n):
                if D[k][0] <= D[j][0]:
                    break
                if D[k][1] > v and k not in C:
                    bad2 += 1
                    if ex2 is None:
                        ex2 = (v, D, sorted(C), j, k)
                    break

print(f"cases (nonempty mask): {tot}")
print(f"(S1) runs are subtrees      : {bad1} violations")
print(f"(S1b) runs not cut mid-subtree: {'yes' if ex1b else 'no'}")
print(f"(S2) descendants above v     : {bad2} violations")
if ex1:
    print(f"  S1-ex v={ex1[0]} D={ex1[1]} cone={ex1[2]} runs={ex1[3]}")
if ex1b:
    print(f"  S1b-ex v={ex1b[0]} D={ex1b[1]} cone={ex1b[2]} run={ex1b[3]}")
if ex2:
    print(f"  S2-ex v={ex2[0]} D={ex2[1]} cone={ex2[2]} j={ex2[3]} k={ex2[4]}")
