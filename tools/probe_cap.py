"""⚠ SUPERSEDED by probe_cap2.py — this script models the WRONG leaf rule.

`trio.expand` peels a length-1 sequence to `[]` (the `r is None` branch),
but Lean's `oper` is the IDENTITY at length 1 (`if j1 = 0 then M`).  So a
positive-level root `[(0,v,z)]` never terminates in the Lean model; it is in
`W a` only via clause 3, i.e. exactly when `2v+z <= a`.  Consequently the
"reaches []" criterion below tests a DIFFERENT (weaker) statement and never
sees the stage.  Kept for the record; use probe_cap2.py.

Original description:

Soundness check for the single remaining core `CoreCap` (catch #8 discipline).

`CoreCap` says: for an equipped context `M` (root `(0,v,z)`, `z <= 1`,
`argOK M` = every column's row-0 depth is positive), replacing `M`'s LAST
column's subscript by an arbitrary `(b,c)` keeps the planted block a
`W`-package:

    Lift1 ((0,v,z) :: cap M b c) t  in  W a       (a >= 2(v+t)+z)
    cap M b c = M.dropLast ++ [(entry M 0 (|M|-1), b, c)]

`W 0` is exactly the hereditarily-terminating set (clause 2 of `Aop` is the
`forall n, M[n] in X` clause and `W` is a least fixed point), and `W` is
monotone, so a NECESSARY condition for `CoreCap` is that every such capped
composite terminates under BM4 expansion.  This probe searches for a
non-terminating (or explosively growing) instance.

The equipment `CtxOK M v z` is not decidable here; it is APPROXIMATED by
"every planted prefix `(0,v,z) :: M.take k` terminates", which is exactly what
`CtxOK` asserts (`W`-membership at the slice), so the approximation is faithful
up to the stage bookkeeping.

Reported: number of instances whose expansion did not reach `[]` within the
step budget (both for the equipment prefixes and for the capped composite).
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio


STEPS = 200
NMAX = 3
SIZE_CAP = 1500


def terminates(S, nseq):
    """Run the expansion with the given n-schedule; True if it reaches []."""
    cur = [tuple(c) for c in S]
    for i in range(STEPS):
        if not cur:
            return True
        if len(cur) > SIZE_CAP:
            return None            # gave up: too big to decide here
        cur = [tuple(c) for c in trio.expand(cur, nseq[i % len(nseq)])]
    return False


def lift1(S, t):
    return [(c[0], c[1] + (t if trio.is_ancestor(S, 1, 0, i) else 0), c[2])
            for i, c in enumerate(S)]


COLS = [(a, b, c) for a in range(1, 3) for b in range(2) for c in range(2)]

tot = Counter()
bad = Counter()
ex = {}

for L in (1, 2):
    for M in itertools.product(COLS, repeat=L):
        M = list(M)
        for v in range(3):
            for z in range(2):
                # equipment approximation: every planted prefix terminates
                eq = True
                for k in range(L):
                    for t in range(2):
                        P = lift1([(0, v, z)] + M[:k], t)
                        r = terminates(P, (1, 2, 3))
                        if r is not True:
                            eq = False
                if not eq:
                    tot['ctx/not-equipped'] += 1
                    continue
                tot['ctx/equipped'] += 1
                for b in range(3):
                    for c in range(3):
                        cap = M[:-1] + [(M[-1][0], b, c)]
                        for t in range(2):
                            X = lift1([(0, v, z)] + cap, t)
                            for nseq in ((1, 1), (1, 2, 3)):
                                key = f'cap/z={z}/c={c}'
                                tot[key] += 1
                                r = terminates(X, nseq)
                                if r is not True:
                                    bad[key] += 1
                                    ex.setdefault(key, (M, v, z, b, c, t,
                                                        nseq, r))

print(f"{'case':22s} {'samples':>9s} {'viol':>8s}")
for k in sorted(tot):
    print(f"{k:22s} {tot[k]:9d} {bad[k]:8d}")
for k, e in sorted(ex.items()):
    print(f"  ex {k}: {e}")
