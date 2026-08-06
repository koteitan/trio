"""Sharp soundness check for `CoreCap` — now with the STAGE (catch #7 fix).

probe_cap.py used `trio.expand`, which peels a length-1 sequence to `[]`.
Lean's `oper` is the IDENTITY at length 1 (`if j1 = 0 then M`), so a length-1
sequence never enters `W a` through clause 2; it enters only through clause 3,
and `Om_mem_W` makes that exactly

    [(d, v, z)] in W a   <->   2*v + z <= a.

For length >= 2, `aop_clause3_to_clause2` (Lean) shows clause 3 is absorbed by
clause 2, so by `A1` (the fixed-point equation)

    |S| >= 2  =>  ( S in W a  <->  forall n >= 1, S[n] in W a ).

That gives an exact recursive characterisation whose only leaves are the
length-<= 1 sequences.  A definite REFUTATION of `CoreCap` is therefore:
the expansion tree of the capped composite reaches a singleton of level > a.

Enumerated: contexts `M` with `argOK M` (row-0 depths positive), roots `(v,z)`
with `z <= 1`, lifts `t`, and caps `(b,c)`; the stage is the MINIMAL admissible
one `a = 2(v+t)+z` (the binding case, since `W` is monotone).  The equipment
`CtxOK M v z` is checked with the same recursive membership test on every
planted prefix at its own minimal stage.

Outcome per instance: 'ok' (tree closed with all leaves admissible),
'VIOL' (a leaf of level > a was reached: `CoreCap` would be false), or
'unknown' (depth/size budget exhausted).
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)             # clause 2 is forall n >= 1; any failing n refutes
MAXDEPTH = 8
MAXLEN = 24


def lev(col):
    return 2 * col[1] + col[2]


def lift1(S, t):
    return [(c[0], c[1] + (t if trio.is_ancestor(S, 1, 0, i) else 0), c[2])
            for i, c in enumerate(S)]


def inW(S, a, depth, memo):
    """None = unknown (budget), True = closed, False = definite non-membership."""
    S = tuple(tuple(c) for c in S)
    key = (S, a)
    if key in memo:
        return memo[key]
    if len(S) == 0:
        return True
    if len(S) == 1:
        r = lev(S[0]) <= a                      # clause 1 (lev 0) or clause 3
        memo[key] = r
        return r
    if depth <= 0 or len(S) > MAXLEN:
        return None
    memo[key] = None                            # cycle guard
    out = True
    for n in NS:
        r = inW(trio.expand(list(S), n), a, depth - 1, memo)
        if r is False:
            memo[key] = False
            return False
        if r is None:
            out = None
    memo[key] = out
    return out


COLS = [(d, b, c) for d in range(1, 3) for b in range(2) for c in range(2)]

tot = Counter()
ex = {}
memo = {}

for L in (1, 2):
    for M in itertools.product(COLS, repeat=L):
        M = list(M)
        for v in range(3):
            for z in range(2):
                # equipment: every planted prefix, at its own minimal stage
                eq = True
                for k in range(L):
                    for t in range(2):
                        P = lift1([(0, v, z)] + M[:k], t)
                        if inW(P, 2 * (v + t) + z, MAXDEPTH, memo) is not True:
                            eq = False
                if not eq:
                    tot['ctx/not-equipped'] += 1
                    continue
                tot['ctx/equipped'] += 1
                for b in range(3):
                    for c in range(2):
                        cap = M[:-1] + [(M[-1][0], b, c)]
                        for t in range(2):
                            a = 2 * (v + t) + z
                            X = lift1([(0, v, z)] + cap, t)
                            r = inW(X, a, MAXDEPTH, memo)
                            key = ('VIOL' if r is False
                                   else 'ok' if r is True else 'unknown')
                            tot['cap/' + key] += 1
                            if r is not True:
                                ex.setdefault(key, (M, v, z, b, c, t, a, X))

print(f"{'case':22s} {'count':>9s}")
for k in sorted(tot):
    print(f"{k:22s} {tot[k]:9d}")
for k, e in sorted(ex.items()):
    print(f"  ex {k}: {e}")
