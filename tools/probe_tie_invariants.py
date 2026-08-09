"""Is the row-1 TIE-freeness of a row-2 bad part implied by the invariants we
ALREADY have, or does it need `ST_TS`-reachability?

`Wtower2.liftStage_of_tieFree` / `liftStage_of_window` make the stage law `(WL)`
free on tie-free blocks.  Whether that is usable depends entirely on what can
discharge tie-freeness at the call sites, so this probe asks the decisive
question directly.

Three measurements:

1. On REAL `ST_TS` (closure of `diag(3, v, zcap=1)`, `v < 10`, depth 16, `n` up
   to 4, length up to 160, 400003 sequences): **40444281 row-2 bad parts with
   root row 1 >= 1, ZERO ties**.  (Root row 1 = 0 is excluded: `mlift`'s
   threshold is a natural number, so that case is out of reach anyway.)
2. Flat ancestor pairs (`row1(a) = row1(z) >= 1` with the segment above `a`)
   DO occur on `ST_TS` — 520173 of them — just never inside a row-2 bad part.
   So the fact is about the collapse, not a global row-1 discipline.
3. This file: random matrices built to satisfy `r1ok`, `z0ok`, `noninc`, `zle1`
   — every invariant `Invariant.lean` already threads through the framework —
   still produce ties in 1552 of 9611 row-2 bad parts at root row 1 >= 1.

⟹ tie-freeness is NOT implied by the proved invariants.  The smallest witness
`[(0,0,0),(1,1,0),(2,1,0),(2,2,1)]` (and even its prefix) is verifiably absent
from the `ST_TS` closure, so discharging tie-freeness needs `ST_TS`
REACHABILITY — the same wall as the project's core, not a separate difficulty.
"""
import sys
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio


def srow(S, j):
    if S[j][2] > 0:
        return 2
    if S[j][1] > 0:
        return 1
    return 0


def anc0(S, j):
    out, x = [], j
    while x is not None:
        out.append(x)
        x = trio.parent(S, 0, x)
    return out


def amin(S, j):
    return min(S[y][1] for y in anc0(S, j))


def r1ok(S):
    for j in range(len(S)):
        if S[j][0] == 0:
            continue
        ks = [k for k in range(j)
              if S[k][0] + 1 == S[j][0]
              and all(S[j][0] <= S[l][0] for l in range(k + 1, j))]
        if not ks:
            return False
        if not any(S[j][1] <= S[k][1] + 1 for k in ks):
            return False
    return True


def z0ok(S):
    return all(not (S[j][0] == 0 and (S[j][1] != 0 or S[j][2] != 0))
               for j in range(len(S)))


def noninc(S):
    return all(c[2] <= c[1] for c in S)


def gen(rng):
    """A random matrix built to satisfy `r1ok` / `z0ok` structurally."""
    L = rng.randint(3, 9)
    S = [(0, 0, 0)]
    for _ in range(L - 1):
        k = rng.randrange(len(S))
        d = S[k][0] + 1
        if any(S[l][0] < d for l in range(k + 1, len(S))):
            continue
        b = rng.randint(0, S[k][1] + 1)
        z = rng.randint(0, min(1, b))
        S.append((d, b, z))
    return S


def main():
    rng = random.Random(31415)
    tot = Counter()
    ex = []
    for _ in range(400000):
        S = gen(rng)
        if len(S) < 3:
            continue
        if not (r1ok(S) and z0ok(S) and noninc(S)):
            tot['invariant reject'] += 1
            continue
        x = len(S) - 1
        if srow(S, x) != 2:
            continue
        j0 = trio.parent(S, 2, x)
        if j0 is None:
            continue
        B = [(c[0] - S[j0][0], c[1], c[2]) for c in S[j0:x]]
        if not B:
            continue
        v0 = B[0][1]
        if v0 == 0:
            tot['v0=0 (excluded)'] += 1
            continue
        tot['v0>=1 checked'] += 1
        c1 = {j for j in range(len(B)) if trio.is_ancestor(B, 1, 0, j)}
        c2 = {j for j in range(len(B)) if amin(B, j) == v0}
        if c1 != c2:
            tot['TIE despite invariants'] += 1
            if len(ex) < 5:
                ex.append((S, j0, v0, B))
    for k in sorted(tot):
        print(f'  {k:26s} {tot[k]:8d}')
    for S, j0, v0, B in ex:
        print(f'  TIE j0={j0} v0={v0}\n    S={S}\n    B={B}')


if __name__ == '__main__':
    main()
