"""(DIAG) — the `|R| = 1` case of `TowerExp2Root`, where the pair theorem lives.

`TowerExp2Root` is the last open statement besides `(CAT)`:

    argOK R -> R /= [] -> z <= 1 -> domT R m ->
    (forall n >= 1, R[n] in Wstar) -> srow R (|R|-1) = 2 ->
    hasParent ((0,v,z) :: R) 2 |R| -> v < w -> z < y ->
    forall n >= 1, ((0,v,z) :: R)[n] in W (2v+z)

For `|R| = 1`, i.e. `M = [(0,v,z), (e,w,y)]`, the expansion is EXACTLY (checked
against `trio.expand` below):

    M[n] = [(k*e, v + k*(w-v), z)]_{k<n}

— a diagonal whose row 2 is the ROOT's `z`, not the orphan's `y`.  So the base
case of the residue is

    (DIAG)  0 < e -> 0 < f -> z <= 1 ->
            [(k*e, v + k*f, z)]_{k<n}  in  W (2v+z)

and it splits cleanly:

  * `z = 1`: every column has row 2 = 1, so no column has a row-2 ancestor with
    a smaller row 2 — every column is an orphan and `oper` is just `Pred`.  The
    sequence shrinks to `[(0,v,1)]`, whose level `2v+1` equals the target stage.
    TRIVIAL.
  * `z = 0`: a genuine PAIR sequence, and `[(k*e, k*f, 0)] in W 0` (take v = 0)
    is exactly pair-sequence termination — the whole lean-yapss theorem.

So the pair theorem is provably ON THE CRITICAL PATH of the trio proof, and it
enters through this single base case.
"""
import sys
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXDEPTH = 11
MAXLEN = 42


def lev(c):
    return 2 * c[1] + c[2]


def inW(S, a, d, memo):
    S = tuple(tuple(c) for c in S)
    key = (S, a)
    if key in memo:
        return memo[key]
    if len(S) == 0:
        return True
    if len(S) == 1:
        r = lev(S[0]) <= a
        memo[key] = r
        return r
    if d <= 0 or len(S) > MAXLEN:
        return None
    memo[key] = None
    out = True
    for n in NS:
        r = inW(trio.expand(list(S), n), a, d - 1, memo)
        if r is False:
            memo[key] = False
            return False
        if r is None:
            out = None
    memo[key] = out
    return out


def main():
    # (1) the |R| = 1 expansion shape
    bad = 0
    for v in range(3):
        for z in range(2):
            for e in (1, 2, 3):
                for w in range(1, 5):
                    for y in range(z + 1, z + 3):
                        if w <= v:
                            continue
                        M = [(0, v, z), (e, w, y)]
                        for n in range(1, 6):
                            got = trio.expand(list(M), n)
                            want = [(k * e, v + k * (w - v), z) for k in range(n)]
                            if got != want:
                                bad += 1
                                if bad <= 3:
                                    print('  SHAPE MISMATCH', M, n, got, want)
    print('(1) |R|=1 expansion shape mismatches:', bad)

    # (2) (DIAG) itself
    memo = {}
    tot = Counter()
    ex = []
    for v in range(3):
        for z in range(2):
            for e in (1, 2):
                for f in (1, 2, 3):
                    for n in range(1, 7):
                        D = [(k * e, v + k * f, z) for k in range(n)]
                        r = inW(D, 2 * v + z, MAXDEPTH, memo)
                        tag = 'z=%d' % z
                        if r is True:
                            tot[tag + '/ok'] += 1
                        elif r is None:
                            tot[tag + '/undecided'] += 1
                        else:
                            tot[tag + '/FAIL'] += 1
                            if len(ex) < 5:
                                ex.append((v, z, e, f, n, D))
    print('(2) (DIAG):')
    for k in sorted(tot):
        print(f'    {k:16s} {tot[k]:6d}')
    for e_ in ex:
        print('    FAIL', e_)

    # (3) the z = 1 diagonal is a pure Pred chain
    D = [(k, 1 + k, 1) for k in range(5)]
    print('(3) z=1 chain: expand(D,2) == D.dropLast ?',
          trio.expand(list(D), 2) == D[:-1])


if __name__ == '__main__':
    main()
