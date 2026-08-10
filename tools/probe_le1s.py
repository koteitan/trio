"""Does adding BRANCH-DATA EQUALITY to `Le1` make the `oper` induction close?

`probe_wconvex_step.py` refuted both the monotone and the existential form of
the `(WCONVEX)` step, and every counterexample was a LENGTH mismatch: moving
row 1 creates or destroys a parent, so the two expansions have different
shapes.  In the sandwich

    Lift1 (X[n]) d  <=1  (Lift1 X d)[n]  <=1  shiftr01 0 d (X[n])

that never happens, because all three come from the SAME X by cone-lifts and
`Lift1` / `shiftr01` both PRESERVE the branch data (`nextrel*`, `le0`, `le1`,
`hasParent`, `parent`, `srow`).

So the right restriction is not "lower row 1" but "lower row 1 WITHOUT changing
the tree":

    Le1s A B  :=  Le1 A B  AND  A and B have identical branch data

If `Le1s` is `oper`-monotone -- `Le1s A B -> Le1s (A[n]) (B[n])` -- then the
downward-closure induction CLOSES outright:

    (ROW1MONO-S)  M in W a -> Le1s M' M -> M' in W a

by A2' on M: clause 2 gives `M[n] in S`, monotonicity gives
`Le1s (M'[n]) (M[n])`, so `M'[n] in W a`, so `M' in W a` by
`mem_of_oper_mem`.  No convexity needed, and `(WL)` follows because
`Lift1 X d` and `shiftr01 0 d X` have the SAME branch data as `X`.

CAVEAT this probe exists to test: the mirror delta

    D1 = entry S 1 j1 - entry S 1 j0        (j1 = last column, j0 = bad root)

is NOT determined by `Le1`.  With row 1 of A = (0,5) and of B = (3,5) we get
D1_A = 5 > D1_B = 2, so after k copies A's row 1 can OVERTAKE B's even though
the trees agree.  Hence two variants are measured:

  (S)   Le1s alone
  (SD)  Le1s AND D1_A <= D1_B  (the mirror delta is ordered too)
"""
import sys
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio
from probe_sandwich import le1_cmp, lift1, shiftr1, srow


def branch_data(S):
    """Everything `oper` looks at: srow of every column, and the parent of
    every (row, column) pair."""
    n = len(S)
    return (tuple(srow(c) for c in S),
            tuple(trio.parent(S, i, j) for i in range(3) for j in range(n)))


def le1s(A, B):
    return le1_cmp(A, B) == 'ok' and branch_data(A) == branch_data(B)


def mirror_delta(S):
    """D1 for the expansion of S, or None when there is no bad root."""
    if len(S) < 2:
        return None
    j1 = len(S) - 1
    i1 = srow(S[j1])
    if i1 == 0:
        return None
    j0 = trio.parent(S, i1, j1)
    if j0 is None:
        return None
    if i1 > 1:
        return S[j1][1] - S[j0][1]
    return 0


def lower_row1(S, mask, amt):
    return [(x, (b - amt if b >= amt else b), z) if j in mask else (x, b, z)
            for j, (x, b, z) in enumerate(S)]


def main(trials=400000, seed=515151):
    rng = random.Random(seed)
    S = Counter()
    SD = Counter()
    Sex, SDex = [], []
    for _ in range(trials):
        L = rng.randint(2, 7)
        B = [(rng.randint(0, 4), rng.randint(0, 5), rng.randint(0, 1))
             for _ in range(L)]
        mask = set(rng.sample(range(L), rng.randint(1, L)))
        A = lower_row1(B, mask, rng.randint(1, 3))
        if not le1s(A, B):
            S['skipped: not Le1s'] += 1
            continue
        dA, dB = mirror_delta(A), mirror_delta(B)
        delta_ok = (dA is None or dB is None or dA <= dB)
        for n in (1, 2, 3, 4):
            An, Bn = trio.expand(A, n), trio.expand(B, n)
            r = 'ok' if le1s(An, Bn) else le1_cmp(An, Bn)
            if r == 'ok' and not le1s(An, Bn):
                r = 'branch'
            S['total'] += 1
            S[r] += 1
            if r != 'ok' and len(Sex) < 6:
                Sex.append((A, B, n, r, An, Bn))
            if delta_ok:
                SD['total'] += 1
                SD[r] += 1
                if r != 'ok' and len(SDex) < 6:
                    SDex.append((A, B, n, r, An, Bn, dA, dB))

    print('--- (S)  Le1s alone:  Le1s A B  =>  Le1s (A[n]) (B[n])')
    for k in sorted(S):
        print(f'  {k:24s} {S[k]:9d}')
    print('--- (SD) Le1s AND the mirror delta ordered (D1_A <= D1_B)')
    for k in sorted(SD):
        print(f'  {k:24s} {SD[k]:9d}')
    for tag, ex in (('S', Sex), ('SD', SDex)):
        if not ex:
            continue
        print(f'--- {tag} counterexamples')
        for row in ex:
            A, B, n, r, An, Bn = row[:6]
            extra = f'  D1_A={row[6]} D1_B={row[7]}' if len(row) > 6 else ''
            print(f'  n={n} why={r}{extra}')
            print(f'    A   ={A}\n    B   ={B}')
            print(f'    A[n]={An}\n    B[n]={Bn}')


if __name__ == '__main__':
    main()
