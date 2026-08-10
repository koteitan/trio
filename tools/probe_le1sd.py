"""Is `Le1sd` the relation that closes the `(WL)` induction?

`probe_le1s.py` found that `Le1` + equal branch data + ORDERED MIRROR DELTA

    Le1sd A B  :=  Le1 A B
                   AND  branch_data A = branch_data B
                   AND  D1_A <= D1_B          (D1 = row-1 mirror delta)

survived 1012280 instances with 0 violations, while dropping the delta clause
costs 1977 violations (all `row1`, all with D1_A > D1_B) and dropping the
branch clause reintroduces the length failures that killed everything before.

Two things must ALSO hold for `Le1sd` to be useful, and neither was measured:

  (A) the (WL) instance satisfies it:
          Le1sd (Lift1 X d) (shiftr01 0 d X)
      -- otherwise the whole relation is irrelevant to the goal.  This is the
      one in doubt: D1 of `shiftr01 0 d X` is D1_X (both endpoints shift by d),
      but D1 of `Lift1 X d` is D1_X + d when the last column is in the root's
      row-1 cone and its row-2 parent is NOT.

  (B) it CHAINS, i.e. `Le1sd` is `oper`-monotone including the delta clause:
          Le1sd A B  ->  Le1sd (A[n]) (B[n])
      -- otherwise the A2' induction cannot recurse.

If both hold, `(ROW1MONO-S)` (downward closure along `Le1sd`) closes by A2' on
M with no convexity, and `(WL)` follows outright.
"""
import sys
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio
from probe_sandwich import le1_cmp, lift1, shiftr1, srow, based_strict
from probe_le1s import branch_data, mirror_delta, le1s


def le1sd_why(A, B):
    r = le1_cmp(A, B)
    if r != 'ok':
        return r
    if branch_data(A) != branch_data(B):
        return 'branch'
    dA, dB = mirror_delta(A), mirror_delta(B)
    if dA is not None and dB is not None and dA > dB:
        return 'delta'
    return 'ok'


def part_A(trials=200000, seed=777):
    """Does the (WL) instance satisfy Le1sd?"""
    rng = random.Random(seed)
    out = Counter()
    ex = []
    for _ in range(trials):
        L = rng.randint(1, 7)
        X = [(rng.randint(0, 4), rng.randint(0, 4), rng.randint(0, 1))
             for _ in range(L)]
        tag = 'based' if based_strict(X) else 'free'
        for d in (1, 2, 3):
            A, B = lift1(X, d), shiftr1(X, d)
            r = le1sd_why(A, B)
            out['total'] += 1
            out[f'{tag}:{r}'] += 1
            if r != 'ok' and len(ex) < 6:
                ex.append((X, d, r, A, B, mirror_delta(A), mirror_delta(B)))
    print('=== (A) Le1sd (Lift1 X d) (shiftr01 0 d X) ===')
    for k in sorted(out):
        print(f'  {k:20s} {out[k]:9d}')
    for X, d, r, A, B, dA, dB in ex:
        print(f'  why={r} d={d} D1_A={dA} D1_B={dB}')
        print(f'    X={X}\n    A={A}\n    B={B}')
    return out


def part_B(trials=300000, seed=888):
    """Does Le1sd chain through oper?"""
    rng = random.Random(seed)
    out = Counter()
    ex = []
    for _ in range(trials):
        L = rng.randint(2, 7)
        B = [(rng.randint(0, 4), rng.randint(0, 5), rng.randint(0, 1))
             for _ in range(L)]
        mask = set(rng.sample(range(L), rng.randint(1, L)))
        amt = rng.randint(1, 3)
        A = [(x, (b - amt if b >= amt else b), z) if j in mask else (x, b, z)
             for j, (x, b, z) in enumerate(B)]
        if le1sd_why(A, B) != 'ok':
            out['skipped: premise fails'] += 1
            continue
        for n in (1, 2, 3, 4):
            An, Bn = trio.expand(A, n), trio.expand(B, n)
            r = le1sd_why(An, Bn)
            out['total'] += 1
            out[r] += 1
            if r != 'ok' and len(ex) < 6:
                ex.append((A, B, n, r, An, Bn,
                           mirror_delta(An), mirror_delta(Bn)))
    print('\n=== (B) Le1sd A B  =>  Le1sd (A[n]) (B[n]) ===')
    for k in sorted(out):
        print(f'  {k:24s} {out[k]:9d}')
    for A, B, n, r, An, Bn, dA, dB in ex:
        print(f'  n={n} why={r} D1_A[n]={dA} D1_B[n]={dB}')
        print(f'    A   ={A}\n    B   ={B}')
        print(f'    A[n]={An}\n    B[n]={Bn}')
    return out


if __name__ == '__main__':
    part_A()
    part_B()
