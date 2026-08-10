"""Does the `(WCONVEX)` induction close?  Measure the step fact.

`(WCONVEX)` (`Wtower2.WConvex`) is now the ONLY residue on the (WL) side:

    A in W a -> C in W a -> A <=1 B -> B <=1 C  ==>  B in W a

The natural proof inducts on `C`'s `W`-derivation.  In the clause-2 case one
has `hop : forall n >= 1, C[n] in S`, and wants `B in W a`, i.e. by clause 2
`forall n >= 1, B[n] in W a`.  Applying the induction hypothesis at `C[n'']`
needs witnesses on both sides, so the whole induction rests on:

  (WCONV-STEP)  A <=1 B <=1 C  ==>  forall n exists n' n'',
                A[n'] <=1 B[n] <=1 C[n'']

`A[n']` is in `W a` for free (`oper_mem_of_mem`), so nothing else is needed.

Two questions, measured separately:

  (M)  the MONOTONE form, n' = n'' = n:   A[n] <=1 B[n] <=1 C[n]
  (E)  the EXISTENTIAL form: some n', n'' in a search window work

`Le1` demands EQUAL LENGTH, so (M) is a strong claim: lowering row 1 changes
branch data (it can CREATE a parent, which is exactly what killed the naive
`(ROW1MONO)` induction), and then `oper` produces a different length.  The
point of this probe is to find out whether the SANDWICH context rescues it --
i.e. whether having C above B constrains B enough.
"""
import sys
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio
from probe_sandwich import le1_cmp, lift1, shiftr1


def le1_ok(A, B):
    return le1_cmp(A, B) == 'ok'


def lower_row1(S, mask, amt):
    """Lower row 1 by `amt` on the columns in `mask` (clamped at 0)."""
    return [(x, (b - amt if j in mask else b), z) if j in mask and b >= amt
            else (x, b, z) for j, (x, b, z) in enumerate(S)]


def gen_chain(rng):
    """Generate A <=1 B <=1 C by starting from C and lowering twice."""
    L = rng.randint(2, 7)
    C = [(rng.randint(0, 4), rng.randint(0, 5), rng.randint(0, 1))
         for _ in range(L)]
    idx = list(range(L))
    m1 = set(rng.sample(idx, rng.randint(0, L)))
    B = lower_row1(C, m1, rng.randint(1, 3))
    m2 = set(rng.sample(idx, rng.randint(0, L)))
    A = lower_row1(B, m2, rng.randint(1, 3))
    return A, B, C


def gen_chain_sandwich(rng):
    """The chain the (WL) induction actually produces:
    A = Lift1(X,d) with the cone-lift, B = something in between,
    C = shiftr01 0 d X."""
    L = rng.randint(2, 7)
    X = [(rng.randint(0, 4), rng.randint(0, 4), rng.randint(0, 1))
         for _ in range(L)]
    d = rng.randint(1, 3)
    A = lift1(X, d)
    C = shiftr1(X, d)
    # B: raise row 1 of A towards C on a random subset
    idx = list(range(L))
    m = set(rng.sample(idx, rng.randint(0, L)))
    B = [(x, (min(b + d, C[j][1]) if j in m else b), z)
         for j, (x, b, z) in enumerate(A)]
    return A, B, C


def main(gen, label, trials=200000, seed=31337, window=6):
    rng = random.Random(seed)
    mono = Counter()
    exist = Counter()
    mono_ex, exist_ex = [], []
    for _ in range(trials):
        A, B, C = gen(rng)
        if not (le1_ok(A, B) and le1_ok(B, C)):
            mono['SKIP: generator broke the chain'] += 1
            continue
        for n in (1, 2, 3):
            An, Bn, Cn = trio.expand(A, n), trio.expand(B, n), trio.expand(C, n)
            lo = le1_cmp(An, Bn)
            hi = le1_cmp(Bn, Cn)
            mono['total'] += 1
            mono[f'lower:{lo}'] += 1
            mono[f'upper:{hi}'] += 1
            if lo == 'ok' and hi == 'ok':
                mono['BOTH ok'] += 1
            elif len(mono_ex) < 5:
                mono_ex.append((A, B, C, n, lo, hi, An, Bn, Cn))

            # existential form: search a window of n', n''
            okl = any(le1_ok(trio.expand(A, m), Bn) for m in range(1, window + 1))
            oku = any(le1_ok(Bn, trio.expand(C, m)) for m in range(1, window + 1))
            exist['total'] += 1
            exist['lower found'] += okl
            exist['upper found'] += oku
            if okl and oku:
                exist['BOTH found'] += 1
            elif len(exist_ex) < 5:
                exist_ex.append((A, B, C, n, okl, oku))

    print(f'\n########## {label} ##########')
    print('--- (M) monotone form  A[n] <=1 B[n] <=1 C[n]')
    for k in sorted(mono):
        print(f'  {k:34s} {mono[k]:9d}')
    print(f'--- (E) existential form (n\', n\'\' searched in 1..{window})')
    for k in sorted(exist):
        print(f'  {k:34s} {exist[k]:9d}')
    for S, ex in (('M', mono_ex), ('E', exist_ex)):
        if not ex:
            continue
        print(f'--- {S} counterexamples')
        for row in ex:
            if S == 'M':
                A, B, C, n, lo, hi, An, Bn, Cn = row
                print(f'  n={n} lower={lo} upper={hi}')
                print(f'    A={A}\n    B={B}\n    C={C}')
                print(f'    A[n]={An}\n    B[n]={Bn}\n    C[n]={Cn}')
            else:
                A, B, C, n, okl, oku = row
                print(f'  n={n} lower_found={okl} upper_found={oku}')
                print(f'    A={A}\n    B={B}\n    C={C}')


if __name__ == '__main__':
    main(gen_chain, 'GENERIC chains (A <=1 B <=1 C by random lowering)')
    main(gen_chain_sandwich, 'SANDWICH-SHAPED chains (Lift1 <=1 B <=1 shiftr01)')
