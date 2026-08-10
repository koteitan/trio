"""Is the recorded (ROW1MONO) "sandwich" actually true?

Memory / PROOF-STATUS record the hint

    Lift1 (X[n]) d  <=1  (Lift1 X d)[n]  <=1  shiftr01 0 d (X[n])

as the shape the (WL) induction would need, with the two ends already known to
sit in `W`.  That was a HINT, never measured.  `Le1` (as now defined in Lean,
`Wtower2.Le1`) demands EQUAL LENGTH, and neither `Lift1` nor `shiftr01`
commutes with `oper` unconditionally, so the lengths are exactly what is in
doubt:

  * `Lift1` provably fails to commute with `oper` when the bad root sits at
    column 0 (measured: 47718/99765) -- each copy grows its own index cone;
  * `shiftr01 0 d` commutes only when the last column has `srow >= 1`
    (`Wslift.oper_shiftr1`).

This probe measures, over based blocks and every `d >= 1`, `n >= 1`:

  LEFT   Le1( Lift1(expand(S,n), d), expand(Lift1(S,d), n) )
  RIGHT  Le1( expand(Lift1(S,d), n), shiftr01(expand(S,n), d) )

separately reporting length mismatches from row-1 order violations, and
splitting by the bad-root column `j0` (0 vs >= 1), since that is the known
fault line.  A length mismatch kills the `Le1` form of the sandwich outright;
a row-1 violation with matching lengths kills it mathematically.
"""
import sys
import itertools
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio


def cone_le1(S):
    """{j | le1 S 0 j} -- the row-1 descendant cone of column 0."""
    return {j for j in range(len(S)) if trio.is_ancestor(S, 1, 0, j)}


def lift1(S, d):
    c = cone_le1(S)
    return [(x, b + (d if j in c else 0), z) for j, (x, b, z) in enumerate(S)]


def shiftr1(S, d):
    return [(x, b + d, z) for (x, b, z) in S]


def srow(col):
    x, b, z = col
    if z != 0:
        return 2
    if b != 0:
        return 1
    return 0


def bad_root(S):
    """Column index of the bad root of the last column, or None."""
    if len(S) < 2:
        return None
    y = srow(S[-1])
    if y == 0:
        return None
    return trio.parent(S, y, len(S) - 1)


def le1_cmp(A, B):
    """Return 'ok' | 'len' | 'row0' | 'row2' | 'row1'."""
    if len(A) != len(B):
        return 'len'
    for (xa, ba, za), (xb, bb, zb) in zip(A, B):
        if xa != xb:
            return 'row0'
        if za != zb:
            return 'row2'
    for (_, ba, _), (_, bb, _) in zip(A, B):
        if ba > bb:
            return 'row1'
    return 'ok'


def based_strict(S):
    return len(S) >= 1 and all(S[0][0] < S[j][0] for j in range(1, len(S)))


def population(seed=4242, nrand=40000):
    rng = random.Random(seed)
    pop = []
    COLS = [(x, b, z) for x in range(3) for b in range(3) for z in range(2)]
    for L in (2, 3):
        for S in itertools.product(COLS, repeat=L):
            S = list(S)
            if S[0][0] != 0:
                continue
            if not based_strict(S):
                continue
            pop.append(S)
    for _ in range(nrand):
        L = rng.randint(3, 7)
        S = [(0, rng.randint(0, 4), rng.randint(0, 1))]
        for _ in range(L - 1):
            S.append((rng.randint(1, 6), rng.randint(0, 4), rng.randint(0, 1)))
        if based_strict(S):
            pop.append(S)
    return pop


def population_adv(seed=99181, nrand=60000):
    """Stress the known fault lines: row-2 collapse at the last column
    (`srow = 2`, the trio-specific case), a bad root at column 0, row-1 TIES
    (the exact gap between the index cone and the value cone), and deep stacks."""
    rng = random.Random(seed)
    pop = []
    for _ in range(nrand):
        L = rng.randint(3, 9)
        # small row-1 alphabet => many ties; z biased to 1 => srow = 2 endings
        v0 = rng.randint(0, 2)
        S = [(0, v0, rng.choice([0, 1, 1]))]
        for _ in range(L - 1):
            S.append((rng.randint(1, 4), rng.choice([v0, v0, v0 + 1, rng.randint(0, 3)]),
                      rng.choice([0, 1, 1])))
        if not based_strict(S):
            continue
        # keep the interesting ones: last column must actually collapse
        if srow(S[-1]) == 0:
            continue
        pop.append(S)
    return pop


def run(pop, label, ds, ns):
    print(f'\n########## {label}: population {len(pop)} ##########', flush=True)
    L = Counter()
    R = Counter()
    Lex, Rex = [], []
    for S in pop:
        j0 = bad_root(S)
        tag = 'j0=0' if j0 == 0 else ('j0>=1' if j0 is not None else 'noroot')
        for d in ds:
            Sd = lift1(S, d)
            for n in ns:
                mid = trio.expand(Sd, n)
                left = lift1(trio.expand(S, n), d)
                right = shiftr1(trio.expand(S, n), d)
                rl = le1_cmp(left, mid)
                L['total'] += 1
                L[f'{tag}:{rl}'] += 1
                if rl != 'ok' and len(Lex) < 6:
                    Lex.append((S, d, n, rl, left, mid))
                rr = le1_cmp(mid, right)
                R['total'] += 1
                R[f'{tag}:{rr}'] += 1
                if rr != 'ok' and len(Rex) < 6:
                    Rex.append((S, d, n, rr, mid, right))
    print('=== LEFT   Le1( Lift1(X[n],d), (Lift1 X d)[n] ) ===')
    for k in sorted(L):
        print(f'  {k:16s} {L[k]:9d}')
    print('=== RIGHT  Le1( (Lift1 X d)[n], shiftr01 0 d (X[n]) ) ===')
    for k in sorted(R):
        print(f'  {k:16s} {R[k]:9d}')
    for name, ex in (('LEFT', Lex), ('RIGHT', Rex)):
        if not ex:
            continue
        print(f'--- {name} counterexamples')
        for S, d, n, why, A, B in ex:
            print(f'  why={why} d={d} n={n}')
            print(f'    S ={S}')
            print(f'    A ={A}')
            print(f'    B ={B}')
    return L, R


def main():
    run(population(), 'BASE', (1, 2, 3), (1, 2, 3))
    run(population_adv(), 'ADVERSARIAL (srow=2 endings, ties, deep)',
        (1, 2, 5), (1, 2, 3, 4, 5))
    return


def main_old():
    pop = population()
    print('population:', len(pop), flush=True)
    L = Counter()
    R = Counter()
    Lex, Rex = [], []
    for S in pop:
        j0 = bad_root(S)
        tag = 'j0=0' if j0 == 0 else ('j0>=1' if j0 is not None else 'noroot')
        Sd = lift1(S, 1)
        for d in (1, 2, 3):
            if d != 1:
                Sd = lift1(S, d)
            for n in (1, 2, 3):
                mid = trio.expand(Sd, n)
                left = lift1(trio.expand(S, n), d)
                right = shiftr1(trio.expand(S, n), d)

                rl = le1_cmp(left, mid)
                L['total'] += 1
                L[f'{tag}:{rl}'] += 1
                if rl != 'ok' and len(Lex) < 6:
                    Lex.append((S, d, n, rl, left, mid))

                rr = le1_cmp(mid, right)
                R['total'] += 1
                R[f'{tag}:{rr}'] += 1
                if rr != 'ok' and len(Rex) < 6:
                    Rex.append((S, d, n, rr, mid, right))

    print('\n=== LEFT   Le1( Lift1(X[n],d), (Lift1 X d)[n] ) ===')
    for k in sorted(L):
        print(f'  {k:16s} {L[k]:9d}')
    print('\n=== RIGHT  Le1( (Lift1 X d)[n], shiftr01 0 d (X[n]) ) ===')
    for k in sorted(R):
        print(f'  {k:16s} {R[k]:9d}')

    for name, ex in (('LEFT', Lex), ('RIGHT', Rex)):
        print(f'\n--- {name} counterexamples')
        for S, d, n, why, A, B in ex:
            print(f'  why={why} d={d} n={n}')
            print(f'    S ={S}')
            print(f'    A ={A}')
            print(f'    B ={B}')


if __name__ == '__main__':
    main()
