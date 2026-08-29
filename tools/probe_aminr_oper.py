"""L88: is `aminR` (the ROOT-EXCLUDED row-0 ancestor row-1 minimum) invariant
under `oper` on the copy columns, the way `amin` is (`Aexp.amin_oper_mir`)?

`Lift1 X d`'s mask is the `le1`-cone of the root, which equals
`{j | aminR X j > v0}` (`L53.coneVR_iff_aminR` + `Lcone.le1_zero_iff`).  The
proved lift machinery (`slift` / `mlift`) is indexed by `amin`, and `amin` is
capped by the root (`amin X j <= v0` always), so no `amin` threshold reaches the
cone (`L53.coneV_root_vacuous`).  The one thing that would carry the whole
`slift` machine over to `aminR` is the (A2) analogue:

    aminR (M[n]) (j0 + (k*Lb + q))  ==  aminR M (j0 + q)      for k < n, q < Lb

**POSITIVE CONTROL**: the same measurement with `amin` must be 100% (that is
`amin_oper_mir`, PROVED).  If the control ever fires, the instrument is wrong.

Split by `j0 == 0` (bad root IS the root, so `take j0 = []` and every copy
carries an image of the root) vs `j0 > 0`.
"""
import sys
import itertools
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

INF = 10**9


def anc0(S, j):
    out, x = [], j
    while x is not None:
        out.append(x)
        x = trio.parent(S, 0, x)
    return out


def amin(S, j):
    return min(S[y][1] for y in anc0(S, j))


def aminR(S, j):
    vals = [S[y][1] for y in anc0(S, j) if y != 0]
    return min(vals) if vals else INF


def srow(S, j):
    if S[j][2] > 0:
        return 2
    if S[j][1] > 0:
        return 1
    return 0


def based_strict(S):
    return S[0][0] == 0 and all(S[0][0] < S[j][0] for j in range(1, len(S)))


def main():
    rng = random.Random(88088)
    pop = []
    COLS = [(x, b, z) for x in range(4) for b in range(4) for z in range(2)]
    for L in (2, 3):
        for S in itertools.product(COLS, repeat=L):
            S = list(S)
            if based_strict(S):
                pop.append(S)
    for _ in range(60000):
        L = rng.randint(3, 7)
        S = [(0, rng.randint(0, 4), rng.randint(0, 1))]
        for _ in range(L - 1):
            S.append((rng.randint(1, 6), rng.randint(0, 4), rng.randint(0, 1)))
        if based_strict(S):
            pop.append(S)
    print('population:', len(pop), flush=True)

    tot = Counter()
    ex = []
    for S in pop:
        L = len(S)
        if L < 2:
            continue
        j1 = L - 1
        i1 = srow(S, j1)
        j0 = trio.parent(S, i1, j1)
        if j0 is None:
            tot['skip: orphan (no bad root)'] += 1
            continue
        Lb = j1 - j0
        if Lb <= 0:
            tot['skip: Lb <= 0'] += 1
            continue
        tag = 'j0==0' if j0 == 0 else 'j0>0'
        for n in (1, 2, 3):
            E = trio.expand(S, n)
            for k in range(n):
                for q in range(Lb):
                    idx = j0 + (k * Lb + q)
                    if idx >= len(E):
                        tot['skip: index out of range'] += 1
                        continue
                    if idx == 0 or j0 + q == 0:
                        # `aminR` is the empty min at the root itself
                        # (`coneVR_iff_aminR` needs `j != 0`); not a copy column.
                        tot['skip: root column (j = 0)'] += 1
                        continue
                    tot[f'{tag}: total'] += 1
                    # POSITIVE CONTROL — must never fire
                    if amin(E, idx) != amin(S, j0 + q):
                        tot[f'{tag}: !! CONTROL amin BROKE'] += 1
                    if aminR(E, idx) == aminR(S, j0 + q):
                        tot[f'{tag}:   aminR invariant'] += 1
                    else:
                        tot[f'{tag}:   aminR BROKEN'] += 1
                        if len(ex) < 8:
                            ex.append((S, n, j0, Lb, k, q, idx,
                                       aminR(S, j0 + q), aminR(E, idx)))
    for key in sorted(tot):
        print(f'  {key:34s} {tot[key]:9d}')
    print('--- aminR counterexamples:')
    for S, n, j0, Lb, k, q, idx, a, b in ex:
        print(f'  S={S} n={n} j0={j0} Lb={Lb} k={k} q={q} idx={idx} '
              f'aminR M={a} aminR M[n]={b}')


if __name__ == '__main__':
    main()
