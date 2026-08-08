"""Does `oper` commute with the root lift `Lift1` when the bad root is not 0?

The `(WL)` residue `LiftStageParented` splits into four branches
(`Wtower2.lean`, `liftStageParented_of_cases`); two are proved.  The branch
`1 <= badPar X` should be the *easy* one, because there the lifted cone
`le1 X 0 .` and the copy guard `le1 X j0 .` are cones of DIFFERENT roots, so
they ought not interfere.  Concretely the branch would follow from

    (C0)   badPar X >= 1  ->  (Lift1 X d)[n] = Lift1 (X[n]) d

and, unwinding the two sides column by column, (C0) is equivalent to the
**cone-from-0 transport**

    (T0)   le1 (X[n]) 0 (j0 + (k*Lb + q))  <->  le1 X 0 (j0 + q)      (k < n, q < Lb)

together with the already-proved head part `le1_gexp_low` (p < j0).

This script measures (C0) and (T0) separately, and — when (C0) fails — reports
which piece of the `oper` data (j1 / i1 / hasParent / j0 / d0 / d1 / guards)
diverged, so a counterexample immediately says which sub-lemma is false.

Population: everything reachable from the z<2 generators `diag(3, v, zcap=1)`
by `X |-> X[n]`, i.e. exactly `ST_TS`, plus their prefixes (the `Aop` clause-3
data are prefixes, and `LSPOn` is stated for arbitrary `X`, not only standard
forms).
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2, 3)
DS = (1, 2, 3)
MAXDEPTH = 6
MAXLEN = 30
VMAX = 4


def le1(S, r, j):
    return trio.is_ancestor(S, 1, r, j)


def lift1(S, d):
    return [(c[0], c[1] + (d if le1(S, 0, i) else 0), c[2])
            for i, c in enumerate(S)]


def operdata(S):
    """The branch data `oper` reads off `S`, or None when `oper` is Pred/id."""
    if len(S) < 2:
        return None
    x = len(S) - 1
    if all(v == 0 for v in S[x]):
        return None
    t = max(y for y in range(3) if S[x][y] > 0)
    r = trio.parent(S, t, x)
    if r is None:
        return None
    d0 = S[x][0] - S[r][0] if 0 < t else 0
    d1 = S[x][1] - S[r][1] if 1 < t else 0
    g0 = tuple(trio.is_ancestor(S, 0, r, j) for j in range(r, x))
    g1 = tuple(le1(S, r, j) for j in range(r, x))
    return dict(j1=x, i1=t, j0=r, d0=d0, d1=d1, g0=g0, g1=g1)


def gen_population():
    seen = {}
    frontier = []
    for v in range(VMAX + 1):
        S = tuple(trio.diag(3, v, zcap=1))
        seen[S] = 0
        frontier.append((S, 0))
    while frontier:
        S, dep = frontier.pop()
        if dep >= MAXDEPTH:
            continue
        for n in NS:
            T = tuple(trio.expand(list(S), n))
            if not T or len(T) > MAXLEN:
                continue
            if T not in seen:
                seen[T] = dep + 1
                frontier.append((T, dep + 1))
    # prefixes too
    out = set(seen)
    for S in list(seen):
        for k in range(1, len(S)):
            out.add(S[:k])
    return sorted(out, key=lambda s: (len(s), s))


def main():
    pop = gen_population()
    stats = Counter()
    cex_c0 = []
    cex_t0 = []
    for S in pop:
        od = operdata(list(S))
        if od is None or od['j0'] < 1:
            continue
        stats['hosts'] += 1
        j0, j1 = od['j0'], od['j1']
        Lb = j1 - j0
        if Lb == 0:
            continue
        for d in DS:
            L = lift1(list(S), d)
            odL = operdata(L)
            for n in NS:
                stats['inst'] += 1
                lhs = trio.expand(L, n)
                rhs = lift1(trio.expand(list(S), n), d)
                if lhs != rhs:
                    stats['C0-viol'] += 1
                    if len(cex_c0) < 5:
                        which = []
                        if odL is None:
                            which.append('branch')
                        else:
                            for key in ('j1', 'i1', 'j0', 'd0', 'd1', 'g0', 'g1'):
                                if odL[key] != od[key]:
                                    which.append(key)
                        cex_c0.append((S, d, n, tuple(which)))
                # (T0) on the unlifted side
                G = trio.expand(list(S), n)
                for k in range(n):
                    for q in range(Lb):
                        p = j0 + k * Lb + q
                        if p >= len(G):
                            continue
                        a = le1(G, 0, p)
                        b = le1(list(S), 0, j0 + q)
                        stats['T0-inst'] += 1
                        if a != b:
                            stats['T0-viol'] += 1
                            if len(cex_t0) < 5:
                                cex_t0.append((S, n, k, q, a, b))
    print('population          :', len(pop))
    print('hosts (badPar >= 1) :', stats['hosts'])
    print('(C0) instances      :', stats['inst'])
    print('(C0) violations     :', stats['C0-viol'])
    print('(T0) instances      :', stats['T0-inst'])
    print('(T0) violations     :', stats['T0-viol'])
    if cex_c0:
        print('\n--- (C0) counterexamples (divergent oper data) ---')
        for S, d, n, which in cex_c0:
            print(f'  X={list(S)} d={d} n={n} diverged={which}')
    if cex_t0:
        print('\n--- (T0) counterexamples ---')
        for S, n, k, q, a, b in cex_t0:
            print(f'  X={list(S)} n={n} k={k} q={q}: le1(G,0,p)={a} le1(X,0,j0+q)={b}')


if __name__ == '__main__':
    main()
