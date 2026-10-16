"""Measure TrigS0 at precisely the zero-lift child frames used by qr_oloc.

Full scans of the supplied sets, four workers at most, no Lhd approximation.
The older, false TrigS is also counted so its failures remain visible.
"""
from collections import Counter
from math import inf

from probe_inv2 import SRO, dependencies, main
from probe_inv3_prefix import Ctx, Z, ONE, app, init, last, lt, succ, sumN


def lift_counts(C, x, A):
    """Nat.find of DepL with loQ/lbQ: least weighted dependency paths.

    Each of the six constructors is relaxed until a fixed point. Nonnegative
    weights give the least reachable count, with v preferred by dOf.
    """
    br = A[1]
    edges = []
    for i, col in enumerate(C.M):
        edges.append(((True, i), (False, i), 0))
        for idx, c in enumerate(C.ch(i)):
            if C.counted(i, c):
                lo = int(C.o(c) == A and lt(C.pre(i, C.ch(i)[:idx]), br)
                         and lt((C.v(i), Z, Z), A))
                edges.append(((True, i), (True, c), lo))
        if col[1] == 0:
            continue
        p = C.e.par(1, i)
        if p is not None:
            edges.append(((False, i), (False, p), 0))
        if col[2] == 0:
            k = C.upg(i)
            if k is not None:
                edges.append(((False, i), (False, k), 0))
        else:
            for idx, j in enumerate(C.ch(i)):
                if C.M[j] != C.e.bump(i):
                    continue
                for k in C.ch(j):
                    lb = 0
                    if C.ch(j) == [k] and C.o(k) == A:
                        prior = sumN([C.bumpTerm(i, jj) for jj in C.ch(i)[:idx]])
                        lb = 2 if prior == Z else 1
                    edges.append(((False, i), (True, k), lb))
    d = {(True, x): 0}
    while True:
        changed = False
        for target, source, weight in edges:
            candidate = d.get(source, inf) + weight
            if candidate < d.get(target, inf):
                d[target] = candidate
                changed = True
        if not changed:
            return {i: d.get((False, i), d.get((True, i), 0)) for i in range(len(C.M))}


def measure_trigS0(matrix):
    """Measure the repaired TrigS0 and retain the unrestricted TrigS failures."""
    M = list(matrix)
    cnt, examples = Counter(input=1), {}
    if not M < SRO:
        cnt['outside_SRO'] += 1
        return cnt, examples
    cnt['below_SRO'] += 1
    x = len(M) - 1
    if x < 1 or M[x][1] == 0 or M[x][2] != 0:
        return cnt, examples
    C = Ctx(M)
    if not C.ok:
        cnt['eval_failed'] += 1
        examples['eval_failed'] = {'matrix': M}
        return cnt, examples
    r, q = C.e.par(1, x), C.e.par(0, x)
    if r is None or q != r:
        return cnt, examples
    mu, br, _ = C.o(r)
    if not br or last(br) != (succ(mu), Z, Z):
        return cnt, examples
    T = Ctx(M[:x])
    if not T.ok:
        cnt['seed_eval_failed'] += 1
        examples['seed_eval_failed'] = {'matrix': M}
        return cnt, examples
    seed = T.o(r)
    if not lt(seed, (mu, ONE, Z)):
        return cnt, examples
    cnt['seed_frames'] += 1
    b = init(br)
    D = dependencies(C, x)
    lifts = None
    for i in range(x):
        if (True, i) not in D:
            continue
        ch = C.ch(i)
        for idx, c in enumerate(ch):
            if (True, c) not in D or not C.counted(i, c):
                continue
            s, y, _ = C.o(c)
            B = C.pre(i, ch[:idx])
            if y != br or not lt(B, y) or not lt((C.v(i), Z, Z), (s, y, Z)):
                continue
            if lifts is None:
                lifts = lift_counts(C, x, C.o(r))
            dc = lifts[c]
            ok = lt(B, app(b, seed))
            cnt['TrigS.cases'] += 1
            cnt['child_lifts.' + str(dc)] += 1
            if not ok:
                cnt['TrigS.failures'] += 1
                examples.setdefault('TrigS', {'matrix': M, 'i': i, 'c': c, 'dOf_c': dc})
            if dc == 0:
                cnt['TrigS0.cases'] += 1
                if not ok:
                    cnt['TrigS0.failures'] += 1
                    examples.setdefault('TrigS0', {'matrix': M, 'i': i, 'c': c, 'dOf_c': dc})
    return cnt, examples


if __name__ == '__main__':
    main(measure_trigS0, ('TrigS0', 'TrigS'), 'trigger frame',
         ('V3TrigSeed.lean', 'V3Inv2.lean', 'V3QRIdx.lean', 'V3QRDiag.lean'))
