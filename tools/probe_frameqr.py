"""Measure AbsDQR and TPLoQR (Ytosk/lean/Ytosk/V3FrameV2.lean) on the ten sets.

Both are statements about the last-column frame: x = |M| - 1, P_1(x) = P_0(x) = r,
row 2 of x is 0, o(r) = psi_mu(b + Omega_{mu+1}), mu != 0.
- AbsDQR: D v-call i < x, row 1 and row 2 of i nonzero, W = bumpW(i) has a hole and
  cof W = omega: every summand q of v(P_1 i) with q < W has q < fsD(W, etaOm mu).
- TPLoQR: D o-call c < x, o(c) = psi_s(y), y != b + Omega_{mu+1},
  split(y, Omega_{s+1}).2 = 0, last y = psi_a(0), a not successor, OHole a,
  cof a = omega: not Omega_{fsD(a, etaOm mu)} < Omega_{s+1}.
DepX is the least closure of its six constructors (probe_inv2.dependencies).
Only matrices strictly below SRO are measured. Run with nice -n 15, at most 4 workers.
"""
from collections import Counter

from probe_inv2 import SRO, dependencies, main
from probe_inv3_prefix import (
    Ctx, Z, app, cof, etaOm, fsD, init, isSucc, last, lt, ohole, split, succ, summ,
)


def measure(matrix):
    """AbsDQR / TPLoQR at the last-column frame (q = r, mu != 0)."""
    M = list(matrix)
    counts = Counter(input=1)
    examples = {}
    if not M < SRO:
        counts['outside_SRO'] += 1
        return counts, examples
    C = Ctx(M)
    if not C.ok:
        counts['eval_failed'] += 1
        examples['eval_failed'] = {'matrix': M}
        return counts, examples
    counts['measured'] += 1
    x = len(M) - 1
    if x < 1 or M[x][1] == 0 or M[x][2] != 0:
        return counts, examples
    r, q = C.e.par(1, x), C.e.par(0, x)
    if r is None or q != r:
        return counts, examples
    mu, br, rest = C.o(r)
    if rest != Z or not br or last(br) != (succ(mu), Z, Z) or mu == Z:
        return counts, examples
    counts['frames'] += 1
    eta = etaOm(mu)
    D = dependencies(C, x)

    def note(field, ok, **info):
        counts[field + '.cases'] += 1
        if not ok:
            counts[field + '.failures'] += 1
            examples.setdefault(field, {'matrix': M, **info})

    for i in range(x):
        if (False, i) in D and M[i][1] != 0 and M[i][2] != 0:
            W = C.bumpW(i)
            if ohole(W) and cof(W)[0] == 'omega':
                F = fsD(W, eta)
                for t in summ(C.vOpt1(i)):
                    if lt(t, W):
                        note('AbsDQR', lt(t, F), i=i, summand=t)
        if (True, i) in D:
            s, y, _ = C.o(i)
            if y == br or split(y, (succ(s), Z, Z))[1] != Z:
                continue
            l = last(y)
            if not l or l[1] != Z:
                continue
            a = l[0]
            if not isSucc(a) and ohole(a) and cof(a)[0] == 'omega':
                note('TPLoQR', not lt((fsD(a, eta), Z, Z), (succ(s), Z, Z)), c=i)
    return counts, examples


if __name__ == '__main__':
    main(measure, fields=('AbsDQR', 'TPLoQR'),
         case_unit='AbsDQR summand, TPLoQR column',
         definitions=('V3FrameV2.lean',))
