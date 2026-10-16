"""Measure the shared residuals HFrameV2 and HLeafV2 (Ytosk/lean/Ytosk/V3GlobV2.lean).

HFrameV2 = TakeFrameV2: AbsDS AbsUS TPLoS TPLoW AbsUWL AbsUW0 AbsDW TrigS0 TPLoN AbsDN.
AbsUS, TPLoS (probe_inv2) and TrigS0 (probe_trigs0) are already measured on the ten sets;
this script measures the other seven, and HLeafV2 = TP1LeafG and TP1WLeafG (V3TP1CutG).

Definitions, line by line:
- AbsDS (V3SeedFields): q != r frame, o(r) = psi_mu(b); D v-call i < x, rows 1, 2 of i nonzero,
  W = bumpW(i), OHole W, holeLev W = mu: summands q < W of v(P_1 i) have q < fsD(W, seed).
- AbsUWL (V3QRLocV): q = r frame, o(r) = psi_mu(b + Omega_{mu+1}); D v-call i < x, upg i = k,
  W = last v(k), OHole W, cof W = omega: q < W gives q < fsD(W, gamS mu b_r 1 (max 1 d_i)).
- AbsUW0 (V3QRFinal4): as AbsUWL with d_i = 0 and the index seed.
- TPLoW (V3QRKeep): q = r frame; D o-call c < x, o(c) = psi_s(y), y != b_r, split(y, Omega_{s+1}).2 = 0,
  last y = psi_a(0), a not successor, OHole a, cof a = omega:
  not Omega_{fsD(a, gamS mu b_r 1 (max 1 d_c))} < Omega_{s+1}.
- AbsDW (V3QRLocV): q = r frame; D v-call i < x, rows 1, 2 nonzero, OHole W, cof W = omega:
  q < W gives q < fsD(W, gamS mu b_r 1 (max 1 d_i)).
- TPLoN (V3QRFinal4): q = r frame; D o-call c < x with d_c = 0, as TPLoW plus NotNode a, index seed.
- AbsDN (V3QRFinal4): every column i, rows 1, 2 nonzero, OHole W, cof W = omega, NotNode W:
  q < W gives q < fsD(W, 1).
- TP1LeafG / TP1WLeafG: every counted-child frame with state B = stB != 0 that rewrites,
  low part 0, OHole y, leaf pairs of CPairG s B y (probe tp1g.py, checked against V3TP1CutG).
seed = o_{M.take x}(r) (evaluation of the prefix); d_i = dOf (probe_trigs0.lift_counts).
Only matrices strictly below SRO. Run with nice -n 15, at most 4 workers.
"""
from collections import Counter

from probe_inv2 import SRO, dependencies, main
from probe_trigs0 import lift_counts
from probe_inv3_prefix import (
    Ctx, Z, ONE, cof, fs, fsD, holelev, isSucc, last, lt, notNode, ohole, spa, split, succ,
    sumN, summ,
)

FIELDS = ('AbsDS', 'AbsUWL', 'AbsUW0', 'TPLoW', 'AbsDW', 'TPLoN', 'AbsDN', 'TP1LeafG',
          'TP1WLeafG.succ', 'TP1WLeafG.lim')


def gamS(mu, b, seed, k):
    t = seed
    for _ in range(k):
        t = (mu, fs(b, t), Z)
    return t


def hpair(t, x):
    out = []
    if not t or not x:
        return out
    if t[1] == Z and t[2] == Z and x[1] == Z and x[2] == Z:
        out.append((t[0], x[0]))
        if not isSucc(x[0]):
            out += hpair(t[0], x[0])
    if t[2] == Z and x[2] == Z and t[0] == x[0]:
        out += hpair(t[1], x[1])
    if t[0] == x[0] and t[1] == x[1]:
        out += hpair(t[2], x[2])
    return out


def cpair(B, h):
    out = []
    if not B or not h:
        return out
    if B[1] == Z and B[2] == Z and h[1] == Z and h[2] == Z:
        out.append((B[0], h[0]))
        if not isSucc(h[0]):
            out += hpair(B[0], h[0])
    if B[2] == Z and h[2] == Z and B[0] == h[0]:
        out += hpair(B[1], h[1])
    if B[0] == h[0] and B[1] == h[1]:
        out += cpair(B[2], h[2])
    return out


def measure(matrix):
    """The seven unmeasured frame fields of TakeFrameV2 and the two leaf conditions."""
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

    def note(field, ok, **info):
        counts[field + '.cases'] += 1
        if not ok:
            counts[field + '.failures'] += 1
            examples.setdefault(field, {'matrix': M, **info})

    def absorb(field, i, W, eta):
        F = fsD(W, eta)
        for t in summ(C.vOpt1(i)):
            if lt(t, W):
                note(field, lt(t, F), i=i, summand=t)

    # AbsDN and the leaves: every column.
    for i in range(len(M)):
        if C.e12(i):
            W = C.bumpW(i)
            if ohole(W) and cof(W)[0] == 'omega' and notNode(W):
                absorb('AbsDN', i, W, ONE)
        vi = C.v(i)
        cl = C.CL(i)
        for idx, c in enumerate(cl):
            B = spa(vi, sumN([C.o(d) for d in cl[:idx]]))
            s, y, _ = C.o(c)
            if B == Z or not (lt(B, y) and lt((vi, Z, Z), (s, y, Z))):
                continue
            if split(y, (succ(s), Z, Z))[1] != Z or not ohole(y):
                continue
            eta = (holelev(y), ONE, Z)
            w = cof(y)[0] == 'omega'
            for tp, k in cpair(B, y):
                if isSucc(k):
                    if w and lt(tp, k):
                        note('TP1WLeafG.succ', lt((tp, Z, Z), ONE), i=i, c=c, k=k)
                elif tp == s and ohole(k) and lt(s, k):
                    note('TP1LeafG', lt(s, fsD(k, eta)), i=i, c=c, k=k)
                    if w:
                        note('TP1WLeafG.lim', lt(s, fsD(k, ONE)), i=i, c=c, k=k)

    # The last-column frame (t = 1).
    x = len(M) - 1
    if x < 1 or M[x][1] == 0 or M[x][2] != 0:
        return counts, examples
    r, q = C.e.par(1, x), C.e.par(0, x)
    if r is None:
        return counts, examples
    T = Ctx(M[:x])
    if not T.ok:
        counts['seed_eval_failed'] += 1
        examples['seed_eval_failed'] = {'matrix': M}
        return counts, examples
    A = C.o(r)
    mu, br, rest = A
    if rest != Z:
        return counts, examples
    seed = T.o(r)
    D = dependencies(C, x)
    if q != r:
        for i in range(x):
            if (False, i) in D and C.e12(i):
                W = C.bumpW(i)
                if ohole(W) and holelev(W) == mu:
                    absorb('AbsDS', i, W, seed)
        return counts, examples
    if not br or last(br) != (succ(mu), Z, Z):
        return counts, examples
    d = lift_counts(C, x, A)
    for i in range(x):
        idx = gamS(mu, br, ONE, max(1, d[i]))
        if (False, i) in D:
            k = C.upg(i)
            if k is not None:
                W = last(C.v(k))
                if ohole(W) and cof(W)[0] == 'omega':
                    absorb('AbsUWL', i, W, idx)
                    if d[i] == 0:
                        absorb('AbsUW0', i, W, seed)
            if C.e12(i):
                W = C.bumpW(i)
                if ohole(W) and cof(W)[0] == 'omega':
                    absorb('AbsDW', i, W, idx)
        if (True, i) in D:
            s, y, _ = C.o(i)
            if y == br or split(y, (succ(s), Z, Z))[1] != Z:
                continue
            l = last(y)
            if not l or l[1] != Z:
                continue
            a = l[0]
            if isSucc(a) or not ohole(a) or cof(a)[0] != 'omega':
                continue
            th = (succ(s), Z, Z)
            note('TPLoW', not lt((fsD(a, idx), Z, Z), th), c=i)
            if d[i] == 0 and notNode(a):
                note('TPLoN', not lt((fsD(a, seed), Z, Z), th), c=i)
    return counts, examples


if __name__ == '__main__':
    main(measure, fields=FIELDS,
         case_unit='absorption: summand; TPLoW/TPLoN: column; leaves: leaf pair',
         definitions=('V3SeedFields.lean', 'V3QRLocV.lean', 'V3QRKeep.lean', 'V3QRFinal4.lean',
                      'V3TP1CutG.lean'))
