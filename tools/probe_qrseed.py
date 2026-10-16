"""t = 1, q = r (P_0 x = P_1 x = r): the seed o'(r) of M.take x against o(r) (V3QRFinal3, hS).
Cases at r:
  lhd  : Lhd z o'(r) o(r) (exact, lhd_exact.py) -- the old path (seedOK_of_lhd_below / _top).
  cs   : not lhd; o'(r) = psi w' 0 0 with WkVA w' v(r) and CS w'  -- seedOK_of_cs_below (V3SeedWeak).
  small: not lhd, not cs; every component of w' is below Omega_{w'} (seedOK_of_small_below).
  wcs  : not lhd, not cs, not small; WCS (v(P_0 r)) w'  -- WCSP's second case.
  FAIL : none of these.
Also split by L = x - r == 1 and by s1 = subscript of o'(r) < v(r) or = v(r).
Only matrices strictly below SRO. nice -n 15, at most 4 workers.
Usage: nice -n 15 python3 probe_qrseed.py --output DIR [SET ...]
"""
from collections import Counter

from probe_inv2 import SRO, main
from probe_inv3_prefix import Ctx, Z, ONE, lt, le, isOT
from lhd_exact import lhdE, comps, indices

OM1 = (ONE, Z, Z)


def CS(t): return all(lt(g, OM1) for g in comps(Z, t))


def WCS(a, w):
    us = {Z, a}; indices(w, us); indices(a, us)
    for u in us:
        if lt(a, u): continue
        ca = comps(u, a)
        mx = Z
        for d in ca:
            if lt(mx, d): mx = d
        for g in comps(u, w):
            if not (lt(g, OM1) or le(g, mx)): return False
    return True


def measure(matrix):
    M = list(matrix)
    counts, examples = Counter(input=1), {}
    if not M < SRO:
        counts['outside_SRO'] += 1
        return counts, examples
    x = len(M) - 1
    if x < 1 or M[x][1] == 0 or M[x][2] != 0:
        return counts, examples
    C = Ctx(M)
    if not C.ok:
        counts['eval_failed'] += 1
        return counts, examples
    r = C.e.par(1, x)
    if r is None or C.e.par(0, x) != r:
        return counts, examples
    T = Ctx(M[:-1])
    if not T.ok:
        counts['eval_failed_take'] += 1
        return counts, examples
    counts['qr'] += 1
    seed, oR, vr = T.o(r), C.o(r), C.v(r)
    tag = 'L1' if x - r == 1 else 'L>1'
    sub = 'top' if seed and seed[0] == vr else 'below'
    if lhdE(seed, oR):
        case = 'lhd'
    elif seed and seed[1] == Z and seed[2] == Z and lt(seed[0], vr) and le(ONE, seed[0]) and isOT(seed[0]):
        w = seed[0]
        small = all(lt(g, (w, Z, Z)) for g in comps(Z, w))
        if CS(w):
            case = 'cs'
        elif small:
            case = 'small'
        else:
            g = C.e.par(0, r)
            case = 'wcs' if g is not None and WCS(C.v(g), w) else 'FAIL'
    else:
        case = 'FAIL'
    counts['QRSeed.cases'] += 1
    counts['QRSeed.%s.%s.%s' % (case, tag, sub)] += 1
    if case == 'FAIL':
        counts['QRSeed.failures'] += 1
        examples.setdefault('QRSeed', {'matrix': M, 'r': r})
    elif case in ('cs', 'small', 'wcs'):
        examples.setdefault('QRSeed.' + case, {'matrix': M, 'r': r})
    return counts, examples


if __name__ == '__main__':
    main(measure, fields=('QRSeed',), case_unit='t = 1, q = r matrix',
         definitions=('V3QRFinal3 hS; V3SeedWeak seedOK_of_cs_below',))
