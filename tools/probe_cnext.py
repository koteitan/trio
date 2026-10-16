"""Measure T2SeedCNext (Ytosk/lean/Ytosk/V3CBig.lean) on the ten sets.

Context (T2SeedPRes.C, V3PSeedAllG): x = r + L = |M| - 1, P_2(x) = r, P_0(x) = q, q != r,
q is not the last counted child of r in M (not CL M r = Lc ++ [q]).
Claim, in N = M.take x: for children d < dn of r in N with no child of r strictly between,
dn < q, d not counted and dn counted (Counted N r _), upg N (dn - 1) = dn.
Counted N i c = col c != bump i and not (isUpg c and topped c) (V3Rank), as Ctx.counted.
Only matrices strictly below SRO. Run with nice -n 15, at most 4 workers.
"""
from collections import Counter

from probe_inv2 import SRO, main
from probe_inv3_prefix import Ctx


def measure(matrix):
    """T2SeedCNext at the t = 2 last column with q != r not the last counted child."""
    M = list(matrix)
    counts = Counter(input=1)
    examples = {}
    if not M < SRO:
        counts['outside_SRO'] += 1
        return counts, examples
    x = len(M) - 1
    if x < 1 or M[x][2] == 0:
        return counts, examples
    C = Ctx(M)
    if not C.ok:
        counts['eval_failed'] += 1
        examples['eval_failed'] = {'matrix': M}
        return counts, examples
    counts['measured'] += 1
    r, q = C.e.par(2, x), C.e.par(0, x)
    if r is None or q is None or q == r:
        return counts, examples
    cl = C.CL(r)
    if cl and cl[-1] == q:
        return counts, examples
    N = Ctx(M[:x])
    if not N.ok:
        counts['take_eval_failed'] += 1
        examples['take_eval_failed'] = {'matrix': M}
        return counts, examples
    counts['frames'] += 1
    ch = N.ch(r)
    for d, dn in zip(ch, ch[1:]):
        if dn >= q or N.counted(r, d) or not N.counted(r, dn):
            continue
        counts['T2SeedCNext.cases'] += 1
        if N.upg(dn - 1) != dn:
            counts['T2SeedCNext.failures'] += 1
            examples.setdefault('T2SeedCNext', {'matrix': M, 'r': r, 'q': q, 'd': d, 'dn': dn})
    return counts, examples


if __name__ == '__main__':
    main(measure, fields=('T2SeedCNext',), case_unit='pair (d, dn)',
         definitions=('V3CBig.lean', 'V3PSeedAllG.lean'))
