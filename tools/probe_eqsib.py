"""Candidate structural invariant EqSibUpg (for PassRootRes, V3ExpT1V.lean), measured on the ten sets.

EqSibUpg M (V3PassRoot.lean): for every column r and every child c of r (row-0 tree) with
an earlier sibling (a child b < c of r), if some bump child j of c (col j = bump c) has a strict
descendant y (Anc0 j y, j != y) with P_1(y) = r, then c is an upgrade target (isUpg c).
(Under R1S/BumpE2/R0P the premise forces col(c) = (e0 r + 1, e1 r + 1, 1).)

Reason for PassRootRes: a counted child c of r = P_1(x) whose v depends on x (c < x) has
col(c) = (e0 r + 1, e1 r + 1, 1) and is topped and counted, so it is not an upgrade target; its bump
child reaches x (or the column before the next upgrade target). An earlier counted sibling is >= c,
so equal to c. EqSibUpg forbids this.

Also measured (t = 1 matrices only): PassFirst = every counted child c of r = P_1(x) with c < x and
DepX M x false c is the first child of r (no earlier child at all).
Only matrices strictly below SRO. Run with nice -n 15, at most 4 workers.
"""
from collections import Counter

from probe_inv2 import SRO, dependencies, main
from probe_inv3_prefix import Ctx


def measure(matrix):
    """EqSibUpg and PassFirst on one matrix."""
    M = list(matrix)
    counts = Counter(input=1)
    examples = {}
    if not M < SRO:
        counts['outside_SRO'] += 1
        return counts, examples
    C = Ctx(M)
    if not C.ok:
        counts['eval_failed'] += 1
        return counts, examples
    counts['measured'] += 1
    n = len(M)
    e = C.e

    def strict_desc(j):
        b = j + 1
        while b < n and M[b][0] > M[j][0]:
            yield b
            b += 1

    for r in range(n):
        ch = C.ch(r)
        for idx, c in enumerate(ch):
            if idx == 0:
                continue
            hit = any(M[j] == e.bump(c) and any(e.par(1, y) == r for y in strict_desc(j))
                      for j in C.ch(c))
            if not hit:
                continue
            counts['EqSibUpg.cases'] += 1
            if c not in e.upgs:
                counts['EqSibUpg.failures'] += 1
                examples.setdefault('EqSibUpg', {'matrix': M, 'r': r, 'c': c, 'children': ch})

    x = n - 1
    if x >= 1 and M[x][1] != 0 and M[x][2] == 0:
        r = e.par(1, x)
        if r is not None:
            D = dependencies(C, x)
            ch = C.ch(r)
            for c in C.CL(r):
                if c >= x or (False, c) not in D:
                    continue
                counts['PassFirst.cases'] += 1
                if ch[0] != c:
                    counts['PassFirst.failures'] += 1
                    examples.setdefault('PassFirst', {'matrix': M, 'r': r, 'c': c, 'children': ch})
    return counts, examples


if __name__ == '__main__':
    main(measure, fields=('EqSibUpg', 'PassFirst'), case_unit='later child c with the premise / dependent child c',
         definitions=('V3PassRoot.lean: EqSibUpg', 'V3ExpT1V.lean: PassRootRes (strong form)'))
