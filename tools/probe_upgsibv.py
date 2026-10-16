"""Measure UpgSibV (candidate, Ytosk/lean/Ytosk/V3CBigV.lean) on the ten sets.

UpgSibV N τ: for every column p and consecutive children a < b of p (row-0 tree, no child of p strictly
between), if upg N (a - 1) = a, topped N a, and upg N (b - 1) != b, then v(b) <= v(a).
It replaces the false T2SeedCNext (V3CBig) in the proof of T2SeedCBig: an uncounted child d of r whose next
sibling dn is counted and not upgraded from dn - 1 has v(dn) <= v(d).
T2SeedCNext is false on the standard
(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(2,1,1)(1,1,1)(2,1,1)(3,0,0)(2,1,0)(1,1,1)(2,1,1)
(prefix of (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(2,1,1)(1,1,1)(2,1,1)(3,0,0)(2,1,0)(2,0,0)[2]);
UpgSibV holds there (checked by --selftest).
upg = Ctx.upg (Eval.lean `upg`), topped = Eval.lean `topped`, v = the valuation of Ev2 (the Cons valuation).
Only matrices strictly below SRO. Run with nice -n 15, at most 4 workers.
"""
import sys
from collections import Counter

import ytosk_eval as Y
from probe_inv2 import SRO, main
from probe_inv3_prefix import Ctx

CEX = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 1), (3, 0, 0), (2, 1, 1), (1, 1, 1),
       (2, 1, 1), (3, 0, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)]


def measure(matrix):
    """UpgSibV on one matrix."""
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

    def topped(a):
        ch = C.ch(a)
        return not ch or M[ch[-1]] == C.e.bump(a)

    def up(c):
        return c >= 1 and C.upg(c - 1) == c

    for p in range(len(M)):
        ch = C.ch(p)
        for a, b in zip(ch, ch[1:]):
            if not (up(a) and topped(a)) or up(b):
                continue
            counts['UpgSibV.cases'] += 1
            if Y.lt(C.v(a), C.v(b)):
                counts['UpgSibV.failures'] += 1
                examples.setdefault('UpgSibV', {'matrix': M, 'p': p, 'a': a, 'b': b})
    return counts, examples


if __name__ == '__main__':
    if sys.argv[1:] == ['--selftest']:
        for k in range(1, len(CEX) + 1):
            c, e = measure(CEX[:k])
            assert not c['UpgSibV.failures'], (k, e)
        print(measure(CEX))
        sys.exit(0)
    main(measure, fields=('UpgSibV',), case_unit='consecutive pair (a, b)',
         definitions=('V3CBigV.lean',))
