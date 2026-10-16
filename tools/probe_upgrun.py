"""Candidate structural invariant UpgRun (for T2SeedCNext), measured on the ten sets.

UpgRun M: for every column p and consecutive children a < b of p (row-0 tree), if
upg(a - 1) = a, a is topped (no children, or last child = bump a), and some later child c > b of p
has upg(c - 1) = c, then upg(b - 1) = b.
UpgRun is false on the standard (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(1,1,1)(2,1,0)(1,1,1)
(= (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(1,1,1)(2,1,0)(2,0,0)[2] cut), with a = 4, b = 6, c = 8 (c has no children).
Variants: UpgRun2 adds "c is topped and has children"; UpgRun3 adds only "c has children".
Only matrices strictly below SRO. Run with nice -n 15, at most 4 workers.
"""
from collections import Counter

from probe_inv2 import SRO, main
from probe_inv3_prefix import Ctx


def measure(matrix):
    """UpgRun on one matrix."""
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

    def topped(a):
        ch = C.ch(a)
        return not ch or M[ch[-1]] == C.e.bump(a)

    def up(c):
        return c >= 1 and C.upg(c - 1) == c

    for p in range(len(M)):
        ch = C.ch(p)
        for idx in range(len(ch) - 2):
            a, b = ch[idx], ch[idx + 1]
            if not (up(a) and topped(a)):
                continue
            later = [c for c in ch[idx + 2:] if up(c)]
            if not later:
                continue
            variants = [('UpgRun', later),
                        ('UpgRun2', [c for c in later if C.ch(c) and topped(c)]),
                        ('UpgRun3', [c for c in later if C.ch(c)])]
            for name, cs in variants:
                if not cs:
                    continue
                counts[name + '.cases'] += 1
                if not up(b):
                    counts[name + '.failures'] += 1
                    examples.setdefault(name, {'matrix': M, 'p': p, 'a': a, 'b': b, 'c': cs[0]})
    return counts, examples


if __name__ == '__main__':
    main(measure, fields=('UpgRun', 'UpgRun2', 'UpgRun3'), case_unit='consecutive pair (a, b)',
         definitions=('candidate, not in Lean yet',))
