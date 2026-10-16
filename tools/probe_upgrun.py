"""Candidate structural invariant UpgRun (for T2SeedCNext), measured on the ten sets.

UpgRun M: for every column p and consecutive children a < b of p (row-0 tree), if
upg(a - 1) = a, a is topped (no children, or last child = bump a), and some later child c > b of p
has upg(c - 1) = c, then upg(b - 1) = b.
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
            if not any(up(c) for c in ch[idx + 2:]):
                continue
            counts['UpgRun.cases'] += 1
            if not up(b):
                counts['UpgRun.failures'] += 1
                examples.setdefault('UpgRun', {'matrix': M, 'p': p, 'a': a, 'b': b})
    return counts, examples


if __name__ == '__main__':
    main(measure, fields=('UpgRun',), case_unit='consecutive pair (a, b)',
         definitions=('candidate, not in Lean yet',))
