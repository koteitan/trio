# -*- coding: utf-8 -*-
"""Measure the psi_0(Omega_alpha) builder on the gap rows of the sheet (the rows whose label is
not a single psi_0(Omega_alpha)).

The candidate for a label O (an ordinal < psi_0(Lambda), parsed with probe_eps_range.parse)
is block(O, 0): one column per summand w^delta, whose children spell strip(delta). For a pure
row psi_0(Omega_alpha) this is M(alpha) again. Prints the counts and the first failures.

  python3 tools/probe_gap.py [N]     N = number of failures to print (default 12)
"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.setrecursionlimit(20000)
import probe_eps_range as P
from collections import Counter

def s(m): return ''.join('(%d,%d,%d)' % c for c in m)

def cols(mat):
    cs = [tuple(int(v) for v in c.split(',')) for c in re.findall(r'\((\d+(?:,\d+)*)\)', mat)]
    return [c + (0,) * (3 - len(c)) for c in cs]

def main(nshow=12):
    pure = set(l.split('\t')[0] for l in open(os.path.join(HERE, 'omega_alpha_rows.tsv')))
    cnt = Counter(); fails = []
    for L in open(os.path.join(HERE, '..', 'tmp', 'fixed-sheet', 'to-psi-I.tsv')):
        p = L.rstrip('\n').split('\t')
        if not p[0].isdigit() or not p[1].startswith('('): continue
        r = int(p[0])
        try: O = P.parse(p[3])
        except Exception: O = None
        if O is None: cnt['unparsed'] += 1; continue
        try: got = P.block(O, 0, 0, False)
        except Exception: cnt['error'] += 1; continue
        ok = got == cols(p[1])
        k = 'pure' if str(r) in pure else 'gap'
        cnt[k + (' ok' if ok else ' ng')] += 1
        if not ok and k == 'gap': fails.append((r, p[3], s(cols(p[1])), s(got)))
    print(dict(cnt))
    for e in fails[:nshow]:
        print(e[0], e[1]); print('   sheet', e[2][:160]); print('   got  ', e[3][:160])

if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 12)
