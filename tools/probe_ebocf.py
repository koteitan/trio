# -*- coding: utf-8 -*-
"""Check the sheet against an independent matrix -> ordinal evaluator (Extended Buchholz).

Each sheet label is turned into an Extended Buchholz term psi_a(b)+c through its D-tree
(probe_fs.from_ord: a unit w^e is D_v(strip(e)), not lowered), and compared, after the
evaluator's standard form sf, with the evaluator's value of the sheet matrix. The evaluator is
Ytosk's algorithm up to SRO (the sheet's last row psi(I) = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0) is
SRO), as implemented in https://github.com/hemisemidemipresent/bms; point EBOCF_LIB at its src/lib.

  EBOCF_LIB=... python3 tools/probe_ebocf.py [N]    counts, and the first N disagreements
"""
import os, sys, json, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.setrecursionlimit(20000)
import probe_fs as F, probe_eps_range as P
from collections import Counter

def dt_eb(t):
    c = []
    for v, a in reversed(t):
        c = [dt_eb(v), dt_eb(a), c]
    return c

def main(nshow=20):
    lines, labs = [], {}
    for L in open(os.path.join(HERE, '..', 'tmp', 'fixed-sheet', 'to-psi-I.tsv')):
        p = L.rstrip('\n').split('\t')
        if not p[0].isdigit() or not p[1].startswith('('): continue
        O = P.parse(p[3])
        if O is None: continue
        try: T = dt_eb(F.from_ord(O))
        except Exception: continue
        labs[int(p[0])] = p[3]
        lines.append(json.dumps({'row': int(p[0]), 'M': [list(c) for c in F.cols(p[1])], 'T': T}))
    out = subprocess.run(['node', os.path.join(HERE, 'ebocf_run.mjs')], input='\n'.join(lines) + '\n',
                         capture_output=True, text=True)
    res = [json.loads(l) for l in out.stdout.splitlines()]
    print(dict(Counter('ok' if r['ok'] else ('err' if r['err'] else 'ng') for r in res)),
          out.stderr[:200])
    for r in [r for r in res if not r['ok']][:nshow]:
        print(r['row'], labs[r['row']]); print('   eval ', r['js']); print('   label', r['lab'])
    return res

if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 20)
