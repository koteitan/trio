# -*- coding: utf-8 -*-
"""Check the sheet against an independent matrix -> ordinal evaluator (Extended Buchholz).

Each sheet label is turned into an Extended Buchholz term psi_a(b)+c through its D-tree
(probe_fs.from_ord: a unit w^e is D_v(strip(e)), not lowered), and compared, after the
evaluator's standard form sf, with the evaluator's value of the sheet matrix. The evaluator is
Ytosk's algorithm up to SRO (the sheet's last row psi(I) = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0) is
SRO), as implemented in https://github.com/hemisemidemipresent/bms; point EBOCF_LIB at its src/lib.

  EBOCF_LIB=... python3 tools/probe_ebocf.py [N]      counts, and the first N disagreements
  EBOCF_LIB=... python3 tools/probe_ebocf.py lean [N]  the Lean definition lean/Ebocf.lean against the
                                                       JavaScript on every sheet matrix
  python3 tools/probe_ebocf.py rt [N]                  round trip of the builder, Lean only
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

def lean_eval(mats):
    """{row: str(eval M)} from the Lean definition lean/Ebocf.lean (run through lean/EbocfRun.lean)."""
    ldir = os.path.join(HERE, '..', 'lean')
    inp = ''.join('%d\t%s\n' % (r, F.smat(m)) for r, m in mats)
    out = subprocess.run(['lake', 'env', 'lean', '--run', 'EbocfRun.lean'], cwd=ldir, input=inp,
                         capture_output=True, text=True)
    return {int(l.split('\t')[0]): l.split('\t')[1] for l in out.stdout.splitlines()}

def compare_lean(nshow=10):
    """Every sheet matrix (labelled or not): does the Lean evaluator print what the JavaScript does."""
    mats = []
    for L in open(os.path.join(HERE, '..', 'tmp', 'fixed-sheet', 'to-psi-I.tsv')):
        p = L.rstrip('\n').split('\t')
        if p[0].isdigit() and p[1].startswith('('): mats.append((int(p[0]), F.cols(p[1])))
    js = subprocess.run(['node', os.path.join(HERE, 'ebocf_run.mjs')], capture_output=True, text=True,
                        input=''.join(json.dumps({'row': r, 'M': [list(c) for c in m], 'T': []}) + '\n'
                                      for r, m in mats)).stdout
    js = {d['row']: d['js'] or 'none' for d in map(json.loads, js.splitlines())}   # js errors: a cycle
    le = lean_eval(mats)
    same = [r for r, _ in mats if js.get(r) == le.get(r)]
    print('rows', len(mats), ' lean == js', len(same), ' (no value: %d)' % sum(le.get(r) == 'none' for r in same))
    for r, m in mats:
        if js.get(r) != le.get(r) and nshow > 0:
            nshow -= 1; print(r, F.smat(m)); print('   js  ', js.get(r)); print('   lean', le.get(r))

BMS = os.path.expanduser('~/code/yaBMS/c/bms')
_std = {}
def standard(m):
    k = tuple(m)
    if k not in _std:
        _std[k] = subprocess.run([BMS, '-s', F.smat(m)], capture_output=True, text=True).stdout.strip() == '1'
    return _std[k]

def roundtrip(nshow=10):
    """Lean only: the sheet matrix S, the builder's matrix B = block(lower(label)) and the label, all
    through lean/Ebocf.lean. Classes: B = S or not; eval(B) = label (round trip) or not; bms -s."""
    rows, jobs = [], []
    for L in open(os.path.join(HERE, '..', 'tmp', 'fixed-sheet', 'to-psi-I.tsv')):
        p = L.rstrip('\n').split('\t')
        if not p[0].isdigit() or not p[1].startswith('('): continue
        O = P.parse(p[3])
        if O is None: continue
        try: T = dt_eb(F.from_ord(O))
        except Exception: continue
        r, S = int(p[0]), F.cols(p[1])
        try: B = P.block(P.lower(O), 0, 0, False)
        except Exception: B = None
        rows.append((r, p[3], S, B))
        jobs += [(3 * r, S), (3 * r + 2, None)] + ([(3 * r + 1, B)] if B else [])
        labterm[3 * r + 2] = json.dumps(T).replace(' ', '')
    ldir = os.path.join(HERE, '..', 'lean')
    inp = ''.join('%d\t%s\n' % (k, ('=' + labterm[k]) if m is None else F.smat(m)) for k, m in jobs)
    out = subprocess.run(['lake', 'env', 'lean', '--run', 'EbocfRun.lean'], cwd=ldir, input=inp,
                         capture_output=True, text=True).stdout
    v = {int(l.split('\t')[0]): l.split('\t')[1] for l in out.splitlines()}
    cnt, cand = Counter(), []
    for r, lab, S, B in rows:
        L, eS, eB = v[3 * r + 2], v[3 * r], v.get(3 * r + 1)
        if B == S:
            cnt['B=S, eval = label' if eS == L else 'B=S, eval != label'] += 1
        elif eB == L:
            k = 'B!=S, round trip, B %s, S %s' % ('std' if standard(B) else 'nonstd',
                                                 'std' if standard(S) else 'nonstd')
            if eS == L: k += ', S also = label'
            cnt[k] += 1
            if standard(B) and standard(S) and eS != L: cand.append((r, lab, S, B, eS, eB))
        else:
            cnt['B!=S, no round trip' + (', S = label' if eS == L else '')] += 1
    for k in sorted(cnt): print('%5d  %s' % (cnt[k], k))
    for r, lab, S, B, eS, eB in cand[:nshow]:
        print(r, lab); print('   sheet', F.smat(S), ' =', eS); print('   build', F.smat(B))
    return cand

labterm = {}

if __name__ == '__main__':
    if sys.argv[1:2] == ['lean']: compare_lean(int(sys.argv[2]) if len(sys.argv) > 2 else 10)
    elif sys.argv[1:2] == ['rt']: roundtrip(int(sys.argv[2]) if len(sys.argv) > 2 else 10)
    else: main(int(sys.argv[1]) if len(sys.argv) > 1 else 20)
