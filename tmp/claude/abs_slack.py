"""Task A: where is the slack of a bad absorption column resolved?
For each of the 226 absorption-failure frames (tmp/codex/abs_failures_classified_20261101.json),
classify, for every column c < bnd, the change of v(c) and o(c) from M to N = M[n]:
  eq / lhd0 (Lhd z) / lhdV (Lhd v(m) only, m = P1 i) / lt / notlt
and record the relation of c to the bad column i, and the first column on the P0 path from i
to the root where both v and o are eq or lhd0 (the recovery point).
Exact Lhd η b a (FS.lean): b < a ∧ ∀ u c, b < c ≤ a → Dom (comps u b) (comps u c ++ z :: comps u η).
"""
from pathlib import Path
import sys, json, collections
R = Path('/home/koteitan/proofs/trio')
sys.path.insert(0, str(R / 'tmp/codex')); sys.path.insert(0, str(R / 'tools'))
import inv3v3_inputs_audit_20261101 as A
from lhd_exact import lt, comps, tmax, succ, indices, ex_K

Z = ()


def lhdV(V, b, a):
    if not lt(b, a): return False
    us = set(); indices(b, us); indices(V, us)
    I = (succ(b), (a, True))
    for u in us:
        g = tmax(comps(u, b))
        if not g: continue
        h = tmax(comps(u, V))
        if not lt(h, g): continue          # allowance covers g
        if ex_K(u, g)(I): return False
    return True


def cls(old, new, V):
    if old == new: return 'eq'
    if lhdV(Z, new, old): return 'lhd0'
    if V is not None and lhdV(V, new, old): return 'lhdV'
    if lt(new, old): return 'lt'
    return 'notlt'


def anc(e, row, c, i):
    p = e.par(row, i)
    while p is not None:
        if p == c: return True
        p = e.par(row, p)
    return False


frames = json.load(open(R / 'tmp/codex/abs_failures_classified_20261101.json'))
out = []
for fr in frames:
    M = [tuple(c) for c in fr['M']]; n = fr['n']; i = fr['i']; r = fr['r']; row = fr['row']
    x = len(M) - 1
    bnd = r if row == 0 else x
    C = A.A.ctx(M)
    N = [tuple(c) for c in A.trio.expand([list(c) for c in M], n)]
    CN = A.A.ctx(N)
    m = C.e.par(1, i)
    V = C.v(m) if m is not None else None
    cols = []
    for c in range(bnd):
        cv = cls(C.v(c), CN.v(c), V); co = cls(C.o(c), CN.o(c), V)
        rel = []
        if c == i: rel.append('i')
        if c == m: rel.append('m')
        if anc(C.e, 0, c, i): rel.append('P0anc')
        if anc(C.e, 1, c, i): rel.append('P1anc')
        if C.upg(c) == i: rel.append('upg_c_to_i')
        if C.upg(i) == c: rel.append('upg_i_to_c')
        if C.upg(c) is not None and C.upg(c) != i: rel.append('upg_c_to_%d' % C.upg(c))
        cols.append({'c': c, 'v': cv, 'o': co, 'rel': rel, 'col': M[c]})
    bad = [d for d in cols if d['v'] not in ('eq', 'lhd0') or d['o'] not in ('eq', 'lhd0')]
    # recovery point on the P0 path from i
    rec = None; p = C.e.par(0, i)
    while p is not None:
        d = cols[p] if p < bnd else None
        if d and d['v'] in ('eq', 'lhd0') and d['o'] in ('eq', 'lhd0'):
            rec = p; break
        p = C.e.par(0, p)
    out.append({'set': fr['set'], 'index': fr['index'], 'n': n, 'row': row, 'r': r, 'i': i, 'm': m,
                'clauses': fr['clauses'], 'upgraders': fr['upgraders'], 'W_eq_seed': fr['W_eq_seed'],
                'M': fr['M'], 'not_lhd0': bad, 'recovery': rec,
                'CL_m': C.CL(m) if m is not None else None,
                'bumpkid_m': (C.e.par(0, m) is not None and M[m] == C.e.bump(C.e.par(0, m))) if m is not None else None})

(R / 'tmp/claude/abs_slack_20261101.json').write_text(json.dumps(out, indent=1))
summ = collections.Counter()
shapes = collections.Counter()
for o in out:
    key = ('t0' if o['row'] == 0 else 't2', all(o['clauses'].values()))
    summ[key] += 1
    shapes[(key, tuple(sorted((tuple(d['rel']), d['v'], d['o']) for d in o['not_lhd0'])), o['recovery'] is not None)] += 1
print('frames', len(out), dict(summ))
for k, v in shapes.most_common():
    print(v, k)
