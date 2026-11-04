"""C2 root frames: compare N = M[n] with M (not with T = M.take x).
Hypothesis H2: CL_M(r) = CL_T(r), CL_N(r) = CL_T(r) ++ [q], v_N(r) = v_M(r), and o_N(d) = o_M(d) for d in CL_T(r).
Then every state before a child of CL_N(r) is a prefix state of M's frame at r (FrameOT M) or the
complete state o_M(r) (Good3 M)."""
import json, glob, sys, collections
R = '/home/koteitan/proofs/trio'
sys.path.insert(0, R + '/tools'); sys.path.insert(0, R + '/tmp/codex')
import seedfo_C2_matches_20261104 as G7
A = G7.A; B = G7.B
rows = []
for f in glob.glob(R + '/tmp/codex/seedfo_C2_shapes_20261104/set*.json'):
    d = json.load(open(f))
    for r in (d.get('records', []) if isinstance(d, dict) else d):
        if isinstance(r, dict) and 'matrix' in r: rows.append(r)
cnt = collections.Counter(); ex = []
seen = set()
for row in rows:
    M = list(map(tuple, row['matrix'])); x = row['x']; r = row['r']; q = row['q']
    for n in (2, 3):
        key = (tuple(M), n)
        if key in seen: continue
        seen.add(key)
        try:
            C, T = A.ctx(M), A.ctx(M[:x])
            N = list(map(tuple, B.trio.expand([list(c) for c in M], n))); CN = A.ctx(N)
            if not all(c.ok for c in (C, T, CN)): cnt['unresolved'] += 1; continue
        except Exception:
            cnt['unresolved'] += 1; continue
        cnt['frames'] += 1
        clT, clM, clN = T.CL(r), C.CL(r), CN.CL(r)
        h = {
            'clM_eq_clT': clM == clT,
            'clN_eq_clT_q': clN == clT + [q],
            'vN_eq_vM_r': CN.v(r) == C.v(r),
            'oN_eq_oM_children': all(CN.o(d) == C.o(d) for d in clT),
        }
        for k2, v in h.items(): cnt[k2 + '.' + str(v)] += 1
        if all(h.values()): cnt['H2'] += 1
        elif len(ex) < 3: ex.append(dict(M=M, n=n, x=x, r=r, q=q, h=h, clT=clT, clM=clM, clN=clN))
print(json.dumps(dict(cnt), indent=1)); print('EX', json.dumps(ex))

# --- part 2: prefix state arguments in N versus M: equal or Lhd z (N below M) ---
sys.path.insert(0, R + '/tmp/claude')
from abs_slack import lhdV
cnt2 = collections.Counter(); ex2 = []
seen2 = set()
for row in rows:
    M = list(map(tuple, row['matrix'])); x = row['x']; r = row['r']; q = row['q']
    for n in (2, 3):
        key = (tuple(M), n)
        if key in seen2: continue
        seen2.add(key)
        try:
            C = A.ctx(M); T = A.ctx(M[:x])
            N = list(map(tuple, B.trio.expand([list(c) for c in M], n))); CN = A.ctx(N)
            if not all(c.ok for c in (C, T, CN)): continue
        except Exception: continue
        a = CN.v(r); clT = T.CL(r)
        for j in range(len(clT) + 1):
            AN = B.spa(a, B.sumN([CN.o(d) for d in clT[:j]]))
            AM = B.spa(a, B.sumN([C.o(d) for d in clT[:j]]))
            if AN == AM: rel = 'eq'
            elif lhdV((), AN, AM): rel = 'lhd0'
            elif B.lt(AN, AM): rel = 'lt'
            else: rel = 'not_lt'
            cnt2['j%d_of_%d.%s' % (j, len(clT), rel)] += 1
            if rel == 'not_lt' and len(ex2) < 2: ex2.append(dict(M=M, n=n, r=r, j=j))
print('PART2', json.dumps(dict(cnt2), indent=1)); print('EX2', json.dumps(ex2))

# --- part 3: child-level relation o_N(d) vs o_M(d) for d in CL_T(r), and whether d is a D column ---
cnt3 = collections.Counter()
seen3 = set()
for row in rows:
    M = list(map(tuple, row['matrix'])); x = row['x']; r = row['r']
    for n in (2, 3):
        key = (tuple(M), n)
        if key in seen3: continue
        seen3.add(key)
        try:
            C = A.ctx(M); T = A.ctx(M[:x])
            N = list(map(tuple, B.trio.expand([list(c) for c in M], n))); CN = A.ctx(N)
            if not all(c.ok for c in (C, T, CN)): continue
        except Exception: continue
        clT = T.CL(r)
        for pos, d in enumerate(clT):
            old, new = C.o(d), CN.o(d)
            rel = 'eq' if old == new else ('lhd0' if lhdV((), new, old) else ('lt' if B.lt(new, old) else 'not_lt'))
            cnt3['%s.%s' % ('last' if pos == len(clT) - 1 else 'notlast', rel)] += 1
print('PART3', json.dumps(dict(cnt3), indent=1))
