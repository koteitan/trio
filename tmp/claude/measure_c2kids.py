"""T2C2Kids (V3VRAPreC.lean) at the C2 root frames of tmp/codex/seedfo_C2_shapes_20261104 (all t = 2 C2 frames of the
86 sets): CL_N(r) = CL_M(r) ++ [q], v_N(r) = v_M(r), o_N(d) = o_M(d) for the children before the last one c0 of CL_M(r),
and o_N(c0) = psi s y 0 with y != 0  ==>  o_M(c0) = psi s yM 0 with y <= yM.  n = 2, 3, 4."""
import json, glob, sys, collections
R = '/home/koteitan/proofs/trio'
sys.path.insert(0, R + '/tools'); sys.path.insert(0, R + '/tmp/codex')
import seedfo_C2_matches_20261104 as G7
A = G7.A; B = G7.B
from lhd_exact import le as LE
SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]
rows = []
for f in sorted(glob.glob(R + '/tmp/codex/seedfo_C2_shapes_20261104/set*.json')):
    d = json.load(open(f))
    for r in (d.get('records', []) if isinstance(d, dict) else d):
        if isinstance(r, dict) and 'matrix' in r: rows.append(r)
cnt = collections.Counter(); ex = {}
seen = set()
for row in rows:
    M = list(map(tuple, row['matrix'])); x = row['x']; r = row['r']; q = row['q']
    if not M < SRO: cnt['outside_SRO'] += 1; continue
    for n in (2, 3, 4):
        key = (tuple(M), n)
        if key in seen: continue
        seen.add(key)
        try:
            C = A.ctx(M)
            N = list(map(tuple, B.trio.expand([list(c) for c in M], n))); CN = A.ctx(N)
            if not (C.ok and CN.ok): cnt['unresolved'] += 1; continue
        except Exception:
            cnt['unresolved'] += 1; continue
        cnt['frames'] += 1
        clM, clN = C.CL(r), CN.CL(r)
        def bad(k):
            cnt[k] += 1
            if k not in ex or len(M) < len(ex[k]['M']): ex[k] = dict(M=M, n=n, r=r, q=q)
        if clN != clM + [q]: bad('cl.false')
        if CN.v(r) != C.v(r): bad('v.false')
        if not clM: cnt['clM_empty'] += 1; continue
        if any(CN.o(d) != C.o(d) for d in clM[:-1]): bad('prefix.false')
        c0 = clM[-1]; oN, oM = CN.o(c0), C.o(c0)
        if oN[2] != (): cnt['last_not_single'] += 1
        if oN[1] == (): cnt['last.argfree'] += 1; continue
        cnt['last.arg'] += 1
        if not (oM[2] == () and oM[0] == oN[0] and LE(oN[1], oM[1])): bad('last.false')
print(json.dumps(dict(cnt), indent=1)); print('EX', json.dumps(ex))
