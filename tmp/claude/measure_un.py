"""Measure the structural condition `un` of the t = 2 C configuration on all input sets.
Frame: x = len - 1 with t = 2 (M[x][1] != 0 and M[x][2] != 0), r = P2 x, q = P0 x, q != r,
q is not the last counted child of r.  Claim: upg M (x - 1) = none."""
from pathlib import Path
import sys, json, collections
R = Path('/home/koteitan/proofs/trio')
sys.path.insert(0, str(R / 'tmp/codex')); sys.path.insert(0, str(R / 'tools'))
import inv3v3_inputs_audit_20261101 as A

sets = json.loads((R / 'tmp/codex/inv3v3_inputs_sets_20261101.json').read_text())
cnt = collections.Counter(); ex = []
for f in sets:
    try:
        ms = A.A.load(f)
    except Exception as e:
        cnt['load_fail'] += 1; continue
    for raw in ms:
        M = list(map(tuple, raw)); x = len(M) - 1
        if x < 1 or M[x][1] == 0 or M[x][2] == 0: continue
        C = A.A.ctx(M)
        r = C.e.par(2, x); q = C.e.par(0, x)
        if r is None or q is None or q == r: continue
        cl = C.CL(r)
        if cl and cl[-1] == q: continue
        cnt['frames'] += 1
        if C.upg(x - 1) is None: cnt['un_true'] += 1
        else:
            cnt['un_false'] += 1
            if len(ex) < 5: ex.append(raw)
    print(f.split('/')[-1], dict(cnt), flush=True)
print('FINAL', dict(cnt)); print('EX', json.dumps(ex))
