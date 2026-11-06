"""QNRelR.unc (V3SeedPFNarrow.lean) at the qn configurations (t = 2, q != r, CL_M(r) = Lc ++ [q]) of the 86 sets
below SRO: every child d < q of r not counted at r has qnS < v(d), qnS = v(r) + w^(1 + sum of the bump terms of the
children of q before x).  One process."""
import sys, json, collections
for p in ['/home/koteitan/proofs/trio/tmp/claude', '/home/koteitan/proofs/trio/tools',
          '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b',
          '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD']:
    sys.path.insert(0, p)
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx, ONE, lt, sumN
import ytosk_eval as Y
from pv2 import load


def measure(M, cnt, ex):
    if not M < SRO: return
    x = len(M) - 1
    if x < 1 or M[x][2] == 0: return
    C = Ctx(M)
    if not C.ok: return
    r = C.e.par(2, x); q = C.e.par(0, x)
    if r is None or q is None or q == r: return
    cl = C.CL(r)
    if not cl or cl[-1] != q: return
    cnt['qn.frames'] += 1
    Sq = Y.add(C.v(r), Y.omega(sumN([ONE] + [C.bumpTerm(q, d) for d in C.ch(q) if d < x])))
    for d in C.ch(r):
        if d >= q or d in cl: continue
        cnt['unc.cases'] += 1
        if not lt(Sq, C.v(d)):
            cnt['unc.failures'] += 1
            if 'unc' not in ex or len(M) < len(ex['unc']['matrix']):
                ex['unc'] = dict(matrix=M, r=r, q=q, d=d, Sq=Y.tstr(Sq), vd=Y.tstr(C.v(d)))


if __name__ == '__main__':
    sets = json.load(open('/home/koteitan/proofs/trio/tmp/codex/inv3v3_inputs_sets_20261101.json'))
    tot = collections.Counter(); ex = {}
    for f in sets:
        for m in load(f):
            measure(list(map(tuple, m)), tot, ex)
        print(f.split('/')[-1], json.dumps(dict(tot)), flush=True)
    print('FINAL', json.dumps(dict(tot))); print('EX', json.dumps(ex, default=str))
