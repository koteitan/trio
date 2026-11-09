"""DecPShape2 (sibling chain) and DecPUntop (V3DecPSplit.lean) on the 86 sets, C1 frames (q != r, CL_M(r) not ending in q, upg(x-1) = none).
DecPShape: c0 (last counted child of r in T) topped in T -> exists b child of c0 with col b = bump c0, b < x, q-1 child of b.
DecPUntop: c0 untopped in T -> qnS < v_T(c0)."""
import sys, json, collections
for p in ['/home/koteitan/proofs/trio/tmp/claude', '/home/koteitan/proofs/trio/tools',
          '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b',
          '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD']:
    sys.path.insert(0, p)
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx, Z, ONE, lt, le, sumN
import ytosk_eval as Y
from pv2 import load
def measure(m):
    M = list(map(tuple, m)); cnt = collections.Counter(); ex = None
    if not M < SRO: return cnt, ex
    x = len(M) - 1
    if x < 1 or M[x][2] == 0: return cnt, ex
    C = Ctx(M)
    if not C.ok: return cnt, ex
    r = C.e.par(2, x); q = C.e.par(0, x)
    if r is None or q is None or q == r: return cnt, ex
    clM = C.CL(r)
    if (clM and clM[-1] == q) or C.upg(x - 1) is not None: return cnt, ex
    T = Ctx(M[:-1])
    if not T.ok: return cnt, ex
    W = Y.add(C.v(r), Y.omega(sumN([ONE] + [C.bumpTerm(q, d) for d in C.ch(q) if d < x])))
    cl = T.CL(r)
    cnt['cases'] += 1
    if not cl: cnt['CL_empty'] += 1; return cnt, ex
    c0 = cl[-1]
    if T.e.topped(c0):
        cnt['topped'] += 1
        chs = [w for w in T.ch(r) if c0 <= w <= q]
        ok = True
        for w, w2 in zip(chs, chs[1:]):
            if not any(M[b] == T.e.bump(w) and b < x and T.e.par(0, w2 - 1) == b for b in T.ch(w)) or C.upg(w2 - 1) != w2:
                ok = False
        if ok: cnt['shape2.ok'] += 1
        else: cnt['shape2.FAIL'] += 1; ex = ('shape2', M)
        cnt['nsib.%d' % len(chs)] += 1
    else:
        cnt['untopped'] += 1
        if lt(W, T.v(c0)): cnt['untop.ok'] += 1
        else: cnt['untop.FAIL'] += 1; ex = ('untop', M)
    return cnt, ex
if __name__ == '__main__':
    from multiprocessing import Pool
    sets = json.load(open('/home/koteitan/proofs/trio/tmp/codex/inv3v3_inputs_sets_20261101.json'))
    tot = collections.Counter(); exs = {}
    with Pool(4) as pool:
        for f in sets:
            for c, e in pool.imap_unordered(measure, load(f), chunksize=200):
                tot.update(c)
                if e and (e[0] not in exs or len(e[1]) < len(exs[e[0]])): exs[e[0]] = e[1]
            print(f.split('/')[-1], json.dumps(dict(tot)), flush=True)
    print('FINAL', json.dumps(dict(tot))); print('EX', exs)
