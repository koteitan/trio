"""T2CopyK CopyVDomK (V3RwClCopy.lean) exactly: VDomF V V' a at the copy frames i of P = M[n-1] (r <= i, le1 P r i)
that have a counted child (CL P i nonempty).  VD_all: the same at every le1 frame (tools/probe_t2vrak.py's VD).
Levels u' in {0} + indices of V', f(a) with not f(a) < u' (comps u' is constant between them)."""
import sys, json, collections
from multiprocessing import Pool
for p in ['/home/koteitan/proofs/trio/tools', '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b',
          '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD']:
    sys.path.insert(0, p)
import probe_t2vrak as K
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx, Z, lt, le, comps
from vracopy import shf
from lhd_exact import indices
import trio, ytosk_eval as Y
from pv2 import load


def measure(matrix):
    M = list(matrix); cnt = collections.Counter(); ex = {}
    if not M < SRO: return cnt, ex
    x = len(M) - 1
    if x < 1 or M[x][2] == 0: return cnt, ex
    C = Ctx(M)
    if not C.ok: return cnt, ex
    r = C.e.par(2, x)
    if r is None: return cnt, ex
    L = x - r
    for n in (2, 3):
        N = trio.expand(M, n); P = trio.expand(M, n - 1)
        CN, CP = Ctx(N), Ctx(P)
        if not (CN.ok and CP.ok): continue
        V = CP.v(r); V2 = CN.v(r + L)
        for i in range(r, len(P)):
            if not K.le1(CP, r, i): continue
            a = CP.v(i); fa = shf(V, V2, a)
            us = {Z}; indices(V2, us); indices(fa, us)
            ok = True
            for u in us:
                if lt(fa, u): continue
                cfa = comps(u, fa)
                if not all(le(g, (fa, Z, Z)) or any(le(g, d) for d in cfa) for g in comps(u, V2)):
                    ok = False; break
            kids = bool(CP.CL(i))
            cnt['VDall.frames'] += 1; cnt['VDK.frames'] += kids
            if not ok:
                cnt['VDall.failures'] += 1
                if kids:
                    cnt['VDK.failures'] += 1
                    if 'VDK' not in ex or len(M) < len(ex['VDK']['matrix']):
                        ex['VDK'] = {'matrix': M, 'n': n, 'i': i, 'P_i': P[i], 'V': Y.tstr(V), 'V2': Y.tstr(V2),
                                     'a': Y.tstr(a), 'fa': Y.tstr(fa)}
    return cnt, ex


if __name__ == '__main__':
    sets = [f for f in json.load(open('/home/koteitan/proofs/trio/tmp/codex/inv3v3_inputs_sets_20261101.json'))
            if f.split('/')[-1] in sys.argv[1:]]
    tot = collections.Counter(); exs = {}
    with Pool(4) as pool:
        for f in sets:
            for c, e in pool.imap_unordered(measure, load(f), chunksize=100):
                tot.update(c)
                for k, v in e.items():
                    if k not in exs or len(v['matrix']) < len(exs[k]['matrix']): exs[k] = v
            print(f.split('/')[-1], json.dumps(dict(tot)), flush=True)
    print('FINAL', json.dumps(dict(tot))); print('EX', json.dumps(exs, default=str))
