"""VDomU (V3T2VRAK3.lean) at the copy frames of P = M[n-1] (r <= i, le1 P r i, counted child c with the state B before c),
levels u in LevAt P i with u <= V:  every g in comps u V' is <= Omega_{f a}, <= sigma B, or <= a component of f(a).
VDu: the same without the sigma B alternative (VDomF at the level u).  One process."""
import sys, json, collections
for p in ['/home/koteitan/proofs/trio/tmp/claude', '/home/koteitan/proofs/trio/tools',
          '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b',
          '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD']:
    sys.path.insert(0, p)
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx, Z, lt, le, comps
from vracopy import sh, shf, frames
import probe_t2vra_esc as E
import trio, ytosk_eval as Y
from pv2 import load
T = Y.tstr


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
        _, pP = frames(CP)
        V = CP.v(r); V2 = CN.v(r + L)
        for i in range(r, len(P)):
            if not E.le1(CP, r, i): continue
            cl = CP.CL(i)
            a = CP.v(i); fa = shf(V, V2, a)
            for idx, c in enumerate(cl):
                B = CP.pre(i, cl[:idx]); sB = sh(V, V2, B)
                for u in pP[i] | {a}:
                    if not le(u, V): continue
                    cfa = comps(u, fa)
                    cnt['cases'] += 1
                    bad = [g for g in comps(u, V2) if not (le(g, (fa, Z, Z)) or any(le(g, d) for d in cfa))]
                    if bad: cnt['VDu.failures'] += 1
                    bad2 = [g for g in bad if not le(g, sB)]
                    if bad2:
                        cnt['VDomU.failures'] += 1
                        if 'VDomU' not in ex or len(M) < len(ex['VDomU']['matrix']):
                            ex['VDomU'] = dict(matrix=M, n=n, i=i, c=c, u=T(u), V=T(V), V2=T(V2), a=T(a),
                                               fa=T(fa), B=T(B), bad=[T(g) for g in bad2])
    return cnt, ex


if __name__ == '__main__':
    sets = [f for f in json.load(open('/home/koteitan/proofs/trio/tmp/codex/inv3v3_inputs_sets_20261101.json'))
            if f.split('/')[-1] in sys.argv[1:]]
    tot = collections.Counter(); exs = {}
    for f in sets:
        for m in load(f):
            c, e = measure(m); tot.update(c)
            for k, v in e.items():
                if k not in exs or len(v['matrix']) < len(exs[k]['matrix']): exs[k] = v
        print(f.split('/')[-1], json.dumps(dict(tot)), flush=True)
    print('FINAL', json.dumps(dict(tot))); print('EX', json.dumps(exs, default=str))
