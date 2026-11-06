"""CopyEsc2 = T2VRACopyEsc with the extra premise "g is not below a component of v_N(i + L)" (the third alternative of
QVRAt in N), and VDK (T2CopyK CopyVDomK) with examples, on the given sets (one process)."""
import sys, json, collections
for p in ['/home/koteitan/proofs/trio/tmp/claude', '/home/koteitan/proofs/trio/tools',
          '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b',
          '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD']:
    sys.path.insert(0, p)
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx, Z, lt, le, comps, split, succ
from vracopy import sh, shf, frames
from lhd_exact import indices
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
        fN, pN = frames(CN); fP, pP = frames(CP)
        V = CP.v(r); V2 = CN.v(r + L)
        for (k, c, B, s, y) in fN:
            i = k - L
            if i < r or i >= len(P): continue
            if split(y, (succ(s), Z, Z))[0] == Z: continue
            aN = CN.v(k); UP = pP[i] | {CP.v(i)}
            for u in pN[k] | {aN}:
                if lt(aN, u): continue
                hard = [g for g in comps(u, s) if lt((s, Z, Z), g) and lt(B, g)]
                if not hard: continue
                cnt['Esc.cases'] += 1
                ok = u in UP and le(u, V)
                if not ok: cnt['Esc.failures'] += 1
                ca = comps(u, aN)
                hard2 = [g for g in hard if not any(le(g, d) for d in ca)]
                if hard2:
                    cnt['Esc2.cases'] += 1
                    if not ok:
                        cnt['Esc2.failures'] += 1
                        if 'Esc2' not in ex: ex['Esc2'] = dict(matrix=M, n=n, i=i, k=k, c=c, u=T(u), V=T(V),
                                                                aN=T(aN), s=T(s), B=T(B), g=[T(g) for g in hard2])
        for i in range(r, len(P)):
            if not E.le1(CP, r, i) or not CP.CL(i): continue
            a = CP.v(i); fa = shf(V, V2, a)
            us = {Z}; indices(V2, us); indices(fa, us)
            for u in us:
                if lt(fa, u): continue
                cfa = comps(u, fa)
                bad = [g for g in comps(u, V2) if not (le(g, (fa, Z, Z)) or any(le(g, d) for d in cfa))]
                if bad:
                    cnt['VDK.failures'] += 1
                    if 'VDK' not in ex or len(M) < len(ex['VDK']['matrix']):
                        ex['VDK'] = dict(matrix=M, n=n, i=i, P_i=P[i], u=T(u), V=T(V), V2=T(V2), a=T(a), fa=T(fa),
                                         bad=[T(g) for g in bad], cl=CP.CL(i))
                    break
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
