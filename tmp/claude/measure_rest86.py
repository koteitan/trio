"""More residuals on all 86 sets (below SRO):
  leaf : TP1LeafG, TP1WLeafG (HFrameV3, V3TP1CutG.lean) at every frame of every matrix (tools/probe_leafg.py).
  QNDom: T2VRAQNDom (V3T2VRASeed.lean) at the qn configurations (t = 2, q != r, CL_M(r) = Lc ++ [q]):
         u in LevAt M rho r, u <= v(r): every g in comps u qnS is <= Omega_qnS, <= t2B v(r) Lc, or <= a component of v(r).
  SeedC: T2VRASeedC (V3T2VRASV.lean) at the C configurations (q != r, CL_M(r) not ending with q), n = 2, 3:
         QVRAt at every counted child frame of r in N = M[n], every u in LevAt N sigma r.
  C2Q  : T2C2QKids (V3VRASeedU.lean) at the C2 configurations (upg M (x-1) != none): CL_N(q) = [x], v_N(x) = v_N(q)."""
import sys, json, collections
from multiprocessing import Pool
for p in ['/home/koteitan/proofs/trio/tmp/claude', '/home/koteitan/proofs/trio/tools',
          '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b',
          '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD']:
    sys.path.insert(0, p)
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx, Z, ONE, lt, le, comps, spa, sumN
from vracopy import frames
import probe_t2vra_esc as E
import probe_leafg as LF
import trio, ytosk_eval as Y
from pv2 import load


def keep(ex, key, M, info):
    if key not in ex or len(M) < len(ex[key]['matrix']): ex[key] = dict(matrix=M, **info)


def measure(matrix):
    M = list(matrix); cnt = collections.Counter(); ex = {}
    if not M < SRO: return cnt, ex
    c1, e1 = LF.measure(M)
    for k, v in c1.items():
        if k.startswith('TP1'): cnt['leaf.' + k] += v
    for k, v in e1.items():
        if k.startswith('TP1'): keep(ex, 'leaf.' + k, M, {})
    x = len(M) - 1
    if x < 1 or M[x][2] == 0: return cnt, ex
    C = Ctx(M)
    if not C.ok: return cnt, ex
    r = C.e.par(2, x); q = C.e.par(0, x)
    if r is None or q is None or q == r: return cnt, ex
    clM = C.CL(r); vr = C.v(r)
    if clM and clM[-1] == q:
        fM, pM = frames(C)
        Sq = Y.add(vr, Y.omega(sumN([ONE] + [C.bumpTerm(q, d) for d in C.ch(q) if d < x])))
        B = spa(vr, sumN([C.o(d) for d in clM[:-1]]))
        cnt['QNDom.frames'] += 1
        for u in pM[r] | {vr}:
            if lt(vr, u): continue
            cv = comps(u, vr)
            for g in comps(u, Sq):
                if not (le(g, (Sq, Z, Z)) or le(g, B) or any(le(g, d) for d in cv)):
                    cnt['QNDom.failures'] += 1; keep(ex, 'QNDom', M, dict(u=Y.tstr(u))); break
        return cnt, ex
    c2 = C.upg(x - 1) is not None
    cnt['C.frames'] += 1; cnt['C2.frames'] += c2
    for n in (2, 3):
        N = trio.expand(M, n); CN = Ctx(N)
        if not CN.ok: cnt['eval_failed_N'] += 1; continue
        fN, pN = frames(CN)
        a = CN.v(r); cl = CN.CL(r)
        for idx, c in enumerate(cl):
            Bc = CN.pre(r, cl[:idx]); cv = CN.o(c)
            for u in pN[r] | {a}:
                cnt['SeedC.cases'] += 1
                if not E.qvrat(a, Bc, cv, u):
                    cnt['SeedC.failures'] += 1; keep(ex, 'SeedC', M, dict(n=n, c=c, u=Y.tstr(u), c2=c2))
        if c2:
            cnt['C2Q.cases'] += 1
            if not (CN.CL(q) == [x] and CN.v(x) == CN.v(q)):
                cnt['C2Q.failures'] += 1; keep(ex, 'C2Q', M, dict(n=n))
    return cnt, ex


if __name__ == '__main__':
    sets = json.load(open('/home/koteitan/proofs/trio/tmp/codex/inv3v3_inputs_sets_20261101.json'))
    if len(sys.argv) > 1: sets = [f for f in sets if f.split('/')[-1] in sys.argv[1:]]
    tot = collections.Counter(); exs = {}
    with Pool(4) as pool:
        for f in sets:
            for c, e in pool.imap_unordered(measure, load(f), chunksize=100):
                tot.update(c)
                for k, v in e.items():
                    if k not in exs or len(v['matrix']) < len(exs[k]['matrix']): exs[k] = v
            print(f.split('/')[-1], json.dumps(dict(tot)), flush=True)
    print('FINAL', json.dumps(dict(tot))); print('EX', json.dumps(exs, default=str))
