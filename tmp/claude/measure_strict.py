"""The k-free seed fields (V3RwFree.lean) on the 86 sets below SRO, with T = M.take x, X1 = state of r in T,
sigma = sigma_{V, V'}:
  sv (q = r, upg(x-1) = x, V' = V + 1): T2SVStrict  X1 < sigma X1
  C1 (q != r, CL_M(r) not ending with q, upg(x-1) = none, V' = qnS): CRelR2.strict  X1 < sigma X1,
     CRelR2.hi  the summands of sigma X1 are not below Omega_{qnS + 1}."""
import sys, json, collections
from multiprocessing import Pool
for p in ['/home/koteitan/proofs/trio/tmp/claude', '/home/koteitan/proofs/trio/tools',
          '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b',
          '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD']:
    sys.path.insert(0, p)
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx, Z, ONE, lt, sumN, spa, summ, succ
from vracopy import sh
import ytosk_eval as Y
from pv2 import load


def measure(m):
    M = list(map(tuple, m)); cnt = collections.Counter(); ex = {}
    if not M < SRO: return cnt, ex
    x = len(M) - 1
    if x < 1 or M[x][2] == 0: return cnt, ex
    C = Ctx(M)
    if not C.ok: return cnt, ex
    r = C.e.par(2, x); q = C.e.par(0, x)
    if r is None or q is None: return cnt, ex
    T = None
    def state():
        Tc = Ctx(M[:-1])
        if not Tc.ok: return None
        return spa(Tc.v(r), sumN([Tc.o(d) for d in Tc.CL(r)]))
    V = C.v(r)
    if q == r:
        if C.upg(x - 1) != x: return cnt, ex
        X1 = state()
        if X1 is None: cnt['T_failed'] += 1; return cnt, ex
        cnt['sv.cases'] += 1
        if not lt(X1, sh(V, succ(V), X1)):
            cnt['sv.failures'] += 1
            ex['sv'] = dict(matrix=M, r=r, X1=Y.tstr(X1))
        return cnt, ex
    cl = C.CL(r)
    if (cl and cl[-1] == q) or C.upg(x - 1) is not None: return cnt, ex
    X1 = state()
    if X1 is None: cnt['T_failed'] += 1; return cnt, ex
    S = Y.add(V, Y.omega(sumN([ONE] + [C.bumpTerm(q, d) for d in C.ch(q) if d < x])))
    sX = sh(V, S, X1)
    cnt['C.cases'] += 1
    if not lt(X1, sX):
        cnt['C.strict.failures'] += 1
        ex['C.strict'] = dict(matrix=M, r=r, q=q, X1=Y.tstr(X1))
    th = (succ(S), Z, Z)
    if any(lt(g, th) for g in summ(sX)):
        cnt['C.hi.failures'] += 1
        ex['C.hi'] = dict(matrix=M, r=r, q=q, X1=Y.tstr(X1))
    return cnt, ex


if __name__ == '__main__':
    sets = json.load(open('/home/koteitan/proofs/trio/tmp/codex/inv3v3_inputs_sets_20261101.json'))
    tot = collections.Counter(); exs = {}
    with Pool(4) as pool:
        for f in sets:
            for c, e in pool.imap_unordered(measure, load(f), chunksize=200):
                tot.update(c)
                for k, v in e.items():
                    if k not in exs or len(v['matrix']) < len(exs[k]['matrix']): exs[k] = v
            print(f.split('/')[-1], json.dumps(dict(tot)), flush=True)
    print('FINAL', json.dumps(dict(tot))); print('EX', json.dumps(exs, default=str))
