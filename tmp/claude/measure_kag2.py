"""KG' = KG with a third alternative, on the sets where KG failed (graft2/4/5/D/E):
  KG' : V < s -> forall g in compsAN V u (sub s V), g <= Omega_s or g <= B or exists d in compsAN V u (sub a V), g <= d.
Also KGc: the third alternative with d in comps u a (weaker).  Frames and levels as tools/probe_t2vrak.py."""
import sys, json, collections
from multiprocessing import Pool
for p in ['/home/koteitan/proofs/trio/tools', '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b',
          '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD']:
    sys.path.insert(0, p)
import probe_t2vrak as K
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx, Z, lt, le, comps
from vracopy import frames
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
        _, pP = frames(CP)
        V = CP.v(r)
        for i in range(r, len(P)):
            if not K.le1(CP, r, i): continue
            a = CP.v(i); cl = CP.CL(i)
            for idx, c in enumerate(cl):
                s, y, tail = CP.o(c)
                if tail != Z or not lt(V, s): continue
                B = CP.pre(i, cl[:idx])
                for u in pP[i] | {a}:
                    if not le(u, V): continue
                    cnt['KG.cases'] += 1
                    bad = [g for g in K.compsA(V, u, Y.sub(s, V)) if not (le(g, (s, Z, Z)) or le(g, B))]
                    if not bad: continue
                    cnt['KG.failures'] += 1
                    dA = K.compsA(V, u, Y.sub(a, V)) if le(V, a) else []
                    dC = comps(u, a)
                    if not all(any(le(g, d) for d in dA) for g in bad):
                        cnt["KG'.failures"] += 1
                        if "KG'" not in ex or len(M) < len(ex["KG'"]['matrix']):
                            ex["KG'"] = {'matrix': M, 'n': n, 'i': i, 'c': c, 'u': Y.tstr(u)}
                    if not all(any(le(g, d) for d in dC) for g in bad):
                        cnt['KGc.failures'] += 1
                    if 'KG' not in ex or len(M) < len(ex['KG']['matrix']):
                        ex['KG'] = {'matrix': M, 'n': n, 'i': i, 'c': c, 'u': Y.tstr(u)}
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
