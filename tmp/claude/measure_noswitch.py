"""QRNoSwitch (V3QRW1.lean) at the qr configurations of the 86 sets below SRO (t = 2, q = r, no upgrade to x,
CL_M(r) = L' ++ [c] ++ [x]): if M triggers at c with the state B' before c, so does M.take x."""
import sys, json, collections
from multiprocessing import Pool
for p in ['/home/koteitan/proofs/trio/tmp/claude', '/home/koteitan/proofs/trio/tools',
          '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b',
          '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD']:
    sys.path.insert(0, p)
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx, Z, lt, sumN, spa
import ytosk_eval as Y
from pv2 import load


def measure(m):
    M = list(map(tuple, m)); cnt = collections.Counter(); ex = {}
    if not M < SRO: return cnt, ex
    x = len(M) - 1
    if x < 1 or M[x][2] == 0: return cnt, ex
    C = Ctx(M)
    if not C.ok: return cnt, ex
    r = C.e.par(2, x)
    if r is None or C.e.par(0, x) != r: return cnt, ex
    if any(C.upg(i) == x for i in range(x)): return cnt, ex
    cl = C.CL(r)
    if not cl or cl[-1] != x: return cnt, ex
    cnt['qr.frames'] += 1
    if len(cl) < 2: return cnt, ex
    T = Ctx(M[:-1])
    if not T.ok: cnt['T_failed'] += 1; return cnt, ex
    c = cl[-2]; a = C.v(r)
    Bp = spa(a, sumN([C.o(d) for d in cl[:-2]]))
    oT, oM = T.o(c), C.o(c)
    trig = lambda o: lt(Bp, o[1]) and lt((a, Z, Z), (o[0], o[1], Z))
    cnt['cases'] += 1
    if trig(oM):
        cnt['trigM'] += 1
        if not trig(oT):
            cnt['failures'] += 1
            ex['switch'] = dict(matrix=M, r=r, c=c, oT=Y.tstr(oT), oM=Y.tstr(oM), B=Y.tstr(Bp))
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
