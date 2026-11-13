"""QRNoSwitch: classify o_T(c) vs o_M(c) at the qr frames (t = 2, q = r, no upgrade to x, CL_M(r) = L' ++ [c] ++ [x])."""
import sys, json, collections
from multiprocessing import Pool
for p in ['/home/koteitan/proofs/trio/tmp/claude', '/home/koteitan/proofs/trio/tools',
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
    if not cl or len(cl) < 2 or cl[-1] != x: return cnt, ex
    T = Ctx(M[:-1])
    if not T.ok: return cnt, ex
    c = cl[-2]
    oT, oM = T.o(c), C.o(c)
    a = C.v(r)
    Bp = spa(a, sumN([C.o(d) for d in cl[:-2]]))
    trig = lambda o: lt(Bp, o[1]) and lt((a, Z, Z), (o[0], o[1], Z))
    if not trig(oM): return cnt, ex
    cnt['cases'] += 1
    cnt['yT0' if oT[1] == Z else 'yTpos'] += 1
    cnt['B0' if Bp == Z else 'Bpos'] += 1
    if Bp != Z:
        k2 = 'Bpos.' + ('eq' if oT == oM else 'neq')
        cnt[k2] += 1
        cnt['Bpos.trigT=%s' % trig(oT)] += 1
        if True:
            hy, hy2 = oM[1][:2], oT[1][:2]
            cnt['Bpos.neq.head_same=%s' % (Y.tstr((hy[0], hy[1], Z)) == Y.tstr((hy2[0], hy2[1], Z)))] += 1
            if k2 not in ex or len(M) < len(ex[k2]['matrix']):
                ex[k2] = dict(matrix=M, r=r, c=c, B=Y.tstr(Bp), oT=Y.tstr(oT), oM=Y.tstr(oM))
        return cnt, ex
    u = C.upg(x - 1)
    return cnt, ex
    k = 'eq' if oT == oM else ('samesub' if oT[0] == oM[0] else 'diffsub')
    cnt[k] += 1
    cnt['upg(x-1)=%s' % ('none' if u is None else ('in_c' if c <= u < x else 'other'))] += 1
    if k != 'eq':
        cnt[k + '.upg=%s' % ('none' if u is None else ('in_c' if c <= u < x else 'other'))] += 1
        if k not in ex or len(M) < len(ex[k]['matrix']):
            ex[k] = dict(matrix=M, r=r, c=c, u=u, oT=Y.tstr(oT), oM=Y.tstr(oM))
    return cnt, ex

if __name__ == '__main__':
    sets = json.load(open('/home/koteitan/proofs/trio/tmp/codex/inv3v3_inputs_sets_20261101.json'))
    n = int(sys.argv[1]) if len(sys.argv) > 1 else len(sets)
    tot = collections.Counter(); exs = {}
    with Pool(4) as pool:
        for f in sets[:n]:
            for c, e in pool.imap_unordered(measure, load(f), chunksize=200):
                tot.update(c)
                for k, v in e.items():
                    if k not in exs or len(v['matrix']) < len(exs[k]['matrix']): exs[k] = v
            print(f.split('/')[-1], json.dumps(dict(tot)), flush=True)
    print('FINAL', json.dumps(dict(tot))); print('EX', json.dumps(exs, default=str))
