"""B'>0 trigger cases at qr frames: shape statistics (|L'|, col d vs col c, arg of B', relation of B' to y)."""
import sys, json, collections
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
    c = cl[-2]; oM = C.o(c); a = C.v(r)
    Bp = spa(a, sumN([C.o(d) for d in cl[:-2]]))
    if Bp == Z or not (lt(Bp, oM[1]) and lt((a, Z, Z), (oM[0], oM[1], Z))): return cnt, ex
    cnt['cases'] += 1
    Lp = cl[:-2]
    cnt['lenL=%d' % min(len(Lp), 3)] += 1
    d = Lp[-1]
    cnt['col_d==col_c=%s' % (M[d] == M[c])] += 1
    cnt['B_single=%s' % (Bp[2] == Z)] += 1
    cnt['B_arg0=%s' % (Bp[1] == Z)] += 1
    cnt['B==o(d)=%s' % (Bp == C.o(d))] += 1
    y = oM[1]
    cnt['headsub_y==sub_B=%s' % (y[0] == Bp[0])] += 1
    cnt['v(d)==headsub_y=%s' % (C.v(d) == y[0])] += 1
    k = 'shape'
    if Bp[1] != Z and (k not in ex or len(M) < len(ex[k]['matrix'])):
        ex[k] = dict(matrix=''.join('(%d,%d,%d)' % t for t in M), r=r, c=c, L=Lp, B=Y.tstr(Bp), y=Y.tstr(y))
    return cnt, ex
if __name__ == '__main__':
    from multiprocessing import Pool
    sets = json.load(open('/home/koteitan/proofs/trio/tmp/codex/inv3v3_inputs_sets_20261101.json'))
    names = sys.argv[1:]
    tot = collections.Counter(); exs = {}
    with Pool(2) as pool:
        for f in sets:
            if names and f.split('/')[-1] not in names: continue
            for c, e in pool.imap_unordered(measure, load(f), chunksize=200):
                tot.update(c)
                for k, v in e.items():
                    if k not in exs or len(v['matrix']) < len(exs[k]['matrix']): exs[k] = v
            print(f.split('/')[-1], json.dumps(dict(tot)), flush=True)
    print('FINAL', json.dumps(dict(tot)))
    for k, v in exs.items(): print('EX', k, json.dumps(v))
