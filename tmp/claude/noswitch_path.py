"""At B'>0 trigger qr frames with o_T(c) != o_M(c): where do (B', y) and (y', y) first differ (DFS order sub, arg, rest)?"""
import sys, json, collections
for p in ['/home/koteitan/proofs/trio/tmp/claude', '/home/koteitan/proofs/trio/tools',
          '/home/koteitan/proofs/trio/tmp/wf/WfDrE', '/home/koteitan/proofs/trio/tmp/wf/WfInvD']:
    sys.path.insert(0, p)
from probe_inv2 import SRO
from probe_inv3_prefix import Ctx, Z, lt, sumN, spa
import ytosk_eval as Y
from pv2 import load
def diff(a, b, path=()):
    """first DFS position where a and b differ; returns (path, kind)"""
    if a == b: return None
    if a == Z or b == Z: return (path, 'z')
    for i, nm in enumerate('sar'):
        if a[i] != b[i]: return diff(a[i], b[i], path + (nm,))
    return None
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
    c = cl[-2]; oT, oM = T.o(c), C.o(c); a = C.v(r)
    Bp = spa(a, sumN([C.o(d) for d in cl[:-2]]))
    if Bp == Z or not (lt(Bp, oM[1]) and lt((a, Z, Z), (oM[0], oM[1], Z))) or oT == oM: return cnt, ex
    y, y2 = oM[1], oT[1]
    p1, k1 = diff(Bp, y); p2, k2 = diff(y2, y)
    cnt['cases'] += 1
    # is p1 strictly before p2 in DFS order, with p2 not a prefix of p1?
    pre = p2[:len(p1)] == p1 and len(p2) > len(p1)
    rel = 'p2_prefix_of_p1' if p1[:len(p2)] == p2 else ('p1_prefix_of_p2' if pre else 'disjoint')
    order = {'s': 0, 'a': 1, 'r': 2}
    if rel == 'disjoint':
        i = next(i for i in range(min(len(p1), len(p2))) if p1[i] != p2[i])
        rel += '.p1_first' if order[p1[i]] < order[p2[i]] else '.p2_first'
    cnt['rel=' + rel] += 1
    cnt['k1=' + k1 + ('.Bz' if k1 == 'z' else '')] += 1
    key = rel
    if key not in ex or len(M) < len(ex[key]['matrix']):
        ex[key] = dict(matrix=''.join('(%d,%d,%d)' % t for t in M), p1=''.join(p1), p2=''.join(p2), B=Y.tstr(Bp), y=Y.tstr(y), y2=Y.tstr(y2))
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
