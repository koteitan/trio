"""Bad2 (exact, t = 2 first disjunct) and qn: the shape of q's subtree before x.
Counts by (simple, weak, g==q, |children q before x|, |children p|, k<x-1)."""
import sys, json, time
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfScout')
from probe_inv3_prefix import Ctx, Z
from lhd_exact import lhd, lhdE, lt
from qndom import load, mt
import ytosk_eval as Y
SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]
def summ(t):
    out = []
    while t: out.append((t[0], t[1], Z)); t = t[2]
    return out
def strong(C, x):
    i = x - 1; k = C.upg(i)
    if k is None: return True
    V = C.vOpt1(i); vk = C.v(k); W = vk
    while W:
        if Y.add(V, W) == vk and any(lt(q, W) and not lhd(q, W) for q in summ(V)): return False
        W = W[2]
    return True
def anc(C, a, b):
    while b is not None:
        if a == b: return True
        b = C.e.par(0, b)
    return False
def go(m):
    cnt = Counter(); ex = []
    M = [tuple(c) for c in m]
    if not M < SRO or len(M) < 4 or M[-1][2] == 0: return cnt, ex
    x = len(M) - 1
    C = Ctx(M)
    if not C.ok: return cnt, ex
    r = C.e.par(2, x); q = C.e.par(0, x)
    if r is None or q is None or q == r: return cnt, ex
    cl = [d for d in C.ch(r) if C.counted(r, d)]
    if not cl or cl[-1] != q: return cnt, ex
    k = C.upg(x - 1)
    if k is None: return cnt, ex
    p = C.e.par(0, x - 1)
    if p is None: return cnt, ex
    g = C.e.par(0, p)
    if g is None or M[p] != C.e.bump(g): return cnt, ex
    cnt['struct'] += 1; cnt[('struct_g=q', g == q, 'k<x-1', k < x - 1)] += 1
    if strong(C, x): return cnt, ex
    cnt['bad2'] += 1
    T = Ctx(M[:-1])
    weak = not lhdE(T.v(q), C.v(q))
    chq = [d for d in C.ch(q) if d < x]
    simple = len(chq) == 1 and chq[0] == p and C.ch(p) == [x - 1] and k < x - 1
    key = ('simple', simple, 'weak', weak, 'g=q', g == q, 'nq', len(chq), 'np', len(C.ch(p)), 'k<x-1', k < x - 1)
    cnt[key] += 1
    if not simple and len(ex) < 2: ex.append((mt(M), r, q, p, g, k))
    return cnt, ex
if __name__ == '__main__':
    for nm in sys.argv[1:]:
        t = time.time(); mats = load(nm)
        tot = Counter(); exs = []
        with Pool(4) as pl:
            for c, ex in pl.imap_unordered(go, mats, chunksize=200):
                tot.update(c); exs += ex[:max(0, 5 - len(exs))]
        res = {'n': len(mats), 'counts': {str(k): v for k, v in tot.items()}, 'examples': exs, 'sec': time.time() - t}
        print(nm, json.dumps(res), flush=True)
