"""WfCofL graft family around the diagonal-type (t = 1) cases where the seed bound is tight
(gamma_1 > Y_2: the chain starts one step behind) or the engine bound is strict at n = 2,
and around the counting-type (t = 0, 2) cases with m_2 = 0 (tight base).

usage: nice -n 15 python3 graftG.py OUT.pkl NSEED PKL...
Same generator as WfCof/graftF.py (WfReM graft.gen_all + WfInvD extra, gen 1 + 300-sample gen 2, bms -s = 1, < SRO).
"""
import sys, pickle, random
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfReM')
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfInvD')
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfCofL')
import graft as G
from graftD import gen
from multiprocessing import Pool
from probe import *

def kind(A):
    vA = val(A)
    if vA is None or A[-1] == (0, 0, 0): return None
    p = path(vA)
    if p is None: return 'nopath'
    vs = {}
    for n in (2,):
        N = [tuple(c) for c in trio.expand([list(c) for c in A], n)]
        try:
            ev = Y.Ev(N); tN = ev.value()
        except RecursionError:
            return None
        if tN is None: return None
        if p[0] == 'diag':
            Yn = Y.sf(ev.o(len(A) - 1))
            if not le(gam(p[3], p[2], 1), Yn): return 'diag_tight'
            if fsD(vA, Yn) != tN: return 'diag_strict'
        else:
            if not le(fsD(vA, natT(1)), tN): return 'succ_tight'
    return None

if __name__ == '__main__':
    out, ns = sys.argv[1], int(sys.argv[2])
    cand = []
    for pk in sys.argv[3:]:
        d = pickle.load(open(pk, 'rb'))
        random.seed(5)
        if len(d) > 20000: d = random.sample(list(d), 20000)
        cand += [tuple(tuple(c) for c in A) for A in d]
    cand = sorted(set(cand), key=lambda A: (len(A), A))
    seeds = {'diag_tight': [], 'diag_strict': [], 'succ_tight': [], 'nopath': []}
    for A in cand:
        k = kind(A)
        if k and len(seeds[k]) < ns: seeds[k].append(A)
        if all(len(v) >= ns for k_, v in seeds.items() if k_ != 'nopath'): break
    print({k: len(v) for k, v in seeds.items()}, flush=True)
    seeds = [A for v in seeds.values() for A in v]
    base = set()
    for A in seeds:
        for n in (2, 3):
            N = tuple(tuple(c) for c in trio.expand([list(c) for c in A], n))
            for j in range(4, len(N) + 1): base.add(N[:j])
        for j in range(4, len(A) + 1): base.add(A[:j])
    print('seeds', len(seeds), 'bases', len(base), flush=True)
    g1 = set()
    with Pool(2) as p:
        for o in p.imap_unordered(gen, sorted(base)): g1 |= o
        print('gen1', len(g1), flush=True)
        random.seed(13); s2 = random.sample(sorted(g1), min(300, len(g1)))
        g2 = set()
        for o in p.imap_unordered(gen, s2): g2 |= o
    allN = sorted(g1 | g2 | set(seeds) | base)
    print('total', len(allN), flush=True)
    pickle.dump([list(N) for N in allN], open(out, 'wb'))
