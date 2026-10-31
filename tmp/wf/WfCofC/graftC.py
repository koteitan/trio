"""WfCofC graft family around the new residuals (HCntPath0, HCntRoot2, HDiagLoc/HDiagStep).
Seeds: t = 0 with Rt < r and fsD(o_A(Rt), 0) = o_{A[2]}(Rt) ('t0_tight'); t = 2 with the same equality at Rt
('t2_tight'); diagonal type whose point in tA has a subscript different from mu ('diag_sub').
usage: nice -n 15 python3 graftC.py OUT.pkl NSEED PKL...   (generator: WfInvD graftD.gen, gen 1 + 300-sample gen 2)
"""
import sys, pickle, random
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfReM')
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfInvD')
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfCofL')
from graftD import gen
from multiprocessing import Pool
from probe import *

def natT(k):
    t = Z
    for _ in range(k): t = (Z, Z, t)
    return t

def kind(A):
    if A[-1] == (0, 0, 0): return None
    try:
        vA = val(A)
        if vA is None: return None
        p = path(vA)
        if p is None: return None
        t = ttype(A); x = len(A) - 1; r = badroot(A)
        evA = Y.Ev(list(A)); evA.value()
        Rt = max(c for c in range(x + 1) if A[c] == (0, 0, 0))
        if p[0] == 'diag':
            return 'diag_sub' if p[1] != p[3] else None
        if t == 1 or (t == 0 and Rt == r): return None
        N = [tuple(c) for c in trio.expand([list(c) for c in A], 2)]
        ev = Y.Ev(N); ev.value()
        if fsD(Y.sf(evA.o(Rt)), natT(0)) == Y.sf(ev.o(Rt)): return 't%d_tight' % t
    except RecursionError:
        return None
    return None

if __name__ == '__main__':
    out, ns = sys.argv[1], int(sys.argv[2])
    cand = []
    for pk in sys.argv[3:]:
        d = pickle.load(open(pk, 'rb'))
        random.seed(5)
        if len(d) > 5000: d = random.sample(list(d), 5000)
        cand += [tuple(tuple(c) for c in A) for A in d]
    cand = sorted(set(cand), key=lambda A: (len(A), A))
    seeds = {'diag_sub': [], 't0_tight': [], 't2_tight': []}
    for A in cand:
        if len(A) < 2: continue
        k = kind(A)
        if k and len(seeds[k]) < ns: seeds[k].append(A)
        if all(len(v) >= ns for v in seeds.values()): break
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
