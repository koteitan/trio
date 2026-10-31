"""WfCof graft family around the worst EvalFS cases (deficit 2).

usage: nice -n 15 python3 graftF.py OUT.pkl NSEED PKL...
Seeds: up to NSEED smallest matrices of PKL with a nonzero last column whose deficit
def(n) = n - L(n) reaches 2 at some n >= 2 (NMAX 4), plus their M[2], M[3] and all their prefixes of length >= 4.
Gen 1 (each seed / prefix) and gen 2 (sample of 300 gen-1): WfReM graft.gen_all (child of each column with row 1
up to e1 + 2, row 2 in {0,1}, first/last child; mutations; append) + WfInvD extra (row-1 lift to 4..6, larger
sibling before x - 1). Kept: bms -s = 1 and < SRO (graft.keep).
"""
import sys, pickle, random
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfReM')
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfInvD')
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfCof')
import graft as G
from graftD import gen
from multiprocessing import Pool
from fsprobe import *

def worst(A):
    vA = val(A)
    if vA is None or A[-1] == (0, 0, 0): return False
    fk = [fs(vA, k) for k in range(8)]
    for n in range(2, 5):
        vN = val([tuple(x) for x in trio.expand([list(x) for x in A], n)])
        if vN is None: return False
        L = max([k for k in range(8) if le(fk[k], vN)], default=-1)
        if n - L >= 2: return True
    return False

if __name__ == '__main__':
    out, ns = sys.argv[1], int(sys.argv[2])
    cand = []
    for pk in sys.argv[3:]:
        d = pickle.load(open(pk, 'rb'))
        random.seed(3)
        if len(d) > 20000: d = random.sample(list(d), 20000)
        cand += [tuple(tuple(c) for c in A) for A in d]
    cand = sorted(set(cand), key=lambda A: (len(A), A))
    seeds = []
    for A in cand:
        if worst(A): seeds.append(A)
        if len(seeds) >= ns: break
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
        random.seed(11); s2 = random.sample(sorted(g1), min(300, len(g1)))
        g2 = set()
        for o in p.imap_unordered(gen, s2): g2 |= o
    allN = sorted(g1 | g2 | set(seeds) | base)
    print('total', len(allN), flush=True)
    pickle.dump([list(N) for N in allN], open(out, 'wb'))
