"""WfQrO graft family against PreG / LastG: seeds = q = r matrices whose triggered-arg frame has PreB false
(pre > init y: the first difference is below the top level) taken from graftH.pkl and famframes.pkl (second generation),
generator = WfInvD graftD.gen (as graftH.py), gen 1 + 200-sample gen 2, bms -s = 1, < SRO.
usage: nice -n 15 python3 graftO.py OUT.pkl NSEED PKL..."""
import sys, pickle, random, collections
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfReM')
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfInvD')
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfQrO')
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
from graftD import gen
import trio
import og as OG
from multiprocessing import Pool
def kind(A):
    M=[tuple(c) for c in A];cnt=collections.Counter()
    try:OG.check(M,cnt,{})
    except Exception:return False
    return cnt['PreB.old.FAIL']>0
if __name__ == '__main__':
    out, ns = sys.argv[1], int(sys.argv[2])
    cand = []
    for pk in sys.argv[3:]:
        d = pickle.load(open(pk, 'rb'))
        random.seed(7)
        if len(d) > 3000: d = random.sample(list(d), 3000)
        cand += [tuple(tuple(c) for c in A) for A in d]
    random.seed(11); random.shuffle(cand)
    seeds = []
    for A in cand:
        if kind(A): seeds.append(A)
        if len(seeds) >= ns: break
    base = set()
    for A in seeds:
        for n in (2, 3):
            N = tuple(tuple(c) for c in trio.expand([list(c) for c in A], n))
            for j in range(max(4, len(N) - 2), len(N) + 1): base.add(N[:j])
        for j in range(max(4, len(A) - 2), len(A) + 1): base.add(A[:j])
    print('seeds', len(seeds), 'bases', len(base), flush=True)
    g1 = set()
    with Pool(2) as p:
        for o in p.imap_unordered(gen, sorted(base)): g1 |= o
        print('gen1', len(g1), flush=True)
        random.seed(13); s2 = random.sample(sorted(g1), min(200, len(g1)))
        g2 = set()
        for o in p.imap_unordered(gen, s2): g2 |= o
    allN = sorted(g1 | g2 | set(seeds) | base)
    print('total', len(allN), flush=True)
    pickle.dump([list(N) for N in allN], open(out, 'wb'))
