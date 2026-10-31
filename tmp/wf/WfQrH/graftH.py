"""WfQrH graft family around the q = r frames that exercise the WfQrH fields:
 trigsub : triggered argument o frame whose last summand changes subscript (PreB false; TrigN not from pre <= init y)
 leafpar : leaf-parent frame triggered in M[n]
 qnz     : a DQ with a non-empty re-exposed Q (C_strip / OT_Q / OT_S are not vacuous)
Bases = seeds, M[2], M[3] and their prefixes ending at the last 3 columns; generator = WfInvD graftD.gen (as WfCofL/graftG.py),
gen 1 + 300-sample gen 2, bms -s = 1, < SRO.  Output: all generated matrices (filter q = r frames when measuring).
usage: nice -n 15 python3 graftH.py OUT.pkl NSEED PKL..."""
import sys, pickle, random, collections
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfReM')
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfInvD')
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfQrH')
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
from graftD import gen
import trio
import oframe as OF
import compq2 as CQ
from multiprocessing import Pool
def kinds(A):
    M=[tuple(c) for c in A];cnt=collections.Counter();ex={}
    try:OF.check(M,cnt,ex)
    except Exception:return set()
    k=set()
    if cnt['PreB.FAIL']:k.add('trigsub')
    if cnt['Leaf.leafpar.ok']:k.add('leafpar')
    if cnt['TrigN.ok'] and not cnt['PreB.FAIL']:pass
    c2=collections.Counter()
    try:CQ.check(M,c2,{})
    except Exception:pass
    if c2['OT_Q.ok']:k.add('qnz')
    return k
if __name__ == '__main__':
    out, ns = sys.argv[1], int(sys.argv[2])
    cand = []
    for pk in sys.argv[3:]:
        d = pickle.load(open(pk, 'rb'))
        random.seed(5)
        if len(d) > 3000: d = random.sample(list(d), 3000)
        cand += [tuple(tuple(c) for c in A) for A in d]
    cand = sorted(set(cand), key=lambda A: (len(A), A))
    seeds = {'trigsub': [], 'leafpar': [], 'qnz': []}
    for A in cand:
        for k in kinds(A):
            if len(seeds[k]) < ns: seeds[k].append(A)
        if all(len(v) >= ns for v in seeds.values()): break
    print({k: len(v) for k, v in seeds.items()}, flush=True)
    seeds = sorted({A for v in seeds.values() for A in v})
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
        random.seed(13); s2 = random.sample(sorted(g1), min(300, len(g1)))
        g2 = set()
        for o in p.imap_unordered(gen, s2): g2 |= o
    allN = sorted(g1 | g2 | set(seeds) | base)
    print('total', len(allN), flush=True)
    pickle.dump([list(N) for N in allN], open(out, 'wb'))
