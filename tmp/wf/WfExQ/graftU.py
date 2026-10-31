"""WfExQ graft family around the AbsUWL witnesses (bad upgrade call, W = A), to attack the Inv3V3 fields
(auw0, aus, adn0, tploq, adsx, tplosx, ...).  Seeds = the failing matrices of `auwl` in full.jsonl (graftE);
bases = seeds, M[2], M[3] and their prefixes ending at the last 3 columns; generator = WfInvD graftD.gen,
gen 1 + 300-sample gen 2 (bms -s = 1, < SRO inside gen).
usage: nice -n 15 python3 graftU.py OUT.pkl NPROC"""
import sys, pickle, random, json, re
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfReM')
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfInvD')
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
from graftD import gen
import trio
from multiprocessing import Pool
def P(s): return tuple(tuple(map(int, t)) for t in re.findall(r'\((\d+),(\d+),(\d+)\)', s))
if __name__ == '__main__':
    out, npr = sys.argv[1], int(sys.argv[2])
    seeds = set()
    for l in open('/home/koteitan/proofs/trio/tmp/wf/WfExQ/full.jsonl'):
        r = json.loads(l)
        for w in r['ex'].get('auwl', []): seeds.add(P(w[1]))
    seeds = sorted(seeds)
    base = set()
    for A in seeds:
        for n in (2, 3):
            N = tuple(tuple(c) for c in trio.expand([list(c) for c in A], n))
            for j in range(max(4, len(N) - 2), len(N) + 1): base.add(N[:j])
        for j in range(max(4, len(A) - 2), len(A) + 1): base.add(A[:j])
    print('seeds', len(seeds), 'bases', len(base), flush=True)
    g1 = set()
    with Pool(npr) as p:
        for o in p.imap_unordered(gen, sorted(base)): g1 |= o
        print('gen1', len(g1), flush=True)
        random.seed(17); s2 = random.sample(sorted(g1), min(300, len(g1)))
        g2 = set()
        for o in p.imap_unordered(gen, s2): g2 |= o
    allN = sorted(g1 | g2 | set(seeds) | base)
    print('total', len(allN), flush=True)
    pickle.dump([list(N) for N in allN], open(out, 'wb'))
