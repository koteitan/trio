"""WfCof: attack EvalFS c = 2 with deep matrices and large n.

usage: nice -n 15 python3 descent.py OUT.pkl SEED WALKS LENCAP
Random descents from SRO[m] (m = 2..5): at each step expand with a random n in 1..4 (or 0 rarely),
keep matrices with len <= LENCAP. Stores the visited matrices (standard by construction).
Then: python3 fsprobe.py OUT.json NMAX OUT.pkl
"""
import sys, random, pickle
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio
SRO = [[0, 0, 0], [1, 1, 1], [2, 1, 1], [3, 1, 0], [2, 0, 0]]
out, seed, walks, cap = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
random.seed(seed)
seen = set()
for w in range(walks):
    M = trio.expand(SRO, random.randint(2, 5))
    for step in range(random.randint(5, 300)):
        if len(M) <= 1: break
        n = random.choice([1, 2, 2, 3, 3, 4, 5]) if random.random() > 0.05 else 0
        N = trio.expand(M, n)
        if len(N) > cap:
            N = trio.expand(M, 1)
        M = N
        if len(M) >= 2: seen.add(tuple(tuple(c) for c in M))
pickle.dump(sorted(seen), open(out, 'wb'))
print(len(seen))
