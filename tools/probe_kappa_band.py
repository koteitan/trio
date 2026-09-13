"""klift_slift_band: for a stair phi with phi(m) = m (m <= v) and phi(m) - m = C (m >= v + J):
   slift (klift X v J K) phi == klift X v (J + C) K',  K'(y) = mK + (phi(v + mK) - (v + mK)),  mK = min(K y, J)."""
import sys, random, itertools
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio
from probe_kappa import clift, anc0

def mu(X, j):
    return min(X[y][1] for y in anc0(X, j))

def slift(X, phi):
    return [(c[0], c[1] + phi(mu(X, i)) - mu(X, i), c[2]) for i, c in enumerate(X)]

COLS = [(a, b, c) for a in range(4) for b in range(6) for c in range(2)]
rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
tot = bad = 0; ex = []
for _ in range(int(sys.argv[2]) if len(sys.argv) > 2 else 20000):
    X = [(0, 0, 0)] + [rnd.choice(COLS) for _ in range(rnd.randrange(2, 7))]
    v = rnd.randrange(1, 3); J = rnd.randrange(0, 3)
    K = {i: rnd.randrange(0, 4) for i in range(len(X))}
    # steps strictly inside [v, v+J): positions p in [v, v+J), phi lifts m > p by s
    steps = [(p, rnd.randrange(1, 3)) for p in range(v, v + J) if rnd.random() < 0.6]
    phi = lambda m, steps=steps: m + sum(s for (p, s) in steps if m > p)
    C = sum(s for (p, s) in steps)
    Kc = {i: min(K[i], J) for i in K}
    lhs = slift(clift(X, v, Kc, J), phi)
    K2 = {}
    for i in range(len(X)):
        mK = min(K[i], J)
        K2[i] = mK + phi(v + mK) - (v + mK)
    rhs = clift(X, v, K2, J + C)
    tot += 1
    if lhs != rhs:
        bad += 1
        if len(ex) < 3: ex.append((X, v, J, K, steps))
print('tot', tot, 'bad', bad)
for e in ex: print(e)
