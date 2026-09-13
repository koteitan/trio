import sys, random, itertools
sys.path.insert(0, S := '/home/koteitan/proofs/trio/tools')
from probe_kappa import clift, all_kappas, cands
COLS = [(a, b, c) for a in range(4) for b in range(4) for c in range(2)]
rnd = random.Random(99)
tot = bad = 0; ex = []
for _ in range(3000):
    A = [(0, 0, 0)] + [rnd.choice(COLS) for _ in range(rnd.randrange(2, 6))]
    o = rnd.randrange(1, 3)
    K1s = list(all_kappas(A, o, 1))
    K1 = rnd.choice(K1s)
    B = clift(A, o, K1, 1)
    j2 = rnd.randrange(1, 3)
    K2s = list(all_kappas(B, o + 1, j2))
    K2 = rnd.choice(K2s)
    C = clift(B, o + 1, K2, j2)
    tot += 1
    if len(cands(A, o)) > 7: continue
    if not any(clift(A, o, K, 1 + j2) == C for K in all_kappas(A, o, 1 + j2)):
        bad += 1
        if len(ex) < 3: ex.append((A, o, K1, K2, j2))
print('tot', tot, 'bad', bad)
for e in ex: print(e)
