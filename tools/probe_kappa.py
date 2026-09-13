"""C1k: capped min-lift commutes with expansion up to re-capping.
lam(y) = 0 if row1 < o or (row1 == o and z == 1); kappa(y) if row1 == o and z == 0; j if row1 > o.
column c lifted by min over row-0 ancestors y (incl. c) of lam(y).
kappa: values in 0..j, antitone along row-0 ancestry among level-o z=0 columns (descendant <= ancestor)."""
import sys, random, itertools
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

def anc0(X, j):
    out = []; p = j
    while p is not None:
        out.append(p); p = trio.parent(X, 0, p)
    return out

def cands(X, o):
    return [i for i, c in enumerate(X) if c[1] == o and c[2] == 0]

def ok_kappa(X, o, K):
    for i, k in K.items():
        for y in anc0(X, i)[1:]:
            if y in K and K[y] < k: return False
    return True

def clift(X, o, K, j):
    out = []
    for i, c in enumerate(X):
        def lam(y):
            r, z = X[y][1], X[y][2]
            if r < o or (r == o and z == 1): return 0
            if r == o: return K[y]
            return j
        out.append((c[0], c[1] + min(lam(y) for y in anc0(X, i)), c[2]))
    return out

def all_kappas(X, o, j):
    cs = cands(X, o)
    for vals in itertools.product(range(j + 1), repeat=len(cs)):
        K = dict(zip(cs, vals))
        if ok_kappa(X, o, K): yield K

if __name__ == "__main__":
    COLS = [(a, b, c) for a in range(4) for b in range(4) for c in range(2)]
    rnd = random.Random(int(sys.argv[1]))
    lo, hi = int(sys.argv[3]), int(sys.argv[4])
    tot = bad = skip = 0; ex = []
    for _ in range(int(sys.argv[2])):
        A = [(0, 0, 0)] + [rnd.choice(COLS) for _ in range(rnd.randrange(lo, hi))]
        o = rnd.randrange(1, 3); j = rnd.randrange(1, 4); n = rnd.randrange(1, 3)
        Ks = list(all_kappas(A, o, j))
        Ks = [K for K in Ks if any(v > 0 for v in K.values())]
        if not Ks: continue
        K = rnd.choice(Ks)
        try:
            lhs = trio.expand(clift(A, o, K, j), n); E = trio.expand(A, n)
        except Exception:
            skip += 1; continue
        if len(cands(E, o)) > 7: skip += 1; continue
        tot += 1
        if not any(clift(E, o, K2, j) == lhs for K2 in all_kappas(E, o, j)):
            bad += 1
            if len(ex) < 3: ex.append((A, o, K, j, n))
    print('tot', tot, 'bad', bad, 'skip', skip)
    for e in ex: print(e)

