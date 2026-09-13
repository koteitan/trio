"""C1: marked lift commutes with expansion up to re-marking.
vlev(y) = 2*row1 + [y in M]; column j lifted by d iff min vlev over row-0 ancestors (incl. j) > 2*o.
M must consist of columns with row1 == o, z == 0, upward-closed along row-0 ancestors of row1 == o."""
import sys, random, itertools
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

def anc0(X, j):
    out = []; p = j
    while p is not None:
        out.append(p); p = trio.parent(X, 0, p)
    return out

def closed(X, o, M):
    for j in M:
        if X[j][1] != o or X[j][2] != 0: return False
        for y in anc0(X, j):
            if X[y][1] == o and y not in M: return False
    return True

def mlift(X, o, M, d):
    out = []
    for j, c in enumerate(X):
        m = min(2 * X[y][1] + (1 if y in M else 0) for y in anc0(X, j))
        out.append((c[0], c[1] + (d if m > 2 * o else 0), c[2]))
    return out

def cands(X, o):
    return [j for j, c in enumerate(X) if c[1] == o and c[2] == 0]

COLS = [(a, b, c) for a in range(4) for b in range(4) for c in range(2)]
rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
tot = bad = skipped = 0
ex = []
for _ in range(int(sys.argv[2]) if len(sys.argv) > 2 else 20000):
    A = [(0, 0, 0)] + [rnd.choice(COLS) for _ in range(rnd.randrange(2, 6))]
    o = rnd.randrange(1, 3); d = rnd.randrange(1, 3); n = rnd.randrange(1, 3)
    cs = cands(A, o)
    Ms = [set(s) for r in range(len(cs) + 1) for s in itertools.combinations(cs, r)]
    Ms = [M for M in Ms if closed(A, o, M) and M]
    if not Ms:
        continue
    M = rnd.choice(Ms)
    try:
        lhs = trio.expand(mlift(A, o, M, d), n)
        E = trio.expand(A, n)
    except Exception:
        skipped += 1; continue
    tot += 1
    cs2 = cands(E, o)
    if len(cs2) > 12:
        skipped += 1; tot -= 1; continue
    ok = False
    for r in range(len(cs2) + 1):
        for s in itertools.combinations(cs2, r):
            s = set(s)
            if closed(E, o, s) and mlift(E, o, s, d) == lhs:
                ok = True; break
        if ok: break
    if not ok:
        bad += 1
        if len(ex) < 3: ex.append((A, o, sorted(M), d, n))
print('tot', tot, 'bad', bad, 'skipped', skipped)
for e in ex: print(e)
