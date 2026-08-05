"""Do the expansion's copies inherit their source column's `amin`?

    (A1)  amin (S[n]) i          = amin S i                  for i < r
    (A2)  amin (S[n]) (r+a*L+xx) = amin S (r+xx)              for the copies

with r = the bad root, L = x - r the copied block length.  This is the single
lemma (G2) reduces to once the branch data are known preserved.
"""
import sys, random
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

def anc0(X, j):
    out = []; p = j
    while p is not None:
        out.append(p); p = trio.parent(X, 0, p)
    return out

def amin(X, j):
    return min(X[y][1] for y in anc0(X, j))

COLS = [(a, b, c) for a in range(4) for b in range(5) for c in range(2)]
rnd = random.Random(24680)
tot = bad1 = bad2 = 0
ex = None
for _ in range(60000):
    S = [(0, rnd.randrange(4), rnd.randrange(2))] + \
        [rnd.choice(COLS) for _ in range(rnd.randrange(1, 5))]
    n = rnd.randrange(1, 4)
    x = len(S) - 1
    if all(v == 0 for v in S[x]):
        continue
    t = max(y for y in range(3) if S[x][y] > 0)
    r = trio.parent(S, t, x)
    if r is None:
        continue
    L = x - r
    E = trio.expand(S, n)
    if len(E) != r + n * L:
        continue
    tot += 1
    for i in range(r):
        if amin(E, i) != amin(S, i):
            bad1 += 1
            if ex is None: ex = ('A1', S, n, i)
            break
    ok = True
    for a in range(n):
        for xx in range(L):
            if amin(E, r + a * L + xx) != amin(S, r + xx):
                ok = False
                if ex is None: ex = ('A2', S, n, a, xx,
                                     amin(E, r + a * L + xx), amin(S, r + xx))
    if not ok:
        bad2 += 1
print(f"expansions checked: {tot}")
print(f"  (A1) prefix amin preserved : {bad1} violations")
print(f"  (A2) copy inherits source  : {bad2} violations")
if ex: print("  ex:", ex)
