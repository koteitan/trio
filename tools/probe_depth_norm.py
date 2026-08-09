"""Does `W`-membership depend only on the ORDER TYPE of row 0?

Rows 1 and 2 carry the level (`lev = 2*row1 + row2`), so the stage is untouched
by a row-0 relabelling.  Row 0 is the tree encoding, and every parent test
(`nextrel0` and the no-dip clause) is purely order-theoretic.  But the expansion
uses row 0 QUANTITATIVELY: it adds `k * (x_{j1} - x_{j0})`.  So the question is
whether that arithmetic is forced by the order.

If membership is order-invariant, towers can be normalised (e.g. to `d0 = 1`)
and the open content of `(TOW)` becomes a much smaller family.  If not, the
counterexample tells us exactly which arithmetic matters.

Four relabellings, all strictly order- and equality-preserving on row 0:
  * `rank`    -- compress the distinct depths to 0,1,2,...
  * `stretch` -- x |-> 2*x
  * `affine`  -- x |-> 3*x + 1
  * `random`  -- a random strictly increasing map

Measured (67900 sequences, length up to 6, depths up to 7): 3290952 decided,
0 disagreements (rank 794933, stretch 837728, affine 841208, random 817083).
A targeted sweep over the depth patterns where the arithmetic differs most
(x0 = 0, x1 large, x2 small) added 134200 decided, 0 disagreements.

⚠ `oper` itself is NOT equivariant.  `M = [(0,0,0),(5,0,0),(1,1,0)]` expands to
order type 0,3,1,4,2,5 while its rank compression expands to 0,2,1,3,2,4.  So
membership invariance, if true, is not a consequence of a commuting square, and
a proof would need a different mechanism.
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXDEPTH = 10
MAXLEN = 40
AMAX = 12


def lev(c):
    return 2 * c[1] + c[2]


def inW(S, a, d, memo):
    S = tuple(tuple(c) for c in S)
    key = (S, a)
    if key in memo:
        return memo[key]
    if len(S) == 0:
        return True
    if len(S) == 1:
        r = lev(S[0]) <= a
        memo[key] = r
        return r
    if d <= 0 or len(S) > MAXLEN:
        return None
    memo[key] = None
    out = True
    for n in NS:
        r = inW(trio.expand(list(S), n), a, d - 1, memo)
        if r is False:
            memo[key] = False
            return False
        if r is None:
            out = None
    memo[key] = out
    return out


def relabel_rank(M):
    vals = sorted({c[0] for c in M})
    idx = {v: i for i, v in enumerate(vals)}
    return [(idx[c[0]], c[1], c[2]) for c in M]


def relabel_stretch(M):
    return [(2 * c[0], c[1], c[2]) for c in M]


def relabel_affine(M):
    return [(3 * c[0] + 1, c[1], c[2]) for c in M]


def main():
    memo = {}
    tot = Counter()
    ex = []
    import random
    rng = random.Random(31337)

    def relabel_random(M):
        vals = sorted({c[0] for c in M})
        out, cur = {}, rng.randint(0, 2)
        for v in vals:
            out[v] = cur
            cur += rng.randint(1, 4)
        return [(out[c[0]], c[1], c[2]) for c in M]

    pop = []
    COLS = [(x, b, z) for x in range(5) for b in range(3) for z in range(2)]
    for L in (2, 3):
        for M in itertools.product(COLS, repeat=L):
            pop.append(list(M))
    for _ in range(40000):                      # longer, deeper random tail
        L = rng.randint(4, 6)
        pop.append([(rng.randint(0, 7), rng.randint(0, 3), rng.randint(0, 1))
                    for _ in range(L)])
    print('population:', len(pop), flush=True)
    for M in pop:
            for name, f in (('rank', relabel_rank), ('stretch', relabel_stretch),
                            ('affine', relabel_affine), ('random', relabel_random)):
                M2 = f(M)
                if M2 == M:
                    continue
                for a in range(AMAX + 1):
                    r1 = inW(M, a, MAXDEPTH, memo)
                    r2 = inW(M2, a, MAXDEPTH, memo)
                    if r1 is None or r2 is None:
                        tot[name + '/undecided'] += 1
                        continue
                    tot[name + '/decided'] += 1
                    if r1 == r2:
                        tot[name + '/agree'] += 1
                    else:
                        tot[name + '/DISAGREE'] += 1
                        if len(ex) < 10:
                            ex.append((name, M, M2, a, r1, r2))
    for k in sorted(tot):
        print(f'  {k:22s} {tot[k]:9d}')
    for name, M, M2, a, r1, r2 in ex:
        print(f'  DISAGREE [{name}] a={a}  {r1} vs {r2}')
        print(f'    M ={M}')
        print(f'    M2={M2}')


if __name__ == '__main__':
    main()
