"""Route (A): the cap-generalised tower, and the `rsum`-free append identity.

`(TOW)` is `Q in W u -> shTower Q e n in W u`.  A direct induction on `n` stalls
because `(shTower Q e n)[j]` peels only the LAST copy:

    (shTower Q e n)[j] = shTower Q e (n-1) ++ shift0((n-1)*e, Q[j])

so the statement has to carry a cap.  The generalised form is

    (TOW')  Q, Y in W u  ->  shTower Q e n ++ shift0(n*e, Y)  in W u

which specialises to `(TOW)` at `Y = Q, n := n-1`.  Its induction runs on `Y`
(via A2') and needs the `rsum`-free append identity

    (AP)  2 <= |B| /\ hasParent B (srow B (|B|-1)) (|B|-1)
          ->  (A ++ B)[n] = A ++ B[n]

for the case where `Y`'s last column has its own parent; the case where `Y`'s
last column is an orphan in `Y` but gets a parent from the tower is the residue.

Measured here:
  (AP)   the append identity, on all short A and parented B
  (TOW') the cap statement, in minstage form
  (ORPH) how often the orphan case actually arises inside (TOW'), i.e. how big
         the residue is
"""
import sys
import random
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXDEPTH = 9
MAXLEN = 34
AMAX = 14


def lev(col):
    return 2 * col[1] + col[2]


def srow(S, j):
    if S[j][2] > 0:
        return 2
    if S[j][1] > 0:
        return 1
    return 0


def has_parent(S, j):
    """Does column j have a parent in its own srow row?"""
    return trio.parent(S, srow(S, j), j) is not None


def shift0(S, e):
    return [(c[0] + e, c[1], c[2]) for c in S]


def tower(Q, e, n):
    out = []
    for k in range(n):
        out.extend(shift0(Q, k * e))
    return out


def inW(S, a, depth, memo):
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
    if depth <= 0 or len(S) > MAXLEN:
        return None
    memo[key] = None
    out = True
    for n in NS:
        r = inW(trio.expand(list(S), n), a, depth - 1, memo)
        if r is False:
            memo[key] = False
            return False
        if r is None:
            out = None
    memo[key] = out
    return out


def minstage(S, memo):
    for a in range(AMAX + 1):
        r = inW(S, a, MAXDEPTH, memo)
        if r is True:
            return a
        if r is None:
            return None
    return None


COLS = [(a, b, c) for a in range(4) for b in range(3) for c in range(2)]


def main():
    memo = {}
    tot = Counter()
    ex = []
    rng = random.Random(20260808)
    short = []
    for L in (1, 2):
        for S in itertools.product(COLS, repeat=L):
            short.append(list(S))
    longer = [[rng.choice(COLS) for _ in range(rng.randint(2, 4))]
              for _ in range(500)]
    pool = short + longer

    # (AP) the rsum-free append identity
    for B in pool:
        if len(B) < 2 or not has_parent(B, len(B) - 1):
            continue
        for A in rng.sample(pool, 25):
            for n in NS:
                tot['AP'] += 1
                if trio.expand(A + B, n) != A + trio.expand(B, n):
                    tot['AP/VIOL'] += 1
                    if len(ex) < 5:
                        ex.append(('AP', A, B, n))
    # (ORPH) how often the residual (orphan) case arises
    for B in pool:
        if len(B) < 2:
            continue
        tot['orph/total'] += 1
        if not has_parent(B, len(B) - 1):
            tot['orph/orphan'] += 1

    # (TOW') the cap statement
    for Q in rng.sample(pool, 260):
        if not Q:
            continue
        mQ = minstage(Q, memo)
        if mQ is None:
            continue
        for e in (1, 2):
            for n in (1, 2):
                for Y in rng.sample(pool, 12):
                    mY = minstage(Y, memo)
                    if mY is None:
                        continue
                    T = tower(Q, e, n) + shift0(Y, n * e)
                    mT = minstage(T, memo)
                    if mT is None:
                        tot["TOW'/undecided"] += 1
                        continue
                    tot["TOW'"] += 1
                    if mT > max(mQ, mY):
                        tot["TOW'/VIOL"] += 1
                        if len(ex) < 8:
                            ex.append(("TOW'", Q, e, n, Y, mQ, mY, mT))
                    elif mT < max(mQ, mY):
                        tot["TOW'/slack"] += 1
    print(f"{'case':18s} {'count':>10s}")
    for k in sorted(tot):
        print(f"{k:18s} {tot[k]:10d}")
    for e in ex:
        print('  ex', e)


if __name__ == '__main__':
    main()
