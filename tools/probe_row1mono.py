"""(ROW1MONO): is `W a` closed under LOWERING row 1 at any set of columns?

    M in W a,  M' has the same row 0 and row 2 and  row1(M'_j) <= row1(M_j)
      ==>  M' in W a

Why it matters: `Lift1 X d` (the lift BM4's row-2 collapse performs, masked by
the `le1`-cone of the root) is exactly the UNIFORM lift `shiftr01 0 d X` with
row 1 lowered by `d` at the columns outside the cone.  The uniform lift is
already proved to transport `W` (`Wslift.ulift_mem_W`), so

    (ULIFT) + (ROW1MONO)  ==>  (WL) LiftStage

with NO tie-freeness and no window hypothesis -- it removes the index-mask vs
value-mask obstruction outright (`Wtower2.liftStage_of_row1mono`).

Measured, 0 violations everywhere:
  * multi-column lowering (exhaustive short blocks + random tail): 369068 decided
  * single-column lowering: 106763 decided
  * ADVERSARIAL, lowering exactly where it changes the parent structure -- at
    the bad root, at its whole `le1`-cone and at the terminal: 773483 decided
    (`main_adversarial` below)
  * TOWER-shaped hosts (row-0-shifted, row-1-lifted copy towers, with and
    without a trailing column) -- the shapes that made A_x1 == 1, W2ok, spanOK
    and dichOK look true on toy data: 258507 decided (`main_tower` below)
The proved `snoc_zeroRow2` is used as a base case of the decision procedure,
which is why these decide far more than the earlier probes.
"""
import sys
import itertools
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXD = 11
MAXLEN = 44


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
    if all(c[2] == 0 for c in S[:-1]):          # zeroRow2 / snoc_zeroRow2
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


def main():
    memo, tot, ex = {}, Counter(), []
    rng = random.Random(24680)
    COLS = [(x, b, z) for x in range(4) for b in range(4) for z in range(2)]
    pop = []
    for L in (2, 3):
        for S in itertools.product(COLS, repeat=L):
            S = list(S)
            if S[0][0] != 0:
                continue
            pop.append(S)
    for _ in range(50000):
        L = rng.randint(3, 7)
        S = [(0, rng.randint(0, 4), rng.randint(0, 1))]
        for _ in range(L - 1):
            S.append((rng.randint(0, 6), rng.randint(0, 5), rng.randint(0, 1)))
        pop.append(S)
    print('pop', len(pop), flush=True)
    for S in pop:
        a = lev(tuple(S[0]))
        if inW(S, a, MAXD, memo) is not True:
            continue
        tot['S ok'] += 1
        for _ in range(8):
            M = []
            for c in S:
                nb = rng.randint(0, c[1]) if c[1] > 0 else 0
                M.append((c[0], nb, c[2]))
            if M == S:
                continue
            r = inW(M, a, MAXD, memo)
            if r is None:
                tot['undecided'] += 1
                continue
            tot['decided'] += 1
            if r is False:
                tot['VIOLATION'] += 1
                if len(ex) < 6:
                    ex.append((S, a, M))
    for k in sorted(tot):
        print(f'  {k:12s} {tot[k]:9d}')
    for S, a, M in ex:
        print(f'  VIOL a={a}\n    S={S}\n    M={M}')


def srow(S, j):
    if S[j][2] > 0:
        return 2
    if S[j][1] > 0:
        return 1
    return 0


def main_adversarial():
    """Lower row 1 exactly at the columns that steer the expansion."""
    memo, tot, ex = {}, Counter(), []
    rng = random.Random(777001)
    for _ in range(200000):
        L = rng.randint(3, 7)
        S = [(0, rng.randint(0, 5), rng.randint(0, 1))]
        for _ in range(L - 1):
            S.append((rng.randint(0, 4), rng.randint(0, 6), rng.randint(0, 1)))
        a = lev(tuple(S[0]))
        if inW(S, a, MAXD, memo) is not True:
            continue
        tot['S ok'] += 1
        x = len(S) - 1
        tgts = {x}
        j0 = trio.parent(S, srow(S, x), x)
        if j0 is not None:
            tgts.add(j0)
            for j in range(len(S)):
                if trio.is_ancestor(S, 1, j0, j):
                    tgts.add(j)
        for j in tgts:
            for nb in range(S[j][1]):
                M = [c for c in S]
                M[j] = (S[j][0], nb, S[j][2])
                r = inW(M, a, MAXD, memo)
                if r is None:
                    tot['undecided'] += 1
                    continue
                tot['decided'] += 1
                if r is False:
                    tot['VIOLATION'] += 1
                    if len(ex) < 6:
                        ex.append((S, a, j, nb, M))
    for k in sorted(tot):
        print(f'  {k:12s} {tot[k]:9d}')
    for S, a, j, nb, M in ex:
        print(f'  VIOL a={a} j={j}->{nb}\n    S={S}\n    M={M}')


def main_tower():
    """Hosts that are guarded copy towers, with an optional trailing column."""
    memo, tot, ex = {}, Counter(), []
    rng = random.Random(606060)

    def tower(Q, e, f, n):
        T = []
        for k in range(n):
            T += [(c[0] + k * e, c[1] + k * f, c[2]) for c in Q]
        return T

    for _ in range(60000):
        L = rng.randint(1, 3)
        Q = [(0, rng.randint(0, 3), rng.randint(0, 1))]
        for _ in range(L - 1):
            Q.append((rng.randint(1, 3), rng.randint(0, 4), rng.randint(0, 1)))
        S = tower(Q, rng.randint(1, 3), rng.randint(0, 2), rng.randint(2, 4))
        if rng.random() < 0.5:
            S = S + [(rng.randint(0, 6), rng.randint(0, 5), rng.randint(0, 1))]
        if len(S) > 60:
            continue
        a = lev(tuple(S[0]))
        if inW(S, a, MAXD, memo) is not True:
            continue
        tot['tower ok'] += 1
        for _ in range(6):
            M = [(c[0], rng.randint(0, c[1]) if c[1] > 0 else 0, c[2]) for c in S]
            if M == S:
                continue
            r = inW(M, a, MAXD, memo)
            if r is None:
                tot['undecided'] += 1
                continue
            tot['decided'] += 1
            if r is False:
                tot['VIOLATION'] += 1
                if len(ex) < 6:
                    ex.append((S, a, M))
    for k in sorted(tot):
        print(f'  {k:12s} {tot[k]:9d}')
    for S, a, M in ex:
        print(f'  VIOL a={a}\n    S={S}\n    M={M}')


if __name__ == '__main__':
    main()
    print('--- adversarial:')
    main_adversarial()
    print('--- towers:')
    main_tower()
