"""(ULIFT): does a UNIFORM row-1 shift transport `W` with a `2*d` stage bump?

`Wslift.slift_mem_W` requires `Stair.zero` (`φ 0 = 0`) — "row-1-zero columns must
not move, to preserve `srow`".  That condition is genuinely needed for the
COMMUTATION `slift_oper`, but this probe asks whether it is needed for the
W-MEMBERSHIP transport, which is all the tower argument uses:

    (ULIFT)   X in W m   ==>   shiftr01 0 d X  in W (m + 2d)

It matters because `mlift`'s threshold is a natural number, so the mask
`{j | amin j >= v0}` is unreachable at `v0 = 0` (the threshold would be `-1`).
`(ULIFT)` is exactly the missing `v0 = 0` case, and with it the root lift
`Lift1` is free whenever the root is strictly minimal in row 1 as well as in
row 0 (`Wtower2.liftStage_of_window`, via `Lcone.le1_zero_iff`).

Measured: 378075 decided, 0 violations, 3 undecided.

The probe also measures the companion structural fact on REAL `ST_TS`
sequences: is the bad part of a row-2 collapse a ROW-1 WINDOW, i.e. does every
interior column carry row 1 strictly above the bad root?  53634 of 53642 do; all
8 failures have root row 1 = 0.
"""
import sys
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
DEPTH = 10
MAXLEN = 50


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    if S[j][2] > 0:
        return 2
    if S[j][1] > 0:
        return 1
    return 0


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
    if d <= 0 or len(S) > 40:
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


def st_ts_pool():
    seen, fr = set(), []
    for v in range(6):
        S = tuple(trio.diag(3, v, zcap=1))
        seen.add(S)
        fr.append((S, 0))
    while fr:
        S, d = fr.pop()
        if d >= DEPTH:
            continue
        for n in (1, 2, 3):
            T = tuple(trio.expand(list(S), n))
            if T and len(T) <= MAXLEN and T not in seen:
                seen.add(T)
                fr.append((T, d + 1))
    out = set()
    for S in seen:
        for k in range(1, len(S) + 1):
            out.add(S[:k])
    return sorted((list(s) for s in out), key=len)


def main():
    pool = st_ts_pool()
    print('ST_TS pool:', len(pool), flush=True)
    tot = Counter()
    ex = []
    for S in pool:
        if len(S) < 2:
            continue
        x = len(S) - 1
        sr = srow(S, x)
        j0 = trio.parent(S, sr, x)
        if j0 is None or sr != 2:
            continue
        v0 = S[j0][1]
        tot['row-2 bad parts'] += 1
        bad = [y for y in range(j0 + 1, x) if S[y][1] <= v0]
        if not bad:
            tot['  row-1 WINDOW holds'] += 1
        else:
            tot['  window FAILS'] += 1
            if v0 == 0:
                tot['    (all at v0 = 0)'] += 1
            if len(ex) < 5:
                ex.append((S, j0, v0, bad))
    for k in sorted(tot):
        print(f'  {k:24s} {tot[k]:8d}')
    for S, j0, v0, bad in ex:
        print(f'  WINFAIL j0={j0} v0={v0} interior={bad}\n    S={S}')

    memo, t2, ex2 = {}, Counter(), []
    rng = random.Random(4242)
    for _ in range(60000):
        L = rng.randint(1, 4)
        S = [(0, rng.randint(0, 3), rng.randint(0, 1))]
        for _ in range(L - 1):
            S.append((rng.randint(1, 4), rng.randint(0, 3), rng.randint(0, 1)))
        for m in range(7):
            if inW(S, m, 10, memo) is not True:
                continue
            for d in (1, 2):
                U = [(c[0], c[1] + d, c[2]) for c in S]
                r = inW(U, m + 2 * d, 10, memo)
                if r is None:
                    t2['undecided'] += 1
                    continue
                t2['decided'] += 1
                if r is False:
                    t2['VIOLATION'] += 1
                    if len(ex2) < 5:
                        ex2.append((S, m, d, U))
    print('--- (ULIFT):')
    for k in sorted(t2):
        print(f'  {k:16s} {t2[k]:8d}')
    for S, m, d, U in ex2:
        print(f'  VIOL m={m} d={d} S={S} U={U}')


if __name__ == '__main__':
    main()
