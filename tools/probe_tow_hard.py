"""(TOW) in its stage-free form — the cleanest face of the residue.

With `W_root_stage` the stage of a `W`-member is its root's level, so

    (TOW)  Q in Wself,  every non-root column strictly deeper than the root
           ==>  concat_{k<n} shiftr01 (k*e) 0 Q  in Wself

reads: *n copies of a good tree, planted at depths q0, q0+e, q0+2e, ..., form a
good forest*.  Everything else in the residue reduces to it (RESIDUE-PROBLEM 4.8),
so a counterexample here would kill the route outright.

`probe_core1.py` measured only 6244 instances.  This probe hunts much harder:
random trees over a wide column range, several `e` and `n`, and it reports the
undecided share honestly.  `e = 0` is excluded because it is already free
(`W_flatMap_copies`).

Measured (seed 4242, 120000 trees of length 1..5, rows 0..5, e in 1..4,
n in 2..5): 1642293 decided, 0 violations, 134699 undecided.  Note the probe
does not impose the no-dip constraint that a real bad root would put on `e`, so
it measures a strictly more general statement.
"""
import sys
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXDEPTH = 10
MAXLEN = 52
AMAX = 14
SAMPLES = 120000


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


def inSelf(S, memo):
    if not S:
        return True
    return inW(S, lev(S[0]), MAXDEPTH, memo)


def main():
    rng = random.Random(4242)
    memo = {}
    tot = Counter()
    ex = []
    for it in range(SAMPLES):
        if it and it % 20000 == 0:
            print(f'  ... {it}/{SAMPLES}  violations: {tot["VIOLATION"]}', flush=True)
        L = rng.randint(1, 5)
        q0 = rng.randint(0, 2)
        Q = [(q0, rng.randint(0, 5), rng.randint(0, 1))]
        for _ in range(L - 1):
            Q.append((q0 + rng.randint(1, 5), rng.randint(0, 5), rng.randint(0, 1)))
        if inSelf(Q, memo) is not True:
            tot['Q not decided in Wself'] += 1
            continue
        tot['Q ok'] += 1
        for e in (1, 2, 3, 4):
            for n in (2, 3, 4, 5):
                T = []
                for k in range(n):
                    T += [(c[0] + k * e, c[1], c[2]) for c in Q]
                if len(T) > MAXLEN:
                    continue
                r = inSelf(T, memo)
                if r is None:
                    tot['undecided'] += 1
                    continue
                tot['decided'] += 1
                if r is False:
                    tot['VIOLATION'] += 1
                    if len(ex) < 8:
                        ex.append((Q, e, n, T))
    for k in sorted(tot):
        print(f'  {k:24s} {tot[k]:9d}')
    for Q, e, n, T in ex:
        print(f'  VIOLATION Q={Q} e={e} n={n}')
        print(f'            T={T}')


if __name__ == '__main__':
    main()
