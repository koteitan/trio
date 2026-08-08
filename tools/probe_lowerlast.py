"""(LOW) — lowering the trailing column, the `|T| = 1` case of the revival core.

`Subst1gRevive` with a single-column block is exactly

    (LOW)  A ++ [c] in W u,  t.0 = c.0,  lev t <= lev c   ==>  A ++ [t] in W u

(the head-depth condition of `(SUBST1g)` forces `t.0 = c.0`, and
`[t] in W (lev c)` forces `lev t <= lev c` by `lev_root_le_of_mem_W`).

Part of it is already free from `Aop` clause 3: if `c` is a dominant terminal of
`A ++ [c]` — parentless, `lev c = m+1` — then `graft (A ++ [c]) [(0, t.1, t.2)]`
IS `A ++ [t]`, and `[(0,t.1,t.2)] in W m` holds exactly when `lev t < lev c`.
So the interesting rows below are

  * `c` PARENTED in `A ++ [c]`   (clause 3 unavailable), and
  * `lev t = lev c` with `t /= c`  (the block would need stage `lev c`, not `lev c - 1`).

This probe measures (LOW) and splits by those two axes.
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXDEPTH = 11
MAXLEN = 40
AMAX = 14


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    if S[j][2] > 0:
        return 2
    if S[j][1] > 0:
        return 1
    return 0


def has_parent(S, j):
    return trio.parent(S, srow(S, j), j) is not None


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


def main():
    memo = {}
    tot = Counter()
    ex = []
    COLS = [(x, b, z) for x in range(3) for b in range(4) for z in range(2)]
    for L in (1, 2, 3, 4):
        for S in itertools.product(COLS, repeat=L):
            S = list(S)
            if S[0][0] != 0:
                continue
            stages = [a for a in range(AMAX + 1) if inW(S, a, MAXDEPTH, memo) is True]
            if not stages:
                continue
            c = S[-1]
            A = S[:-1]
            cpar = has_parent(S, len(S) - 1)
            for b in range(4):
                for z in range(2):
                    t = (c[0], b, z)
                    if lev(t) > lev(c):
                        continue
                    T = A + [t]
                    tag = ('c-parented' if cpar else 'c-orphan') + \
                          ('/lev=' if lev(t) == lev(c) else '/lev<')
                    tpar = has_parent(T, len(T) - 1)
                    for a in stages:
                        r = inW(T, a, MAXDEPTH, memo)
                        if r is None:
                            tot['undecided'] += 1
                            continue
                        tot[tag] += 1
                        if tpar:
                            tot[tag + ' [t parented]'] += 1
                        if r is False:
                            tot['VIOLATION'] += 1
                            tot[tag + ' VIOL'] += 1
                            if len(ex) < 8:
                                ex.append((S, a, t, T))
    for k in sorted(tot):
        print(f'  {k:34s} {tot[k]:9d}')
    for S, a, t, T in ex:
        print(f'  VIOL a={a} S={S} t={t} -> T={T}')


if __name__ == '__main__':
    main()
