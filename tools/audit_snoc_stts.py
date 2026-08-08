"""Audit (SNOC) on REAL BM4 sequences, not just the random/exhaustive pool.

`probe_snoc.py` measured (SNOC) on short exhaustive and randomised sequences.
The soundness rule for this project is that a frozen claim must be re-audited on
sequences actually reachable by the expansion (`ST_TS`) at closure+5/+6, because
random column tuples miss the tower shapes that killed earlier conjectures
(A_x1 == 1, W2ok, spanOK, dichOK were all true on toy data and false on hosts).

Population: everything reachable from the z<2 generators `diag(3, v, zcap=1)` by
`X |-> X[n]`, plus every prefix, capped by length so `minstage` stays decidable.
For each such `C` and a sweep of appended columns `p`, check

    minstage(C ++ [p]) <= minstage(C)      when p finds a parent in C ++ [p]

and report the orphan half separately as a control.
"""
import sys
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXDEPTH = 9
MAXLEN = 36
AMAX = 18
DEPTH = 6          # closure+6
MAXC = 9           # keep minstage decidable


def lev(col):
    return 2 * col[1] + col[2]


def srow(S, j):
    if S[j][2] > 0:
        return 2
    if S[j][1] > 0:
        return 1
    return 0


def has_parent(S, j):
    return trio.parent(S, srow(S, j), j) is not None


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


def st_ts_pool():
    seen, frontier = set(), []
    for v in range(6):
        S = tuple(trio.diag(3, v, zcap=1))
        seen.add(S)
        frontier.append((S, 0))
    while frontier:
        S, dep = frontier.pop()
        if dep >= DEPTH:
            continue
        for n in NS:
            T = tuple(trio.expand(list(S), n))
            if T and len(T) <= 22 and T not in seen:
                seen.add(T)
                frontier.append((T, dep + 1))
    out = set()
    for S in seen:
        for k in range(1, min(len(S), MAXC) + 1):
            out.add(S[:k])
    return sorted((list(s) for s in out), key=len)


def main():
    memo = {}
    tot = Counter()
    ex = []
    rng = random.Random(20260808)
    pool = st_ts_pool()
    print('ST_TS-derived C candidates:', len(pool),
          '(max length', max(len(c) for c in pool), ')')
    # appended columns: a sweep around the depths that actually occur
    dmax = max(c[0] for C in pool for c in C) + 2
    cols = [(d, b, z) for d in range(dmax + 1) for b in range(4) for z in range(2)]
    # test the implication directly, stage by stage: `C in W a  ->  C ++ [p] in W a`.
    # This avoids needing the exact minstage, which is rarely decidable on real
    # ST_TS sequences within the search bounds.
    for C in pool:
        stages = [a for a in range(AMAX + 1) if inW(C, a, MAXDEPTH, memo) is True]
        if not stages:
            tot['C/no-decided-stage'] += 1
            continue
        tot['C/ok'] += 1
        for p in rng.sample(cols, min(14, len(cols))):
            S = C + [p]
            tag = 'snoc' if has_parent(S, len(C)) else 'orph'
            for a in stages:
                r = inW(S, a, MAXDEPTH, memo)
                if r is None:
                    tot[tag + '/undecided'] += 1
                    continue
                tot[tag] += 1
                if r is False:
                    tot[tag + '/VIOL'] += 1
                    if len(ex) < 8:
                        ex.append((tag, C, p, a))
    print(f"{'case':18s} {'count':>10s}")
    for k in sorted(tot):
        print(f"{k:18s} {tot[k]:10d}")
    for e in ex:
        print('  ex', e)


if __name__ == '__main__':
    main()
