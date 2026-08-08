"""Audit `(SUBST1g)` on REAL BM4 sequences — it is now the SINGLE core.

`Final.TRIO_terminates_of_subst1g` rests on `(SUBST1g)` alone, so the project's
soundness rule applies with full force: a frozen claim must be re-audited on
sequences actually reachable by the expansion (`ST_TS`) at closure+5/+6, because
random column tuples miss the tower shapes that killed A_x1 == 1, W2ok, spanOK
and dichOK — all of which were true on toy data and false on hosts.

`probe_subst1g.py` used exhaustive SHORT hosts and a fixed list of toy tails.
Here both the host AND the substituted block come from the `ST_TS` closure of
the `z<2` generators `diag(3, v, zcap=1)`, so the blocks carry genuine guarded
tower structure.  The block is re-based (row-0 shifted) onto the host column it
hangs under, exactly as `(SUBST1g)` requires.

As in `audit_snoc_stts.py` the IMPLICATION is tested stage by stage —
`S in W a  and  C in W (lev S p)  ==>  R in W a` — rather than through
`minstage`, which is rarely decidable on real ST_TS sequences within bounds.
"""
import sys
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXDEPTH = 22
MAXLEN = 400
AMAX = 30
DEPTH = 6          # closure+6
MAXHOST = 6        # keep the stage decidable on genuine tower prefixes
MAXBLOCK = 5


def lev(col):
    return 2 * col[1] + col[2]


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


def st_ts_pool(maxcut):
    """Every prefix (up to `maxcut`) of everything reachable from the z<2
    generators by `X |-> X[n]`, to depth `DEPTH`."""
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
        for k in range(1, min(len(S), maxcut) + 1):
            out.add(S[:k])
    return sorted((list(s) for s in out), key=len)


def main():
    memo = {}
    tot = Counter()
    ex = []
    rng = random.Random(20260809)
    hosts = st_ts_pool(MAXHOST)
    blocks = [Y for Y in st_ts_pool(MAXBLOCK)
              if all(c[0] > Y[0][0] for c in Y[1:])]      # root strictly shallowest
    print('ST_TS hosts:', len(hosts), ' blocks:', len(blocks))

    for S in hosts:
        stages = [a for a in range(AMAX + 1) if inW(S, a, MAXDEPTH, memo) is True]
        if not stages:
            tot['host/no-decided-stage'] += 1
            continue
        tot['host/ok'] += 1
        for p in range(len(S)):
            x = S[p][0]
            for Y in rng.sample(blocks, min(24, len(blocks))):
                shift = x - Y[0][0]
                if shift < 0:
                    continue
                C = [(c[0] + shift, c[1], c[2]) for c in Y]
                if inW(C, lev(S[p]), MAXDEPTH, memo) is not True:
                    tot['block/not in W(lev)'] += 1
                    continue
                R = S[:p] + C + S[p + 1:]
                if len(R) > MAXLEN:
                    continue
                same = (C[0][1], C[0][2]) == (S[p][1], S[p][2])
                for a in stages:
                    r = inW(R, a, MAXDEPTH, memo)
                    if r is None:
                        tot['undecided'] += 1
                        continue
                    tot['decided'] += 1
                    if not same:
                        tot['decided/head-differs'] += 1
                    if r is False:
                        tot['VIOLATION'] += 1
                        if len(ex) < 8:
                            ex.append((S, a, p, C, R))
    print(f"{'case':24s} {'count':>10s}")
    for k in sorted(tot):
        print(f'  {k:24s} {tot[k]:10d}')
    for S, a, p, C, R in ex:
        print(f'  VIOL a={a} p={p}')
        print(f'    S={S}')
        print(f'    C={C}')
        print(f'    R={R}')


if __name__ == '__main__':
    main()
