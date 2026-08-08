"""Can two `W`-members be concatenated when the second one is DEEPER?

`Wset.W_add` needs `rsum A B` = "B's root is the shallowest column of A ++ B".
That is exactly wrong for a tower: `T_{n+1} = T_n ++ shift0(Q, n*e)` appends a
block whose root is the DEEPEST.  If instead

    (W_add')  A in W u  ->  B in W u
              -> (forall p in A, A0 <= p.1) -> (forall p in B, B0 <= p.1)
              -> A0 <= B0  ->  A ++ B in W u

holds, the row-0-shifted copy tower (probe_core1 (C): 6244 instances, exact
equality) follows by a two-line induction, and with it the last open `(WL)`
branch `badPar = 0, i1 = 1`.

Reported in minstage form: `minstage(A ++ B) <= max(minstage A, minstage B)`.
V2 = the hypotheses above.  V4 = no hypotheses at all (expected to fail; it
tells us how much of V2 is actually load-bearing).
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2)
MAXDEPTH = 8
MAXLEN = 26
AMAX = 14


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


def minstage(S, memo):
    for a in range(AMAX + 1):
        r = inW(S, a, MAXDEPTH, memo)
        if r is True:
            return a
        if r is None:
            return None
    return None


def shallow(S):
    return all(S[0][0] <= p[0] for p in S)


COLS = [(a, b, c) for a in range(3) for b in range(2) for c in range(2)]


def main():
    memo = {}
    tot = Counter()
    ex = {}
    seqs = []
    for L in (1, 2):
        for S in itertools.product(COLS, repeat=L):
            seqs.append(list(S))
    stage = {}
    for S in seqs:
        m = minstage(S, memo)
        if m is not None:
            stage[tuple(S)] = m
    print('sequences with a known minstage:', len(stage), '/', len(seqs))
    keys = list(stage)
    for A in keys:
        for B in keys:
            if len(A) + len(B) > 4:
                continue
            AB = list(A) + list(B)
            m = minstage(AB, memo)
            if m is None:
                tot['undecided'] += 1
                continue
            bound = max(stage[A], stage[B])
            ok = m <= bound
            tot['V4'] += 1
            if not ok:
                tot['V4/VIOL'] += 1
                ex.setdefault('V4', (list(A), list(B), stage[A], stage[B], m))
            if shallow(A) and shallow(B) and A[0][0] <= B[0][0]:
                tot['V2'] += 1
                if not ok:
                    tot['V2/VIOL'] += 1
                    ex.setdefault('V2', (list(A), list(B), stage[A], stage[B], m))
                elif m < bound:
                    tot['V2/slack'] += 1
    print(f"{'case':14s} {'count':>10s}")
    for k in sorted(tot):
        print(f"{k:14s} {tot[k]:10d}")
    for k, e in sorted(ex.items()):
        print(f"  ex {k}: A={e[0]} B={e[1]} mA={e[2]} mB={e[3]} mAB={e[4]}")


if __name__ == '__main__':
    main()
