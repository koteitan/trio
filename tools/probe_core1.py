"""The last open `(WL)` branch: `badPar = 0`, collapse row `1`.

After v0.118.77 the stage law `(WL)` rests on exactly one class of sequences
(`Final.TRIO_terminates_of_srow1`):

    LSPOn (fun X => badPar X = 0 /\ srow X (|X|-1) = 1)

i.e.  [forall n>=1, Lift1 (X[n]) d in W a]  ->  [forall n>=1, (Lift1 X d)[n] in W a].

Here `d1 = 0` and `d0 = entry X 0 j1 - entry X 0 0 > 0`, so

    X[n]          = flatMap_{k<n} shift0(k*d0) (X.dropLast)
    (Lift1 X d)[n] = flatMap_{k<n} shift0(k*d0) Q,   Q = Lift1 (X.dropLast) d

Commutation FAILS here: `Lift1 (X[n]) d` lifts only copy 0's cone (the copy
roots all carry row 1 = entry X 1 0, so they are NOT in the 0-cone of X[n]),
whereas `(Lift1 X d)[n]` carries the same mask on EVERY copy.  So the branch
cannot be closed the way the other three were.

This script measures three things:

  (S)  the branch statement itself, in minstage form:
         sup_n minstage((Lift1 X d)[n])  <=  max(2d, sup_n minstage(Lift1 (X[n]) d))
  (T)  the structural identity  (Lift1 X d)[n] = flatMap_{k<n} shift0(k*d0) Q
  (C)  the candidate closing lemma — a row-0-shifted copy tower costs no stage:
         minstage(flatMap_{k<n} shift0(k*e) Q) = minstage(Q)
       for Q whose root is strictly the shallowest column.

(C) is the interesting one: if true it closes this branch directly (n shifted
copies of a W-member stay in the same stage), and it is the same shape as the
other open core `TowerExp`.
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


def le1(S, r, j):
    return trio.is_ancestor(S, 1, r, j)


def lift1(S, d):
    return [(c[0], c[1] + (d if le1(S, 0, i) else 0), c[2])
            for i, c in enumerate(S)]


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


def branch_data(X):
    """(j0, i1, d0) when X is a host of the open branch, else None."""
    if len(X) < 2:
        return None
    x = len(X) - 1
    if all(v == 0 for v in X[x]):
        return None
    t = max(y for y in range(3) if X[x][y] > 0)
    if t != 1:
        return None
    r = trio.parent(X, t, x)
    if r != 0:
        return None
    return (0, 1, X[x][0] - X[0][0])


COLS = [(a, b, c) for a in range(3) for b in range(3) for c in range(2)]
DS = (1, 2, 3)


def main():
    memo = {}
    tot = Counter()
    ex = {}
    for L in (2, 3):
        for X in itertools.product(COLS, repeat=L):
            X = list(X)
            bd = branch_data(X)
            if bd is None:
                continue
            _, _, d0 = bd
            tot['hosts'] += 1
            # (T) structural identity
            for d in DS:
                LX = lift1(X, d)
                Q = LX[:-1]
                for n in NS:
                    tot['T'] += 1
                    if trio.expand(LX, n) != tower(Q, d0, n):
                        tot['T/VIOL'] += 1
                        ex.setdefault('T', (X, d, n))
            # (S) the branch statement, in minstage form
            for d in DS:
                LX = lift1(X, d)
                hyp = []
                goal = []
                bad = False
                for n in NS:
                    a = minstage(lift1(trio.expand(X, n), d), memo)
                    b = minstage(trio.expand(LX, n), memo)
                    if a is None or b is None:
                        bad = True
                        break
                    hyp.append(a)
                    goal.append(b)
                if bad:
                    tot['S/undecided'] += 1
                    continue
                tot['S'] += 1
                if max(goal) > max(2 * d, max(hyp)):
                    tot['S/VIOL'] += 1
                    ex.setdefault('S', (X, d, hyp, goal))
    # (C) the candidate closing lemma, on its own population
    for L in (1, 2, 3):
        for Q in itertools.product(COLS, repeat=L):
            Q = list(Q)
            if any(Q[i][0] <= Q[0][0] for i in range(1, len(Q))):
                continue          # root must be strictly the shallowest
            mq = minstage(Q, memo)
            if mq is None:
                tot['C/undecided'] += 1
                continue
            for e in (1, 2, 3):
                for n in NS:
                    T = tower(Q, e, n)
                    mt = minstage(T, memo)
                    if mt is None:
                        tot['C/undecided'] += 1
                        continue
                    tot['C'] += 1
                    if mt > mq:
                        tot['C/VIOL'] += 1
                        ex.setdefault('C', (Q, e, n, mq, mt, T))
                    elif mt < mq:
                        tot['C/slack'] += 1
    print(f"{'case':16s} {'count':>9s}")
    for k in sorted(tot):
        print(f"{k:16s} {tot[k]:9d}")
    for k, e in sorted(ex.items()):
        print(f"  ex {k}: {e}")


if __name__ == '__main__':
    main()
