"""Is the ambient lift `Lift1` really needed, or would a PREPEND-only interface do?

yapss closes `Wstar_closed` with no cores because its interface is a prepend:
`Wstar R := argOK R -> forall v, (0,v) :: R in W v`, and a prepended root passes
straight through the expansion (`oper_append_inner`).  trio needed the ambient
lift `Lift1` because the ROW-2 collapse feeds its tower a ROOT-LIFTED previous
stage:

    M[j+1] = (0,v,z) :: graft R (Lift1 (M[j]) d1)          (oper_cons_tower2)

Now `Lift1 Y d` on a BASED `Y = (0,a,b) :: T` only touches the columns in the
row-1 cone of index 0:

    Lift1 ((0,a,b) :: T) d = (0, a+d, b) :: (T with the cone columns lifted)

So if that cone were just `{0}`, the lift would be nothing but "bump the root",
the datum would be `(0, v+d1, z) :: T` with `T = graft R (...) in Wstar` (which
clause 3's `hgr` already supplies), and **the whole lift language — (WL), (TOW),
(CAT), (SNOC) — would be unnecessary**.

Measured here, on row-2 tower hosts `M = (0,v,z) :: R`
(`domT R m`, `srow R (|R|-1) = 2`, `hasParent M 2 |R|`):

  Q1  is the 0-cone of `M[j]` equal to `{0}`?
  Q2  if not, is the lifted set exactly `{0} union (the copy roots)`?
  Q3  how many non-root columns get lifted, as a fraction?

Q1 = yes would be decisive.  Q2 = yes would mean a much weaker language than
full `Lift1` suffices (a root-chain lift).
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2, 3)
JMAX = 4


def srow(S, j):
    if S[j][2] > 0:
        return 2
    if S[j][1] > 0:
        return 1
    return 0


def le1(S, r, j):
    return trio.is_ancestor(S, 1, r, j)


def cone0(S):
    return [i for i in range(len(S)) if le1(S, 0, i)]


def is_tower2_host(v, z, R):
    """M = (0,v,z) :: R is a row-2 tower host arriving through clause 2."""
    if not R:
        return False
    x = len(R) - 1
    if srow(R, x) != 2:
        return False
    # domT R m : the last column is an orphan in its own row, of level m+1
    if trio.parent(R, 2, x) is not None:
        return False
    if 2 * R[x][1] + R[x][2] == 0:
        return False
    if any(c[0] == 0 for c in R):        # argOK: every column of R is deeper than the root
        return False
    M = [(0, v, z)] + list(R)
    # the root must be the row-2 parent of the last column
    return trio.parent(M, 2, len(R)) == 0


COLS = [(a, b, c) for a in range(1, 4) for b in range(3) for c in range(1, 3)]
COLS_MID = [(a, b, c) for a in range(1, 4) for b in range(3) for c in range(2)]


def main():
    tot = Counter()
    ex = []
    exq4 = []
    hosts = 0
    for v in range(3):
        for z in range(2):
            for L in (1, 2, 3):
                for R in itertools.product(
                        COLS_MID if L > 1 else COLS, repeat=L):
                    R = list(R)
                    if srow(R, len(R) - 1) != 2:
                        continue
                    if not is_tower2_host(v, z, R):
                        continue
                    hosts += 1
                    M = [(0, v, z)] + R
                    Y = M
                    for j in range(1, JMAX + 1):
                        Y = trio.expand(list(M), j)
                        if len(Y) > 40:
                            break
                        c = cone0(Y)
                        tot['inst'] += 1
                        if c == [0]:
                            tot['Q1/cone-is-root-only'] += 1
                        else:
                            tot['Q1/cone-bigger'] += 1
                            if len(ex) < 6:
                                ex.append((v, z, R, j, Y, c))
                        tot['cone-size-sum'] += len(c)
                        tot['len-sum'] += len(Y)
                        # Q4: is the cone an INITIAL SEGMENT {0,..,k}?
                        if c == list(range(len(c))):
                            tot['Q4/cone-is-prefix'] += 1
                            if len(c) == len(Y):
                                tot['Q4/cone-is-everything'] += 1
                        else:
                            tot['Q4/cone-not-prefix'] += 1
                            if len(exq4) < 6:
                                exq4.append((v, z, R, j, Y, c))
    print('row-2 tower hosts:', hosts)
    print(f"{'case':26s} {'count':>10s}")
    for k in sorted(tot):
        print(f"{k:26s} {tot[k]:10d}")
    if tot['inst']:
        print('mean cone size / mean length: %.2f / %.2f'
              % (tot['cone-size-sum'] / tot['inst'],
                 tot['len-sum'] / tot['inst']))
    for e in exq4:
        v, z, R, j, Y, c = e
        print(f'  Q4 counterexample v={v} z={z} R={R} j={j}')
        print(f'     M[j] = {Y}')
        print(f'     cone = {c}')


if __name__ == '__main__':
    main()
