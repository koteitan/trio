"""Is the guarded root lift `Lift1` a PROVED staircase lift in disguise?

`Wslift` proves that the staircase lift transports `W`-membership with a stage
bump (`slift_mem_W`, `mlift_mem_W`) — no cores — because `slift` COMMUTES with
`oper`.  Its mask is determined by `amin X j` (the minimum row-1 value over the
row-0 ancestors of `j`), and `Stair` requires `φ m - m` nondecreasing and
`φ 0 = 0`.

`Lift1 X d` — the lift the row-2 tower actually performs — lifts the columns of
the `le1`-cone of the root, `{j | le1 X 0 j}`.  That is NOT an `amin` condition
a priori.  But `amin X j <= row1(0) =: v0` always (the root is a row-0 ancestor
of everything in a based block), so the only candidate match is

    mask(mlift X (v0-1) d)  =  {j | amin X j > v0 - 1}  =  {j | amin X j = v0}

and `mlift X (v0-1) d` IS proved.  This probe measures, over based `zle1` blocks:

  * how often `{j | le1 X 0 j} = {j | amin X j = v0}` (the cone coincides), and
  * the split by `v0 = 0` vs `v0 >= 1` (`Stair.zero` forbids `v0 = 0`, since the
    threshold `v0 - 1` truncates in ℕ and the lift would move row-1-zero columns).

Whenever the cone coincides AND `v0 >= 1`, the (WL) instance is FREE.
"""
import sys
import itertools
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio


def anc0(S, j):
    """Row-0 ancestors of `j`, including `j`."""
    out = []
    x = j
    while x is not None:
        out.append(x)
        x = trio.parent(S, 0, x)
    return out


def amin(S, j):
    return min(S[y][1] for y in anc0(S, j))


def cone_le1(S):
    return {j for j in range(len(S)) if trio.is_ancestor(S, 1, 0, j)}


def cone_amin(S, v0):
    return {j for j in range(len(S)) if amin(S, j) == v0}


def based_strict(S):
    """Root strictly shallowest — what every consumer of the lift supplies."""
    return all(S[0][0] < S[j][0] for j in range(1, len(S)))


def main():
    rng = random.Random(90901)
    tot = Counter()
    diff_ex, hard_ex = [], []
    pop = []
    COLS = [(x, b, z) for x in range(4) for b in range(4) for z in range(2)]
    for L in (1, 2, 3):
        for S in itertools.product(COLS, repeat=L):
            S = list(S)
            if S[0][0] != 0:
                continue
            if not based_strict(S):
                continue
            pop.append(S)
    for _ in range(60000):
        L = rng.randint(4, 7)
        S = [(0, rng.randint(0, 4), rng.randint(0, 1))]
        for _ in range(L - 1):
            S.append((rng.randint(1, 6), rng.randint(0, 4), rng.randint(0, 1)))
        if based_strict(S):
            pop.append(S)
    print('population:', len(pop), flush=True)

    for S in pop:
        v0 = S[0][1]
        c1 = cone_le1(S)
        c2 = cone_amin(S, v0)
        tot['total'] += 1
        # sanity: is the le1-cone always inside the amin-cone?
        if not c1 <= c2:
            tot['CONE NOT CONTAINED'] += 1
            if len(hard_ex) < 5:
                hard_ex.append(('notsub', S, sorted(c1), sorted(c2)))
        if c1 == c2:
            tot['cone coincides'] += 1
            if v0 >= 1:
                tot['  FREE (v0>=1)'] += 1
            else:
                tot['  blocked by v0=0'] += 1
        else:
            tot['cone DIFFERS'] += 1
            if v0 >= 1:
                tot['  differs, v0>=1'] += 1
            else:
                tot['  differs, v0=0'] += 1
            if len(diff_ex) < 6:
                diff_ex.append((S, v0, sorted(c1), sorted(c2)))
    for k in sorted(tot):
        print(f'  {k:24s} {tot[k]:9d}')
    print('--- cone differences:')
    for S, v0, c1, c2 in diff_ex:
        print(f'  S={S} v0={v0} le1cone={c1} amincone={c2}')
    for tag, S, c1, c2 in hard_ex:
        print(f'  {tag} S={S} {c1} {c2}')


if __name__ == '__main__':
    main()
