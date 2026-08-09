"""How often is BM4's row-2 copy block TIE-FREE, on REAL `ST_TS` sequences?

`Wtower2.liftStage_of_tieFree` makes the stage law `(WL)` FREE (no cores, via the
proved `mlift_mem_W`) whenever the block the lift acts on is TIE-FREE:

    {j | le1 B 0 j}  =  {j | coneV B (v0 - 1) j}   and   v0 = row1(B[0]) >= 1

`le1`-cone ⊆ `amin`-cone is unconditional (`Wtower2.coneV_of_le1`), so the only
gap is a column whose row-1 value TIES the root's.

The soundness rule of this project says a frozen claim must be re-measured on
sequences actually REACHABLE by the expansion, not on random column tuples —
random tuples reported 86% tie-free, which means nothing on its own.  This probe
walks the `ST_TS` closure of the `z<2` generators `diag(3, v, zcap=1)` and, at
every sequence whose terminal collapses at row 2, rebases the copied block
`B = S[j0 .. j1-1]` and tests tie-freeness there.
"""
import sys
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

NS = (1, 2, 3)
DEPTH = 11
MAXLEN = 60


def srow(S, j):
    if S[j][2] > 0:
        return 2
    if S[j][1] > 0:
        return 1
    return 0


def anc0(S, j):
    out, x = [], j
    while x is not None:
        out.append(x)
        x = trio.parent(S, 0, x)
    return out


def amin(S, j):
    return min(S[y][1] for y in anc0(S, j))


def tiefree(B):
    v0 = B[0][1]
    c1 = {j for j in range(len(B)) if trio.is_ancestor(B, 1, 0, j)}
    c2 = {j for j in range(len(B)) if amin(B, j) == v0}
    return c1 == c2, v0


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
            if T and len(T) <= MAXLEN and T not in seen:
                seen.add(T)
                frontier.append((T, dep + 1))
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
        if j0 is None:
            tot['orphan terminal'] += 1
            continue
        if sr != 2:
            tot['srow<2 terminal'] += 1
            continue
        B = [(c[0] - S[j0][0], c[1], c[2]) for c in S[j0:x]]
        if not B:
            continue
        tot['row-2 copy blocks'] += 1
        tf, v0 = tiefree(B)
        if tf and v0 >= 1:
            tot['  (WL) FREE'] += 1
        elif tf:
            tot['  tie-free but v0=0'] += 1
        else:
            tot['  HAS TIE'] += 1
            if len(ex) < 8:
                ex.append((S, j0, B, v0))
    for k in sorted(tot):
        print(f'  {k:24s} {tot[k]:8d}')
    for S, j0, B, v0 in ex:
        print(f'  TIE j0={j0} v0={v0}')
        print(f'    S={S}')
        print(f'    B={B}')


if __name__ == '__main__':
    main()
