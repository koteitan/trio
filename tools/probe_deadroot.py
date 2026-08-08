"""Which side condition can `Wstar` carry?

With the `natDom` guard, `Wstar R` needs a `tbAll` side condition on the
PRINCIPAL block `M = (0,v,z) :: R` (see GRAFTALL-PLAN 4.5).  Three candidates,
in decreasing strength:

  (S1)  tbAll M (2v+z)   -- every parentless column of M is at level <= the root
  (S2)  tbAll M m        -- ... <= R's trailing orphan level  (m from domT R m)
  (S3)  tbAll M a        -- ... <= the target stage

`Wstar_closed`'s branches need:
  * clause 3, dead orphan  -> m < a           <= (S3)
  * clause 3, tower        -> tbAll M m       <= (S2), and (S1) implies it
                              because `tower1_le` gives 2v+z <= m
  * the recursive Wstar calls must reproduce the condition

(S3) alone is NOT enough (the tower recursion runs at stage `m`, which can be
far below `a`).  So the question is whether (S1) -- the clean, root-relative
form -- actually holds for the blocks the proof feeds to `Wstar`, namely the
TOP-LEVEL TREES of standard matrices (`mem_of_Aclosed_aux`).

This probe walks standard matrices (expansions of seeds), splits each into its
top-level trees `T = p :: R` (re-based to depth 0), and reports, for every
tree and every proper "sub-root" split the induction also uses:

    r  = lev(root)
    u0 = max{ lev(c) | c parentless in T }
    verdict: u0 <= r ?

It also reports the same for ALL prefixes `T.take k`, since `Wstar_closed`
re-enters on `R.dropLast` and on `graft R y`.
"""
import sys
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

MAXLEN = 80


def lev(c):
    return 2 * c[1] + c[2]


def srow(c):
    return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)


def parentless(X, j):
    return lev(X[j]) > 0 and trio.parent(X, srow(X[j]), j) is None


def u0(X):
    return max((lev(X[j]) for j in range(len(X)) if parentless(X, j)),
               default=0)


def toplevel_trees(M):
    """split M into maximal blocks whose columns are all deeper than the head."""
    out = []
    i = 0
    while i < len(M):
        d = M[i][0]
        j = i + 1
        while j < len(M) and M[j][0] > d:
            j += 1
        out.append([(c[0] - d, c[1], c[2]) for c in M[i:j]])
        i = j
    return out


def main():
    tot = Counter()
    ex = []
    seeds = []
    for v in range(4):
        for z in range(2):
            seeds.append(trio.diag(3, v, z))
    base = [(0, 0, 0)]
    for a in range(1, 4):
        for b in range(3):
            for c in range(2):
                seeds.append(base + [(1, b, c), (a, b, c)])
                seeds.append(base + [(1, b, c)])

    mats = []
    for S in seeds:
        X = list(S)
        for _ in range(12):
            mats.append(list(X))
            if len(X) < 2 or len(X) > MAXLEN:
                break
            X = trio.expand(list(X), 2)

    for M in mats:
        for T in toplevel_trees(M):
            if not T:
                continue
            r = lev(T[0])
            for k in range(1, len(T) + 1):
                P = T[:k]
                tot['tree-prefix'] += 1
                b = u0(P)
                if b <= r:
                    tot['S1/ok'] += 1
                else:
                    tot['S1/FAIL'] += 1
                if b <= max(r, 1):
                    tot['S1pp/ok'] += 1
                else:
                    tot['S1pp/FAIL'] += 1
                    if len(ex) < 6:
                        ex.append((T, k, r, b, P))

    print('standard matrices walked:', len(mats))
    for k in sorted(tot):
        print(f'  {k:16s} {tot[k]:8d}')
    for T, k, r, b, P in ex:
        print(f'  S1-FAIL  root lev={r}  u0={b}  k={k}')
        print(f'     tree  ={T}')
        print(f'     prefix={P}')


if __name__ == '__main__':
    main()
