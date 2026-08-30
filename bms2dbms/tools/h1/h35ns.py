# -*- coding: utf-8 -*-
"""H35 (a)(b): `NS` を振る／節 3（graft）が効きうる場所を数える。"""
import sys, os, time, random
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio

AW, LMAX, AMAX = 6, 8, 16
MAXDEPTH, MAXLEN = 9, 34
COLS = [(a, b, c) for a in range(AW + 1) for b in range(a + 1)
        for c in range(min(b, 1) + 1)]


def lev(col):
    return 2 * col[1] + col[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def has_parent(S, j):
    return trio.parent(S, srow(S, j), j) is not None


def domT(S, m):
    """Lean の `domT M m`: 末尾が **レベル m+1 の孤児**。節 3 の前提。"""
    j = len(S) - 1
    return lev(S[j]) == m + 1 and not has_parent(S, j)


def mk(NS):
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
    return minstage


def pool(rng, n=2500):
    P = []
    for _ in range(n):
        P.append([list(rng.choice(COLS)) for _ in range(rng.randint(2, LMAX))])
    for v in range(8):
        P.append([list(c) for c in trio.diag(3, v, zcap=1)])
    return P


print('=== (a) NS を振る ===')
for NS in ((1, 2), (1, 2, 3), (1, 2, 3, 4)):
    ms = mk(NS)
    memo = {}
    rng = random.Random(99)
    P = pool(rng)
    tot, dist = Counter(), Counter()
    t0 = time.time()
    for C in P:
        mC = ms(C, memo)
        if mC is None:
            tot['C/未判定'] += 1
            continue
        for p in COLS:
            S = C + [list(p)]
            m = ms(S, memo)
            if m is None:
                tot['未判定'] += 1
                continue
            if has_parent(S, len(C)):
                tot['snoc'] += 1
                dist[m - mC] += 1
                if m > mC:
                    tot['**違反**'] += 1
    print('  NS=%-12s snoc %7d / 違反 %d / 未判定 %d / **m-mC の分布 %s**  (%.0fs)'
          % (str(NS), tot['snoc'], tot['**違反**'], tot['未判定'],
             sorted(dist.items()), time.time() - t0), flush=True)

print()
print('=== (b) 節 3（graft）が片側だけで効きうるか ===')
print('  節 3 の前提は `domT M m`（末尾がレベル m+1 の孤児）。')
print('  snoc の場合 `C ++ [p]` は**定義から親を持つ**ので `domT` は**必ず偽**。')
ms = mk((1, 2))
memo = {}
rng = random.Random(99)
P = pool(rng)
c = Counter()
for C in P:
    mC = ms(C, memo)
    if mC is None:
        continue
    dC = any(domT(C, m) for m in range(AMAX))
    for p in COLS[:20]:
        S = C + [list(p)]
        if not has_parent(S, len(C)):
            continue
        dS = any(domT(S, m) for m in range(AMAX))
        c[('C で節 3 が使える' if dC else 'C でも使えない',
           'C++[p] で使える' if dS else 'C++[p] では使えない')] += 1
for k, v in c.most_common():
    print('   %-46s %d' % (str(k), v))
