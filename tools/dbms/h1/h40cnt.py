# -*- coding: utf-8 -*-
"""**課題 H40 段階 1 —— 残核の前提を全部満たす (S, p, C) を「数えるだけ」。**

`Subst1gReviveSelf`（`lean/Wtower2.lean:3274`）の前提:

    1. S ∈ Wself                              （証明書 `wcert(S)` で近似。健全・不完全）
    2. p < |S|
    3. C != []
    4. C ∈ Wself
    5. lev C 0 <= lev S p
    6. entry C 0 0 = entry S 0 p
    7. forall q in C, entry S 0 p <= q.1
    8. R の末尾列は R で親を持つ                （R = S.take p ++ C ++ S.drop (p+1)）
    9. (S.drop(p+1) = [] かつ C の末尾が C 内で孤児)
       または (S.drop(p+1) != [] かつ その末尾が S.drop(p+1) 内で孤児)
    10. exists q in R.dropLast, 0 < q.2.2      ← **(C2)(C5') をちょうど排除する前提**

前提 10 があるので `R` に (C1)(C2)(C5') は当たらない。⟹ 残核は自明ではない。
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import wcert as wc
from collections import Counter

N = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
AMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
rng = random.Random(20260829)
COLS = [(a, b, c) for a in range(AMAX + 1) for b in range(AMAX + 1)
        for c in range(2)]


def orphan_last(M):
    j = len(M) - 1
    return not wc.has_parent(M, j)


def gen_S():
    """S は**行 2 に 1 を混ぜる**（前提 10 のため）。証明書が当たるものだけ残す。"""
    L = rng.randint(2, 6)
    return tuple(rng.choice(COLS) for _ in range(L))


def gen_C(d, levSp):
    L = rng.randint(1, 4)
    c0 = [(b, z) for b in range(AMAX + 1) for z in range(2)
          if 2 * b + z <= levSp]
    if not c0:
        return None
    b, z = rng.choice(c0)
    out = [(d, b, z)]
    for _ in range(L - 1):
        a = rng.randint(d, AMAX)
        bb = rng.randint(0, AMAX)
        out.append((a, bb, rng.randint(0, 1)))
    return tuple(out)


t0 = time.time()
cnt = Counter()
hits = []
for _ in range(N):
    S = gen_S()
    cnt['生成'] += 1
    if wc.wcert(S) is None:
        cnt['1. S に証明書が無い'] += 1
        continue
    p = rng.randrange(len(S))
    d, levSp = S[p][0], wc.lev(S[p])
    C = gen_C(d, levSp)
    if C is None:
        cnt['5/6. C が作れない'] += 1
        continue
    if wc.wcert(C) is None:
        cnt['4. C に証明書が無い'] += 1
        continue
    R = tuple(S[:p]) + C + tuple(S[p + 1:])
    if not wc.has_parent(R, len(R) - 1):
        cnt['8. R の末尾に親が無い'] += 1
        continue
    tail = tuple(S[p + 1:])
    d9 = (orphan_last(C) if not tail else orphan_last(tail))
    if not d9:
        cnt['9. 選言が偽'] += 1
        continue
    if not any(q[2] > 0 for q in R[:-1]):
        cnt['10. R.dropLast に行 2 > 0 が無い'] += 1
        continue
    cnt['**前提を全部満たす**'] += 1
    hits.append((S, p, C, R))

print('生成 %d 個（列は 行0,行1 <= %d、行2 <= 1／|S| 2..6／|C| 1..4）  (%.0fs)'
      % (N, AMAX, time.time() - t0))
for k, v in sorted(cnt.items()):
    print('   %-34s %7d' % (k, v))
print()
print('**前提を全部満たす (S,p,C) = %d 組**' % len(hits))
if hits:
    import pickle
    pickle.dump(hits, open('/tmp/h1work/h40hits.pkl', 'wb'))
    print('   /tmp/h1work/h40hits.pkl に保存')
    print('   例:')
    for S, p, C, R in hits[:3]:
        print('     S=%s p=%d C=%s' % (list(S), p, list(C)))
        print('       R=%s  cert(R)=%s' % (list(R), wc.wcert(R)))
