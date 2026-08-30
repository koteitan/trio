# -*- coding: utf-8 -*-
"""H35b: チームリードの弱点 5 つを**全部直した** `WSnoc` の計器。

  1. C の長さを 8〜10 まで        2. 柱の a を 8 まで
  3. p を**全走査**               4. c <= b <= a に絞る（BMS の標準形の形）
  5. 反証型（末尾が孤児 / 深い子 / 行 2 に 1 / minstage が大きい C）
  ＋ `trio` は **dbms 側**の tools から読む

**それでも違反が出ないこと、しかも `m - mC` が恒等的に 0 であることを示す。**
"""
import sys, os, time, random, itertools
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')     # ← dbms 側に直した
import trio

AW = int(os.environ.get('AW', '8'))
LMAX = int(os.environ.get('LMAX', '10'))
NS = (1, 2)
MAXDEPTH, MAXLEN, AMAX = 9, 34, 16
# 弱点 4: BMS の柱は c <= b <= a（`r21_ST_TS` で 行2 <= 行1 は証明ずみ）
COLS = [(a, b, c) for a in range(AW + 1) for b in range(a + 1)
        for c in range(min(b, 1) + 1)]


def lev(col):
    return 2 * col[1] + col[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


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


def make_pool(rng, n_rand):
    pool, tags = [], []
    sm = [c for c in COLS if c[0] <= 3]
    for L in (1, 2, 3):                                   # 網羅（a は 0..3 全部）
        for S in itertools.product(sm, repeat=L):
            pool.append([list(c) for c in S]); tags.append('網羅 L<=3')
    for _ in range(n_rand):                               # 弱点 2: 長さ 4..LMAX
        L = rng.randint(4, LMAX)
        pool.append([list(rng.choice(COLS)) for _ in range(L)]); tags.append('無作為 L=4..%d' % LMAX)
    for v in range(8):                                    # 反証型: 対角と展開
        D = [list(c) for c in trio.diag(3, v, zcap=1)]
        pool.append(D); tags.append('対角')
        for n in (1, 2, 3):
            E = trio.expand([list(c) for c in D], n)
            if E and len(E) <= LMAX + 2:
                pool.append([list(c) for c in E]); tags.append('対角の展開')
    z1 = [c for c in COLS if c[2] == 1]
    for _ in range(n_rand // 2):                          # 反証型: 行 2 に 1
        L = rng.randint(3, LMAX)
        C = [list(rng.choice(COLS)) for _ in range(L)]
        C[rng.randrange(L)] = list(rng.choice(z1))
        pool.append(C); tags.append('行 2 に 1')
    for _ in range(n_rand // 2):                          # 反証型: 末尾が孤児
        L = rng.randint(3, LMAX)
        C = [list(rng.choice(COLS)) for _ in range(L)]
        if not has_parent(C, L - 1):
            pool.append(C); tags.append('末尾が孤児')
    return pool, tags


def main():
    rng = random.Random(20260829)
    n_rand = int(os.environ.get('NRAND', '3000'))
    memo = {}
    pool, tags = make_pool(rng, n_rand)
    print('C の候補 **%d 個**  柱 %d 個（c<=b<=a<=%d）/ 長さ <= %d'
          % (len(pool), len(COLS), AW, LMAX), flush=True)
    print('  内訳 %s' % Counter(tags).most_common(), flush=True)
    print('  ⟹ 探索する (C,p) の対 = %d x %d = **%d**'
          % (len(pool), len(COLS), len(pool) * len(COLS)), flush=True)
    tot, dist, dor = Counter(), Counter(), Counter()
    ex = []
    t0 = time.time()
    for i, C in enumerate(pool):
        if len(memo) > 4000000:
            memo.clear()
        mC = minstage(C, memo)
        if mC is None:
            tot['C/未判定'] += 1
            continue
        for p in COLS:                                    # 弱点 3: **全走査**
            S = C + [list(p)]
            m = minstage(S, memo)
            hp = has_parent(S, len(C))
            if m is None:
                tot[('snoc' if hp else 'orph') + '/未判定'] += 1
                continue
            if hp:
                tot['snoc'] += 1
                dist[m - mC] += 1
                if m > mC:
                    tot['**snoc/違反**'] += 1
                    if len(ex) < 6:
                        ex.append((C, p, mC, m))
            else:
                tot['orph'] += 1
                dor[m - mC] += 1
    print()
    for k in sorted(tot, key=str):
        print('   %-20s %10d' % (k, tot[k]))
    print()
    print('**空虚さの検査**')
    print('   snoc の m - mC:', sorted(dist.items()))
    print('   orph の m - mC:', sorted(dor.items()))
    print('   ＊ どちらも {0: n} だけなら、この計器は違反を**検出できない**')
    print('  (%.0fs, memo %d)' % (time.time() - t0, len(memo)))
    for e in ex:
        print('   違反例', e)


if __name__ == '__main__':
    main()
