# -*- coding: utf-8 -*-
"""課題 H35: `WSnoc` を広い母集団で測る。

    (SNOC)  C ∈ W u → C ≠ [] → hasParent (C ++ [p]) (srow ..) |C| → C ++ [p] ∈ W u

`tools/probe_snoc.py` の母集団の穴（教訓 11「母集団の定義を疑う」）:

  * `COLS = a,b < 4` —— **docstring 自身の例 `(1,5,0)` が入っていない**。
    行 1 が 4 以上の柱が 1 本も無いので「親が見つかって塔になる」型の p を採れていない
  * 網羅部分が `COLS[:16]` —— **行 0 が 0 か 1 の柱だけ**
  * 1 つの C につき p は 32 個中 10 個だけ
  * `NS = (1, 2)` —— 展開の添字が 2 つだけ

ここでは 行0/行1 を `AW` まで、`NS` を可変にし、**敵対的な C / p** を足す。
**空虚さの検査**（`minstage` が動くか、`m - mC` の分布）も出す。
"""
import sys, os, time, random, itertools
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio

AW = int(os.environ.get('AW', '7'))
NS = tuple(int(x) for x in os.environ.get('NS', '1,2').split(','))
MAXDEPTH = int(os.environ.get('DEPTH', '9'))
MAXLEN = int(os.environ.get('MAXLEN', '34'))
AMAX = int(os.environ.get('AMAX', '16'))
NPROBE = int(os.environ.get('NPROBE', '200000'))
COLS = [(a, b, c) for a in range(AW + 1) for b in range(AW + 1) for c in range(2)]


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


def make_pool(rng):
    """C の母集団。網羅 ＋ 無作為 ＋ **敵対的**。"""
    pool, tags = [], []
    small = [c for c in COLS if c[0] <= 2 and c[1] <= 2]
    for L in (1, 2, 3):
        for S in itertools.product(small, repeat=L):
            pool.append(list(S)); tags.append('網羅')
    for _ in range(4000):                       # 無作為（広い柱から）
        pool.append([rng.choice(COLS) for _ in range(rng.randint(2, 7))])
        tags.append('無作為')
    # --- 敵対的 1: 対角の塔とその展開（本物の ST_TS に近い形）
    for v in range(6):
        D = [list(c) for c in trio.diag(3, v, zcap=1)]
        pool.append(D); tags.append('対角')
        for n in (1, 2, 3):
            E = trio.expand([list(c) for c in D], n)
            if E and len(E) <= 12:
                pool.append([list(c) for c in E]); tags.append('対角の展開')
    # --- 敵対的 2: 末尾が孤児になる C
    for _ in range(1500):
        C = [rng.choice(COLS) for _ in range(rng.randint(2, 6))]
        if not has_parent(C, len(C) - 1):
            pool.append(C); tags.append('末尾が孤児')
    # --- 敵対的 3: 行 2 が 1 の柱を必ず含む C（trio の難所は行 2）
    z1 = [c for c in COLS if c[2] == 1]
    for _ in range(1500):
        C = [rng.choice(COLS) for _ in range(rng.randint(1, 5))]
        C.insert(rng.randrange(len(C) + 1), rng.choice(z1))
        pool.append(C); tags.append('行 2 に 1')
    return pool, tags


def main():
    rng = random.Random(20260829)
    memo = {}
    pool, tags = make_pool(rng)
    print('C の候補 **%d 個**（AW=%d / NS=%s / DEPTH=%d / AMAX=%d）'
          % (len(pool), AW, NS, MAXDEPTH, AMAX), flush=True)
    print('  内訳 %s' % Counter(tags).most_common(), flush=True)
    tot = Counter()
    dist = Counter()
    ex = []
    t0 = time.time()
    per = max(1, NPROBE // max(1, len(pool)))
    for idx, C in enumerate(pool):
        if len(memo) > 3000000:
            memo.clear()
        mC = minstage(C, memo)
        if mC is None:
            tot['C/未判定'] += 1
            continue
        tot['_C 判定できた'] += 1
        # p は「親を持つ」ものを優先して採る（snoc の場合を厚くする）
        cand = rng.sample(COLS, min(len(COLS), per * 3))
        got = 0
        for p in cand:
            S = C + [p]
            hp = has_parent(S, len(C))
            if not hp:
                tot['orph'] += 1
                m = minstage(S, memo)
                if m is not None and m > mC:
                    tot['orph/VIOL'] += 1
                continue
            got += 1
            m = minstage(S, memo)
            if m is None:
                tot['snoc/未判定'] += 1
                continue
            tot['snoc'] += 1
            dist[m - mC] += 1
            if m > mC:
                tot['**snoc/違反**'] += 1
                if len(ex) < 8:
                    ex.append((C, p, mC, m))
            elif m < mC:
                tot['snoc/緩み'] += 1
            if got >= per:
                break
    print()
    print('%-22s %10s' % ('場合', '件数'))
    for k in sorted(tot, key=str):
        print('%-22s %10d' % (k, tot[k]))
    print()
    print('**空虚さの検査**: minstage の差 m - mC の分布')
    for d in sorted(dist):
        print('   m - mC = %+d : %d' % (d, dist[d]))
    print('   ＊ 全部 0 なら「minstage が動かない」＝ 検査が効いていない')
    print('  (%.0fs, memo %d)' % (time.time() - t0, len(memo)))
    for e in ex:
        print('  違反例', e)


if __name__ == '__main__':
    main()
