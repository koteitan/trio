# -*- coding: utf-8 -*-
"""`WSnoc`（`lean/Wtower2.lean:2023`）の**両側とも健全な**反証器。

`probe_snoc.py` の `minstage` は `W` の代役でしかない（節 3 未実装、節 1 を
`lev <= a` に緩めている）。ここでは Lean の `W` そのものを、
**下界 `Wlo`（True が健全）** と **上界 `Wup`（False が健全）** で挟む。

Lean（`lean/Wset.lean:171`）:

    M in W u <=> lfp X. [ (|M| <= 1 /\ lev M 0 = 0)                     (1)
                        \/ (forall n >= 1, M[n] in X)                    (2)
                        \/ (exists m < u, domT M m /\
                              forall z in W m, based z -> graft M z in X) (3) ]

### 下界 `Wlo`（True が健全 —— 任意の u で `M in W u`）

`oper` は「最後の列が零列」または「親が無い」とき `Pred M`（= dropLast）を返す。
これは **n に依らない**ので、節 2 の `forall n >= 1` が**有限で確かめられる**。

    Wlo(M) := (|M| <= 1 /\ lev M 0 = 0)
           \/ (|M| >= 2 /\ (最後の列が零 \/ 親が無い) /\ Wlo(Pred M))

＝「**孤児の塔**」。切り詰めが一切入らないので True は本物。

### 上界 `Wup`（False が健全 —— `Wup = False` なら本当に `M not in W u`）

* 節 2 は `n in 1..N` に切る。切ると**通りやすくなる**ので上界。
  `False` は「有限の証人 n が見つかった」なので健全。
* 節 3 は**必要条件**に緩める。2 つの観察:
  - `domT M m` は `lev M (|M|-1) = m+1` で m を**一意に**決める。
    よって「exists m < u」は m = lev(最後) - 1 の 1 通りだけ調べればよい。
  - `[] in W m`（節 1、`|[]| = 0 <= 1`, `lev [] 0 = 0`）かつ `based []`。
    `graft M [] = M.dropLast`（Lean の `graft_nil`）。
    ⟹ **節 3 ならば `M.dropLast in X`**。これを節 3 の代わりに使う。
  緩めているので上界。`False` は健全。

### 反証

    Wlo(C) = True（C in W u が**確定**） かつ hasParent(C ++ [p], .., |C|)
    かつ Wup(C ++ [p], u) = False（not in W u が**確定**）
    ⟹ **`WSnoc` の本物の反例**
"""
import sys, os, time, random, itertools
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio


def lev_at(M, j):
    return 2 * M[j][1] + M[j][2] if 0 <= j < len(M) else 0


def srow(M, j):
    return 2 if M[j][2] > 0 else (1 if M[j][1] > 0 else 0)


def has_parent(M, j):
    return trio.parent(list(M), srow(M, j), j) is not None


def domT_m(M):
    """`domT M m` が成り立つ**唯一の** m（無ければ None）。"""
    if not M:
        return None
    j = len(M) - 1
    L = lev_at(M, j)
    if L == 0 or has_parent(M, j):
        return None
    return L - 1


def Wlo(M):
    """W u の健全な下界（孤児の塔）。True なら**任意の u で** M in W u。"""
    M = list(M)
    while len(M) >= 2:
        j = len(M) - 1
        if M[j] != (0, 0, 0) and has_parent(M, j):
            return False
        M = M[:-1]
    return len(M) <= 1 and (len(M) == 0 or lev_at(M, 0) == 0)


def Wup(M, u, depth, memo, N, maxlen):
    """W u の健全な上界。**False なら本当に M not in W u**。"""
    M = tuple(tuple(c) for c in M)
    key = (M, u, depth)
    if key in memo:
        return memo[key]
    if len(M) <= 1 and (len(M) == 0 or lev_at(M, 0) == 0):
        memo[key] = True
        return True
    if depth <= 0 or len(M) > maxlen:
        return None
    memo[key] = None                      # 循環よけ
    # 節 3 を**先に**見る（`dropLast` は必ず縮むので安く、必ず止まる）。
    # 節 2 は伸びるので高い。順序は結論に影響しない（どちらも選言）。
    dm = domT_m(M)
    c3 = False
    if dm is not None and dm < u:
        c3 = Wup(M[:-1], u, depth - 1, memo, N, maxlen)
    if c3 is True:
        memo[key] = True
        return True
    c2 = True
    for n in range(1, N + 1):
        r = Wup(trio.expand(list(M), n), u, depth - 1, memo, N, maxlen)
        if r is False:
            c2 = False
            break
        if r is None:
            c2 = None
    if c2 is True:
        memo[key] = True
        return True
    out = False if (c2 is False and c3 is False) else None
    memo[key] = out
    return out


def towers(cols, maxlen, cap):
    """`Wlo` が立つ C（孤児の塔）を幅優先で作る。母数を明記できる形。"""
    out = []
    frontier = [(c,) for c in cols if lev_at([c], 0) == 0]
    out += frontier
    while frontier and len(out) < cap:
        nxt = []
        for C in frontier:
            if len(C) >= maxlen:
                continue
            for p in cols:
                S = C + (p,)
                j = len(S) - 1
                if S[j] == (0, 0, 0) or not has_parent(S, j):
                    nxt.append(S)
                    if len(out) + len(nxt) >= cap:
                        break
            if len(out) + len(nxt) >= cap:
                break
        out += nxt
        frontier = nxt
    return out[:cap]


def towers_deep(cols, lo, hi, cap, seed=11):
    """**長い**孤児の塔を乱択で作る（BFS だと |C| <= 3 に偏るため）。"""
    rng = random.Random(seed)
    out = []; tries = 0
    base = [c for c in cols if c[1] == 0 and c[2] == 0]
    while len(out) < cap and tries < cap * 400:
        tries += 1
        C = (rng.choice(base),)
        tgt = rng.randint(lo, hi)
        while len(C) < tgt:
            ok = [p for p in cols
                  if p == (0, 0, 0) or not has_parent(C + (p,), len(C))]
            if not ok:
                break
            C = C + (rng.choice(ok),)
        if len(C) >= lo:
            out.append(C)
    return out


if __name__ == '__main__':
    U = int(sys.argv[1]); N = int(sys.argv[2]); DEP = int(sys.argv[3])
    CAP = int(sys.argv[4]) if len(sys.argv) > 4 else 3000
    MAXLEN = int(sys.argv[5]) if len(sys.argv) > 5 else 34
    COLS = [(a, b, c) for a in range(6) for b in range(8) for c in range(2)]
    print('u=%d  節 2 の n = 1..%d  depth=%d  COLS=%d 列  maxlen=%d'
          % (U, N, DEP, len(COLS), MAXLEN), flush=True)
    DEEP = len(sys.argv) > 6 and sys.argv[6] == 'deep'
    T = (towers_deep(COLS, 4, 12, CAP) if DEEP else towers(COLS, 6, CAP))
    print('  C の長さ分布: %s'
          % dict(sorted(Counter(len(C) for C in T).items())), flush=True)
    print('**C: Wlo が立つ孤児の塔 %d 個（C in W u が確定、任意の u）**' % len(T),
          flush=True)
    assert all(Wlo(C) for C in random.Random(1).sample(T, min(200, len(T))))
    print('  陽性対照: 抜き取り 200 個すべてで Wlo = True  OK', flush=True)

    memo = {}; tot = Counter(); ex = []; t0 = time.time()
    for i, C in enumerate(T):
        if len(memo) > 3000000:           # memo が 4GB 級に育つので上限を切る
            memo.clear(); tot['memo を捨てた回数'] += 1
        if time.time() - t0 > (int(os.environ.get("R49BUDGET", 2400))):
            tot['**時間切れ（C を %d / %d まで）**' % (i, len(T))] += 1; break
        cand = [p for p in COLS if has_parent(C + (p,), len(C))]
        cand.sort(key=lambda q: 2 * q[1] + q[2], reverse=True)
        for p in cand:
            r = Wup(C + (p,), U, DEP, memo, N, MAXLEN)
            if r is None:
                tot['決まらず'] += 1
            elif r is True:
                tot['C+[p] は W %d の上界の中（反例でない）' % U] += 1
            else:
                tot['**反例: C in W %d だが C+[p] not in W %d**' % (U, U)] += 1
                if len(ex) < 10:
                    ex.append((C, p))
    print('--- 結果 (%.0fs)' % (time.time() - t0))
    for k in sorted(tot):
        print('    %-46s %d' % (k, tot[k]))
    for e in ex:
        print('    ex C=%s  p=%s' % (''.join(map(str, e[0])), e[1]))
