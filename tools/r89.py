# -*- coding: utf-8 -*-
"""**課題 R89 —— `CoreCap` の展開の形を測る。**

対象は **`CoreCap` が見る形だけ**（教訓 19/20）:

    S := Lift1 ((0,v,z) :: cap M b c) t,   argOK M, 1 <= |M|, z <= 1, CtxOK M v z

測るもの:
  (a) バッドルート `j0`（= `parent S i1 j1`, `j1 = |S|-1`）の分布。とくに `j0 = 0` の率
  (b) コピーされる塊 `S[j0:j1]`（⚠ `range' j0 (j1-j0)` なので **cap 列 j1 は入らない**）
  (c) `j0` が `b, c` に依存するか（固定 (M,v,z,t) で (b,c) を振って j0 が動くか）
  (d) 増分 `d0`（行 0）と `d1`（行 1）が 0 か正か

★ **`j0` は `n` に依存しない**（`oper` の定義: `j0 = parent M i1 j1` に `n` が現れない）。
  ⟹ `n` を振る必要がない。

対照（教訓 11/18）:
  (A) `|M| = 1` は `j1 = 1` なので親は 0 しかない ⟹ **`j0 = 0` が構造的に強制**。内蔵の陽性対照
  (B) `argOK` を外した母集団（M の内部に row0 = 0 を許す）
  (C) `CtxOK` フィルタ有り／無し
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter, defaultdict

# ---- W 所属の健全な判定（`Wchar.lean` の厳密な特徴づけ。probe_cap2.py と同じ） ----
NS = (1, 2, 3)


def lev(c):
    return 2 * c[1] + c[2]


def lift1(S, t):
    return [(c[0], c[1] + (t if trio.is_ancestor(S, 1, 0, i) else 0), c[2])
            for i, c in enumerate(S)]


def inW(S, a, depth, memo, maxlen):
    """True = 閉じた / False = **確定した非所属** / None = 予算切れ。"""
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
    if depth <= 0 or len(S) > maxlen:
        return None
    memo[key] = None                       # 循環ガード
    out = True
    for n in NS:
        r = inW(trio.expand(list(S), n), a, depth - 1, memo, maxlen)
        if r is False:
            memo[key] = False
            return False
        if r is None:
            out = None
    memo[key] = out
    return out


# ---- 構造測定: `oper` の分岐と j0 / d0 / d1（Lean `Trio.lean:98` の逐語訳） ----
def shape(S):
    """(branch, j0, i1, d0, d1) を返す。branch in {ident, zero, noparent, copy}."""
    j1 = len(S) - 1
    if j1 == 0:
        return ('ident', None, None, 0, 0)
    if S[j1][0] == 0 and S[j1][1] == 0 and S[j1][2] == 0:
        return ('zero', None, None, 0, 0)
    i1 = 2 if S[j1][2] > 0 else (1 if S[j1][1] > 0 else 0)
    j0 = trio.parent(S, i1, j1)
    if j0 is None:
        return ('noparent', None, i1, 0, 0)
    d0 = (S[j1][0] - S[j0][0]) if i1 > 0 else 0
    d1 = (S[j1][1] - S[j0][1]) if i1 > 1 else 0
    return ('copy', j0, i1, d0, d1)


def cap(M, b, c):
    return M[:-1] + [(M[-1][0], b, c)]


def run(DS, BS, CS, VS, ZS, TS, CAPB, CAPC, LS, ctxfilter, depth, maxlen,
        label, sample=None, seed=0):
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    memo = {}
    tot = Counter()
    j0dist = Counter()
    bcdep = Counter()          # (c) 固定 (M,v,z,t) で j0 が (b,c) に依存するか
    dpair = Counter()          # (d) (d0>0, d1>0) の同時分布
    blockkind = Counter()      # (b) 塊が何か
    ex = {}
    t0 = time.time()
    import random
    rng = random.Random(seed)
    for L in LS:
        Ms = itertools.product(COL, repeat=L)
        if sample is not None and len(COL) ** L > sample:
            allM = list(itertools.product(COL, repeat=L))
            Ms = rng.sample(allM, sample)
        for Mt in Ms:
            M = list(Mt)
            for v in VS:
                for z in ZS:
                    # ---- 装備 CtxOK M v z ----
                    if ctxfilter:
                        st = 'eq'
                        for k in range(L):
                            for t in TS:
                                r = inW(lift1([(0, v, z)] + M[:k], t),
                                        2 * (v + t) + z, depth, memo, maxlen)
                                if r is False:
                                    st = 'NOT-eq'
                                elif r is None and st == 'eq':
                                    st = 'unk-eq'
                        tot['ctx/' + st] += 1
                        if st == 'NOT-eq':
                            continue
                    else:
                        tot['ctx/nofilter'] += 1
                    for t in TS:
                        seen = set()
                        for b in CAPB:
                            for c in CAPC:
                                S = lift1([(0, v, z)] + cap(M, b, c), t)
                                j1 = len(S) - 1
                                br, j0, i1, d0, d1 = shape(S)
                                tot['branch/' + br] += 1
                                if br != 'copy':
                                    seen.add((br, None))
                                    continue
                                seen.add((br, j0))
                                j0dist[(L, j0)] += 1
                                tot['j0=0' if j0 == 0 else 'j0>=1'] += 1
                                dpair[(d0 > 0, d1 > 0)] += 1
                                # (b) 塊 S[j0:j1]
                                if j0 == 0:
                                    blockkind['root-included'] += 1
                                elif j0 == 1:
                                    blockkind['M-all(dropLast)'] += 1
                                else:
                                    blockkind['M-proper-suffix'] += 1
                                if j0 == 0 and 'j0=0' not in ex:
                                    ex['j0=0'] = (L, M, v, z, b, c, t, S, i1, d0, d1)
                                if j0 >= 1 and 'j0>=1' not in ex:
                                    ex['j0>=1'] = (L, M, v, z, b, c, t, S, i1, d0, d1, S[j0:j1])
                        js = {x[1] for x in seen if x[0] == 'copy'}
                        bcdep['const' if len(js) <= 1 else f'varies({len(js)})'] += 1
    dt = time.time() - t0
    print(f'### {label}   ({dt:.1f}s, memo={len(memo)})')
    for k in sorted(tot):
        print(f'  {k:22s} {tot[k]:10d}')
    print('  -- (a) j0 の分布 (|M|, j0) --')
    for k in sorted(j0dist):
        print(f'     |M|={k[0]} j0={k[1]:2d} : {j0dist[k]:10d}')
    print('  -- (b) コピー塊 S[j0:j1] --')
    for k in sorted(blockkind):
        print(f'     {k:20s} {blockkind[k]:10d}')
    print('  -- (c) 固定 (M,v,z,t) で j0 は (b,c) に依存するか --')
    for k in sorted(bcdep):
        print(f'     {k:20s} {bcdep[k]:10d}')
    print('  -- (d) (d0>0, d1>0) --')
    for k in sorted(dpair):
        print(f'     d0>0={k[0]} d1>0={k[1]} : {dpair[k]:10d}')
    for k in sorted(ex):
        print(f'  ex {k}: {ex[k]}')
    print()
    return tot, j0dist


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--depth', type=int, default=9)
    ap.add_argument('--maxlen', type=int, default=28)
    ap.add_argument('--L', type=int, default=3)
    ap.add_argument('--sample', type=int, default=None)
    ap.add_argument('--which', default='main')
    a = ap.parse_args()
    DS, BS, CS = (1, 2, 3), (0, 1, 2), (0, 1)
    VS, ZS, TS = (0, 1, 2), (0, 1), (0, 1, 2)
    CAPB, CAPC = (0, 1, 2, 3), (0, 1, 2)
    LS = tuple(range(1, a.L + 1))
    if a.which in ('main', 'all'):
        run(DS, BS, CS, VS, ZS, TS, CAPB, CAPC, LS, True, a.depth, a.maxlen,
            f'MAIN  argOK + CtxOK, |M|<={a.L}, depth={a.depth}', a.sample)
    if a.which in ('nofilter', 'all'):
        run(DS, BS, CS, VS, ZS, TS, CAPB, CAPC, LS, False, a.depth, a.maxlen,
            f'CTRL-C  argOK only (CtxOK 無し), |M|<={a.L}', a.sample)
    if a.which in ('noargok', 'all'):
        run((0, 1, 2, 3), BS, CS, VS, ZS, TS, CAPB, CAPC, LS, False, a.depth,
            a.maxlen, f'CTRL-B  argOK を外した（row0=0 を許す）, |M|<={a.L}', a.sample)
