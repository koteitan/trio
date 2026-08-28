# -*- coding: utf-8 -*-
"""課題 R29-4: `tools/probe_snoc.py` の母集団監査（教訓 11）＋ `WSnoc` の反証型。

`probe_snoc.py` は書き換えない（読むだけ）。ここに写して母数を振る。

Lean の本物（`lean/Wset.lean:171` Aop, `:217` W）:

    M in W u  <=>  lfp X. [ (|M| <= 1 /\ lev M 0 = 0)
                          \/ (forall n >= 1, M[n] in X)
                          \/ (exists m < u, domT M m /\
                                forall z in W m, based z -> graft M z in X) ]

`probe_snoc.inW(S, a)` が実装しているのは

    |S| = 0                     -> True     <- Lean にない（Lean は |M| <= 1 かつ lev = 0）
    |S| = 1                     -> lev <= a <- Lean は lev M 0 = 0。a は節 3 の代役
    それ以外                     -> forall n in NS=(1,2)  <- Lean は forall n >= 1
    節 3（domT / graft）        -> **無い**

つまり節 1 と 2 は**ゆるめ**、節 3 は**落として**いる。片側の近似ではないので
「違反 0」は `WSnoc` の証拠として弱い。ここで測るのは:

  (A) NS の切り詰めが minstage を変えるか（NS=(1,2) vs (1,2,3) vs (1,2,3,4)）
  (B) memo に depth が入っていないことで結果が呼び出し順に依存するか
  (C) COLS の幅（`COLS[:16]` は行 0 が {0,1} だけ。docstring 自身の証人
      `p=(1,5,0)` は COLS の外）
  (D) 反証型: 段がぴったり（たるみ 0）の C に、親が付く中で lev 最大の p を足す
"""
import sys, time, random, itertools
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio

MAXDEPTH = 9
MAXLEN = 34
AMAX = 16


def lev(col):
    return 2 * col[1] + col[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def has_parent(S, j):
    return trio.parent(list(S), srow(S, j), j) is not None


def inW(S, a, depth, memo, ns):
    """probe_snoc.inW の写し。memo のキーに depth を入れる版（既定）。"""
    S = tuple(tuple(c) for c in S)
    key = (S, a, depth)
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
    for n in ns:
        r = inW(trio.expand(list(S), n), a, depth - 1, memo, ns)
        if r is False:
            memo[key] = False
            return False
        if r is None:
            out = None
    memo[key] = out
    return out


def inW_orig(S, a, depth, memo, ns):
    """probe_snoc.py そのまま（memo のキーに depth が**入っていない**）。"""
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
    for n in ns:
        r = inW_orig(trio.expand(list(S), n), a, depth - 1, memo, ns)
        if r is False:
            memo[key] = False
            return False
        if r is None:
            out = None
    memo[key] = out
    return out


def minstage(S, memo, ns, f=inW, depth=MAXDEPTH):
    for a in range(AMAX + 1):
        r = f(S, a, depth, memo, ns)
        if r is True:
            return a
        if r is None:
            return None
    return None


COLS16 = [(a, b, c) for a in range(4) for b in range(4) for c in range(2)]


def pool_orig(rng):
    """probe_snoc.main() の母集団をそのまま再現。"""
    pool = []
    for L in (1, 2, 3):
        for S in itertools.product(COLS16[:16], repeat=L):
            pool.append(list(S))
    pool += [[rng.choice(COLS16) for _ in range(rng.randint(2, 5))]
             for _ in range(700)]
    return pool


def run_snoc(pool, cols, memo, ns, npt, rng, f=inW, depth=MAXDEPTH, budget=1e9):
    tot = Counter(); ex = []
    t0 = time.time()
    for C in pool:
        if time.time() - t0 > budget:
            tot['**時間切れで打ち切り**'] += 1; break
        mC = minstage(C, memo, ns, f, depth)
        if mC is None:
            tot['C/undecided'] += 1; continue
        for p in (rng.sample(cols, npt) if npt < len(cols) else cols):
            S = C + [p]
            tag = 'snoc' if has_parent(S, len(C)) else 'orph'
            m = minstage(S, memo, ns, f, depth)
            if m is None:
                tot[tag + '/undecided'] += 1; continue
            tot[tag] += 1
            if m > mC:
                tot[tag + '/VIOL'] += 1
                if len(ex) < 8: ex.append((tag, C, p, mC, m))
            elif m < mC:
                tot[tag + '/slack'] += 1
    return tot, ex, time.time() - t0


def show(name, tot, ex, dt, extra=''):
    print('--- %s  (%.0fs) %s' % (name, dt, extra))
    for k in sorted(tot):
        print('    %-22s %d' % (k, tot[k]))
    for e in ex[:4]:
        print('    ex', e)
    sys.stdout.flush()


if __name__ == '__main__':
    mode = sys.argv[1]
    rng = random.Random(20260808)
    P = pool_orig(random.Random(20260808))
    print('probe_snoc の母集団 C = %d 個（内訳: 全数 |C|<=3 over COLS[:16] %d ＋ 乱択 700）'
          % (len(P), len(P) - 700), flush=True)
    print('COLS = %d 個  COLS[:16] = %s ... %s（**行 0 が {0,1} だけ**）'
          % (len(COLS16), COLS16[0], COLS16[15]), flush=True)
    print('docstring の証人 p=(1,5,0) は COLS の中か: %s'
          % ((1, 5, 0) in COLS16), flush=True)

    if mode == 'A':          # NS の切り詰め
        S = random.Random(7).sample(P, int(sys.argv[2]))
        base = {}
        for ns in [(1, 2), (1, 2, 3), (1, 2, 3, 4)]:
            memo = {}; d = Counter(); t0 = time.time()
            for C in S:
                v = minstage(C, memo, ns)
                if ns == (1, 2):
                    base[tuple(map(tuple, C))] = v
                else:
                    b = base[tuple(map(tuple, C))]
                    d['同じ' if v == b else ('%s -> %s' % (b, v))] += 1
            print('  NS=%-12s %d 個 (%.0fs)  %s'
                  % (str(ns), len(S), time.time() - t0,
                     '基準' if ns == (1, 2) else dict(d)), flush=True)

    elif mode == 'B':        # memo に depth が無いことの影響
        S = random.Random(7).sample(P, int(sys.argv[2]))
        shared = {}; d = Counter()
        for C in S:
            a = minstage(C, shared, (1, 2), inW_orig)        # 使い回しの memo
            b = minstage(C, {}, (1, 2), inW_orig)            # まっさらな memo
            d['同じ' if a == b else '**違う** %s vs %s' % (a, b)] += 1
        print('  probe_snoc の memo（depth 無し）: 使い回し vs まっさら  %s'
              % dict(d), flush=True)

    elif mode == 'C':        # COLS の幅
        WIDE = [(a, b, c) for a in range(6) for b in range(8) for c in range(2)]
        S = random.Random(7).sample(P, int(sys.argv[2]))
        for nm, cols in [('COLS（元, 32 列）', COLS16), ('広い COLS（96 列）', WIDE)]:
            memo = {}
            tot, ex, dt = run_snoc(S, cols, memo, (1, 2), 10,
                                   random.Random(3), budget=900)
            show(nm, tot, ex, dt)

    elif mode == 'D':        # 反証型
        WIDE = [(a, b, c) for a in range(6) for b in range(8) for c in range(2)]
        memo = {}
        tight = []
        for C in P:
            m = minstage(C, memo, (1, 2))
            if m is not None and m > 0:
                tight.append((C, m))
        print('  **たるみ 0 の C（minstage > 0）**: %d / %d' % (len(tight), len(P)),
              flush=True)
        tot = Counter(); ex = []; t0 = time.time()
        for C, mC in tight:
            if time.time() - t0 > 1800: tot['時間切れ'] += 1; break
            cand = [p for p in WIDE if has_parent(C + [p], len(C))]
            cand.sort(key=lev, reverse=True)
            for p in cand[:6]:            # **親が付く中で lev 最大**の p
                m = minstage(C + [p], memo, (1, 2))
                if m is None: tot['undecided'] += 1; continue
                tot['snoc'] += 1
                if m > mC:
                    tot['**VIOL**'] += 1
                    if len(ex) < 8: ex.append((C, p, lev(p), mC, m))
                elif m < mC: tot['slack'] += 1
        show('反証型: たるみ 0 の C ＋ 親が付く lev 最大の p', tot, ex,
             time.time() - t0)

    elif mode == 'E':
        # **本物の W 0**。u = 0 では節 3（domT/graft）が空（m < 0）なので
        #     M in W 0 <=> (|M| <= 1 /\ lev M 0 = 0) \/ (forall n >= 1, M[n] in W 0)
        # これは inW(S, a=0) と**完全に一致**する。つまり probe_snoc が Lean の
        # W を忠実に測れているのは mC = 0 の場合だけ。
        # 最小不動点なので n を 1..N に切ると True は過大近似だが **False は健全**
        # （有限の証人 n が見つかっている）。よって反証は False 側で狙う。
        NS = tuple(range(1, int(sys.argv[3]) + 1)) if len(sys.argv) > 3 else (1, 2, 3, 4)
        DEP = int(sys.argv[4]) if len(sys.argv) > 4 else MAXDEPTH
        WIDE = [(a, b, c) for a in range(6) for b in range(8) for c in range(2)]
        memo = {}
        # (1) probe_snoc の snoc 事例のうち、Lean の W を忠実に測れているのは何割か
        m2 = {}; d = Counter()
        for C in P:
            mC = minstage(C, m2, (1, 2))
            if mC is None: d['C/undecided'] += 1
            elif mC == 0:  d['mC = 0（**Lean の W 0 と一致**）'] += 1
            else:          d['mC >= 1（節 3 の代役。Lean の W とは無関係）'] += 1
        print('  probe_snoc の C %d 個の内訳: %s' % (len(P), dict(d)), flush=True)
        # (2) 反証型: W 0 で C in W 0 かつ C+[p] not in W 0 を探す
        print('  反証型: NS=%s depth=%d COLS=%d 列' % (str(NS), DEP, len(WIDE)),
              flush=True)
        inw0 = [C for C in P if inW(C, 0, DEP, memo, NS) is True]
        print('  **C in W 0（NS 全部で確認）: %d / %d**' % (len(inw0), len(P)),
              flush=True)
        tot = Counter(); ex = []; t0 = time.time()
        for C in inw0:
            if time.time() - t0 > 2400: tot['時間切れ']+= 1; break
            cand = [p for p in WIDE if has_parent(C + [p], len(C))]
            cand.sort(key=lev, reverse=True)
            for p in cand[:12]:          # 親が付く中で lev が大きい順
                r = inW(C + [p], 0, DEP, memo, NS)
                if r is None: tot['undecided'] += 1
                elif r is True: tot['C+[p] in W 0'] += 1
                else:
                    tot['**VIOL: C in W 0 だが C+[p] not in W 0**'] += 1
                    if len(ex) < 8: ex.append((C, p, lev(p)))
        show('反証型 W 0（False は健全）', tot, ex, time.time() - t0)
