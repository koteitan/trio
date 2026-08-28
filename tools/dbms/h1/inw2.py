# -*- coding: utf-8 -*-
"""**正しい `inW`** —— `lean/Wset.lean` の `Aop`（:171）を 3 節とも実装する。

    Aop Wfam u X M :=
      (M.length <= 1 /\ **lev M 0 = 0**)                          -- 節 1（底）
      \/ (forall n >= 1, M[n] in X)                               -- 節 2（展開）
      \/ (exists m < u, domT M m /\
            forall z in Wfam m, based z -> graft M z in X)        -- 節 3（graft）

既存の 27 個のプローブは**節 1 を `lev(S[0]) <= a` と書いていた**。これは
定理 `lev_root_le_of_mem_W` であって**底ではない**。底に据えると段 `a` が
最初から全部の 1 列行列を飲み込み、上に伝播して `inW` が `lev(S[0]) <= a`
に潰れる。**これが退化の正体**（team-lead, 2026-08-29）。

近似の向きを必ず意識すること:
  * 節 2 の `forall n` を `NS` で近似 ⟹ 真になりやすい ⟹ **`W` が広くなる**
  * 節 3 の `forall z in W m` を有限 pool で近似 ⟹ 真になりやすい ⟹ **広くなる**
  ⟹ **pool や NS を広げると `inW` は False になりやすい。**
  ⟹ どちらも振って結果が動かないことを確かめる（教訓 11）。

真偽の健全性:
  * **False は健全**（節 2 の 1 本の反例、節 3 の pool 内の 1 本の反例で足りる）
  * True は過大評価しうる（上の 2 つの `forall` を有限で切っているため）
  * 深さ/長さ切れは None（未判定）
"""
import sys, itertools
sys.setrecursionlimit(100000)
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio

NS = (1, 2)          # 節 2 の forall n の近似
MAXD = 9             # 節 2 の再帰の深さ
MAXLEN = 34
ZCOLS_X, ZCOLS_B, ZL = 3, 3, 3   # 節 3 の pool の大きさ


def lev(c):
    return 2 * c[1] + c[2]


def levM(S, j):
    return 0 if j >= len(S) else 2 * S[j][1] + S[j][2]


def srow(S, j):
    c = S[j]
    return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)


def has_parent(S, j):
    return trio.parent(list(S), srow(S, j), j) is not None


def domT(S, m):
    """lean/Wset.lean:61 —— 末尾がレベル m+1 の**孤児**。"""
    if not S:
        return False
    j = len(S) - 1
    return levM(S, j) == m + 1 and not has_parent(S, j)


def graft(S, z):
    """lean/Wset.lean:67 —— 末尾の孤児を森 z で置き換え、行 0 を再基準化。"""
    x = S[-1][0]
    return list(S[:-1]) + [(q[0] + x, q[1], q[2]) for q in z]


def oper(S, n):
    """lean/Trio.lean:98 `oper` の忠実な写し。

    ⚠ **`trio.expand` は長さ 1 のとき `[]` を返すが、Lean は `M` を返す**
    （`if j1 = 0 then M`）。`trio.expand` を使うと長さ 1 の行列が空列に落ち、
    節 2 が底（節 1）に触れて**全部 True** になる。これが 2 つめの退化源。
    """
    if len(S) <= 1:
        return list(S)                 # j1 = 0 ⟹ 恒等（**Lean はここが M**）
    return trio.expand(list(S), n)


def based(z):
    """lean/Wset.lean:72 —— entry z 0 0 = 0（空列も based）。"""
    return (not z) or z[0][0] == 0


# ---- 節 3 の pool ------------------------------------------------------
def _cands(xmax, bmax, zl):
    cols = [(x, b, c) for x in range(xmax) for b in range(bmax)
            for c in range(min(b, 1) + 1)]
    out = [()]
    for L in range(1, zl + 1):
        for z in itertools.product(cols, repeat=L):
            if z[0][0] == 0:                     # based
                out.append(z)
    return out


class InW(object):
    """`W u = lfpS (Aset (Wf u) u)` の **Kleene 近似**による判定器。

        X_0 = 空集合,  X_{k+1} = Aset (Wf u) u X_k,  W u = ∪_k X_k

    `k`（= `stage`）を切る ⟹ **`W` を下から近似**（False 側に安全）。
    節 2 の `forall n` を `NS` で、節 3 の `forall z` を有限 pool で切る
    ⟹ **上から近似**（True 側に緩い）。**両方振って動かないことを確かめる。**

    `k` は再帰のたびに真に減るので**循環は起きない**。memo は `(S, u, k)`。
    `k = 0` は `X_0 = 空` なので **False**（「未判定」ではない。ここが肝）。
    """

    def __init__(self, ns=NS, maxd=MAXD, maxlen=MAXLEN,
                 zx=ZCOLS_X, zb=ZCOLS_B, zl=ZL):
        self.ns, self.maxd, self.maxlen = ns, maxd, maxlen
        self.memo = {}
        self.cand = _cands(zx, zb, zl)
        self.pool = {}
        self.stat = {'c1': 0, 'c2': 0, 'c3': 0, 'no': 0}

    def Wpool(self, m):
        if m in self.pool:
            return self.pool[m]
        self.pool[m] = ()
        self.pool[m] = tuple(z for z in self.cand if self(z, m) is True)
        return self.pool[m]

    def __call__(self, S, u, k=None):
        return self._go(tuple(tuple(c) for c in S), u,
                        self.maxd if k is None else k)

    def _go(self, S, u, k):
        if k <= 0 or len(S) > self.maxlen:
            return False                          # X_0 = 空
        key = (S, u, k)
        r = self.memo.get(key)
        if r is not None:
            return r
        if len(S) <= 1 and levM(S, 0) == 0:       # 節 1
            self.memo[key] = True
            self.stat['c1'] += 1
            return True
        # 節 2: forall n >= 1, M[n] in X_{k-1}
        if all(self._go(tuple(map(tuple, oper(S, n))), u, k - 1)
               for n in self.ns):
            self.memo[key] = True
            self.stat['c2'] += 1
            return True
        # 節 3: exists m < u, domT M m, forall z in W m based, graft in X_{k-1}
        for m in range(u):
            if not domT(S, m):
                continue
            if all(self._go(tuple(map(tuple, graft(S, z))), u, k - 1)
                   for z in self.Wpool(m)):
                self.memo[key] = True
                self.stat['c3'] += 1
                return True
        self.memo[key] = False
        self.stat['no'] += 1
        return False


def minstage(f, S, amax=16):
    """S が入る最小の段。近似なので**下から**は保証されない（見つからねば None）。"""
    for a in range(amax + 1):
        if f(S, a) is True:
            return a
    return None
