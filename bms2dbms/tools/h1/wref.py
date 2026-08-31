# -*- coding: utf-8 -*-
"""**健全な反証器**（課題 H57 の共通モジュール）。

`lean/Wchar.lean` の**厳密な特徴づけ**をそのまま実装する:

    `aop_clause3_to_clause2`（:39）  節 3 は |S| >= 2 で節 2 に吸収される
    `mem_iff_oper_mem`（:75）        `2 <= |S|` ⟹ (`S ∈ W a` ⟺ `∀ n >= 1, S⟦n⟧ ∈ W a`)
    `mem_iff_lev_le`（:106）         `[(d,v,z)] ∈ W a` ⟺ `2v+z <= a`
    `W_nil`                          `[] ∈ W a`

⟹ 3 節の `Aop` は次の**決定的**な再帰に潰れる（節 3 の pool 近似は要らない）:

    |S| = 0        → True
    |S| = 1        → lev S[0] <= a
    |S| >= 2       → ∀ n >= 1, inW(S[n], a)

## 近似の向き（毎回意識すること）

    **False は健全**   … `∀ n >= 1` の 1 本の反例で足りる。NS ⊆ {n : n>=1} なので、
                        NS のどれかで False なら**確定した非所属**。
    **True は過大**     … `∀ n` を有限 NS で切っている。⟹ `W` が広くなる。
    **None は未判定**   … 深さ・長さの予算切れ。**通過に数えてはいけない。**

## 仮定の検査に使うときの向き

核の仮定（`C ∈ W u` など）を `inW == True` で確かめると、True が過大なので
**仮定を過大に認める** ⟹ 母集団が広くなる ⟹ **違反を見つけやすくなる**。
したがって「**違反ゼロ**」はこの向きでは**強い結果**である。
逆に**違反が出たときは、その 1 件について仮定を手で確かめ直す必要がある**。
"""
import sys
from collections import Counter

sys.setrecursionlimit(100000)
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio  # noqa: E402

NS = (1, 2, 3)
MAXDEPTH = 9
MAXLEN = 34


def lev(col):
    return 2 * col[1] + col[2]


def levM(S, j):
    return 0 if j >= len(S) else 2 * S[j][1] + S[j][2]


def entry(S, i, j):
    return 0 if j >= len(S) else S[j][i]


def srow(S, j):
    """lean/Trio.lean:81 —— 非零の最下行。"""
    if j >= len(S):
        return 0
    c = S[j]
    return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)


def has_parent(S, i, j):
    """lean/Trio.lean:85 `hasParent M i j`。"""
    return trio.parent(list(S), i, j) is not None


def has_parent_last(S):
    """末尾列が自分の行で親を持つか。"""
    if not S:
        return False
    j = len(S) - 1
    return has_parent(S, srow(S, j), j)


def domT(S, m):
    """lean/Wset.lean:61。"""
    if not S:
        return False
    j = len(S) - 1
    return levM(S, j) == m + 1 and not has_parent(S, srow(S, j), j)


def dom_m(S):
    """`domT S m` が成り立つ唯一の `m`（無ければ None）。"""
    if not S:
        return None
    j = len(S) - 1
    L = levM(S, j)
    if L == 0:
        return None
    if has_parent(S, srow(S, j), j):
        return None
    return L - 1


def argOK(S):
    """lean/Wset.lean:1314 —— 全列の行 0 が正。"""
    return all(c[0] > 0 for c in S)


def based(S):
    return entry(S, 0, 0) == 0


def graft(M, z):
    """lean/Wset.lean:66。"""
    d = entry(M, 0, len(M) - 1)
    return list(M[:-1]) + [(c[0] + d, c[1], c[2]) for c in z]


def cap(M, b, c):
    """lean/Lind.lean:168 —— 末尾列の添字を (b,c) に差し替える。"""
    return list(M[:-1]) + [(entry(M, 0, len(M) - 1), b, c)]


def Lift1(X, d):
    """lean/Wset.lean:927 —— 行 1 を `le1 X 0 ·` の錐の上でだけ `d` 持ち上げる。"""
    return [(c[0], c[1] + (d if trio.is_ancestor(list(X), 1, 0, i) else 0), c[2])
            for i, c in enumerate(X)]


def shiftr01(d, e, X):
    """行 0 を `d`、行 1 を `e` ずらす。"""
    return [(c[0] + d, c[1] + e, c[2]) for c in X]


# ---------------------------------------------------------------- 反証器

class Ref:
    """健全な反証器。`ns` / `maxdepth` / `maxlen` を振れる（予算検査用）。"""

    def __init__(self, ns=NS, maxdepth=MAXDEPTH, maxlen=MAXLEN, maxnodes=None):
        self.ns = ns
        self.maxdepth = maxdepth
        self.maxlen = maxlen
        self.maxnodes = maxnodes      # 1 回の照会あたりの展開回数の上限（None = 無制限）
        self.memo = {}
        self.calls = 0
        self._budget = 0

    def inW(self, S, a, depth=None):
        """True=閉じた / **False=確定した非所属** / None=予算切れ。"""
        if depth is None:
            depth = self.maxdepth
            self._budget = self.maxnodes if self.maxnodes else -1
        S = tuple(tuple(c) for c in S)
        key = (S, a)
        m = self.memo
        if key in m:
            return m[key]
        if len(S) == 0:
            return True
        if len(S) == 1:
            r = lev(S[0]) <= a
            m[key] = r
            return r
        if depth <= 0 or len(S) > self.maxlen or self._budget == 0:
            return None
        if self._budget > 0:
            self._budget -= 1
        self.calls += 1
        m[key] = None                       # 循環ガード（None なので False にはならない）
        out = True
        for n in self.ns:
            r = self.inW(trio.expand(list(S), n), a, depth - 1)
            if r is False:
                m[key] = False
                return False
            if r is None:
                out = None
        m[key] = out
        return out

    def minstage(self, S, amax=16):
        """`inW` が True になる最小の段。None = その範囲では未判定。"""
        for a in range(amax + 1):
            r = self.inW(S, a)
            if r is True:
                return a
            if r is None:
                return None
        return None


# ---------------------------------------------------------------- 陽性対照

CONTROLS = [
    ([(0, 1, 0)], 0, False, '単元 lev 2 > 0'),
    ([(0, 5, 1)], 10, False, '単元 lev 11 > 10'),
    ([(0, 2, 0), (1, 0, 0)], 0, False, '§130.4 の対照 1'),
    ([(0, 3, 1), (1, 0, 0)], 2, False, '§130.4 の対照 2（行 2 も効く）'),
    ([(0, 1, 0), (2, 0, 0), (1, 0, 0)], 1, False, '§130.4 の対照 3'),
    ([(0, 1, 1), (1, 0, 0)], 2, False, '行 2 つき'),
    ([], 0, True, '空列'),
    ([(0, 0, 0)], 0, True, '単元 lev 0'),
    ([(0, 5, 1)], 11, True, '単元 lev 11 <= 11'),
    ([(0, 0, 0), (1, 1, 0)], 0, True, '（反例でない）'),
    # 不完全性の実例: Lean では `snoc_zeroRow2` で `W 0` に入るが、
    # 反証器は塔が伸びるので判定できない（**未判定を通過に数えない**理由）。
    ([(0, 0, 0), (1, 1, 1)], 0, None, '**不完全性の実例**（Lean では W 0 に入る）'),
]


def print_controls(ref, tag=''):
    """陽性対照。**予算に依らないこと**も同時に確かめる（10 倍予算で再測）。"""
    big = Ref(ns=(1, 2, 3, 4), maxdepth=ref.maxdepth + 6, maxlen=ref.maxlen * 2,
              maxnodes=30000)
    ok = True
    print('**陽性対照%s**（`確定 非所属` が出ること／予算を上げても動かないこと）' % tag)
    print()
    print('| `S` | `a` | 期待 | 判定 | 予算増 | 備考 |')
    print('|---|--:|---|---|---|---|')
    nm = {True: 'W に入る', False: '**確定 非所属**', None: '未判定'}
    for S, a, want, why in CONTROLS:
        r = ref.inW(S, a)
        r3 = big.inW(S, a)
        # 健全性の要: **False は予算を上げても False のまま**でなければならない。
        if want is False and not (r is False and r3 is False):
            ok = False
        if want is True and r is not True:
            ok = False
        print('| `%s` | %d | %s | %s | %s | %s |'
              % (''.join('(%d,%d,%d)' % q for q in S) or '[]', a,
                 nm[want], nm[r], nm[r3], why))
    print()
    print('**対照の総合: %s**' % ('全部期待どおり' if ok else '⚠ ずれあり'))
    print()
    return ok


def degeneracy(rows):
    """退化検査: 判定（'OK'/'違反'/'未判定'）が自明な関数と一致していないか。

    `rows` は `(verdict, S)` の列（`S` は判定対象の列）。
    """
    print('**退化検査**（判定が自明な述語と一致していないか）')
    print()
    feats = {
        '`len(S) <= 2`': lambda S: len(S) <= 2,
        '`len(S) <= 3`': lambda S: len(S) <= 3,
        '`lev S[0] == 0`': lambda S: levM(S, 0) == 0,
        '`行 2 が全部 0`': lambda S: all(c[2] == 0 for c in S),
        '`行 1 が全部 0`': lambda S: all(c[1] == 0 for c in S),
    }
    print('| 述語 | 判定と一致 | 母数 |')
    print('|---|--:|--:|')
    n = len(rows)
    for name, f in feats.items():
        agree = sum(1 for v, S in rows if (v == 'OK') == bool(f(S)))
        print('| %s | %d (%.1f%%) | %d |'
              % (name, agree, 100.0 * agree / max(n, 1), n))
    print()


def tally(tot, title='結果'):
    print('**%s**' % title)
    print()
    print('| 場合 | 件数 |')
    print('|---|--:|')
    for k in sorted(tot):
        print('| %s | %d |' % (k, tot[k]))
    print()


def fmt(S):
    return ''.join('(%d,%d,%d)' % tuple(q) for q in S) or '[]'
