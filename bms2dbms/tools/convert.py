"""BMS(BM4) -> DBMS 変換（厳密版）。

原理:
  BM4 の展開規則は BMS と DBMS で同一で、違うのは標準形の集合だけ。よって
  行列が表す順序数 ord(M) は展開規則だけで決まり、システムに依存しない:
      ord(空) = 0
      ord(M)  = ord(M-末尾列) + 1     (末尾列が全零 = 後続)
      ord(M)  = sup_n ord(M[n])       (それ以外 = 極限)
  変換 f は「同じ順序数を表す DBMS 標準形」を返す写像で
      f(0) = 空,  f(a+1) = f(a) ++ 全零列,  f(lim) = sup_n f(a[n])
  さらに
      M が既に DBMS 標準形なら f(M) = M
      f(A ++ B) = f(A) ++ f(B)   (B が行 0 の根で始まるとき)

sup の求め方:
  DBMS の対角から展開で降り、「まだ全部の X_n = f(M[n]) より大きい」あいだ降り続ける。
  比較は X_n が接頭辞的に増えることを使い、flat 比較の最初の差が X_n の内側に
  入った時点で確定する（X_n を e より長くする必要が無い）。
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import Mat, expand, cmpmat, diag, rows, show, parse, isstd

MMAX = 40        # 降下で試す展開添字の上限
KMAX = 200       # 対角接頭辞の上限
NMAX = 48        # X_n を見る最大の項数
PAD = 200         # 降下で許す行列長 = len(X_1) + PAD

_memo: dict = {}
stats = {'limit': 0, 'X': 0}
BUDGET = [400000]


class Budget(Exception):
    pass


def blocks(m: Mat):
    out, cur = [], []
    for c in m:
        if c[0] == 0 and cur:
            out.append(tuple(cur)); cur = []
        cur.append(c)
    if cur:
        out.append(tuple(cur))
    return out


def convert(m: Mat, Y: int | None = None) -> Mat:
    if Y is None:
        Y = rows(m)
    key = (m, Y)
    if key in _memo:
        return _memo[key]
    bs = blocks(m)
    if len(bs) > 1:
        r = tuple(c for b in bs for c in convert(b, Y))
    elif not m:
        r = ()
    elif Y > 1 and all(c[Y - 1] == 0 for c in m):
        # 最上行が全零なら 1 行少ないシステムで解いてゼロ埋め（f は行数を保つ）
        r = tuple(c + (0,) for c in convert(tuple(c[:Y - 1] for c in m), Y - 1))
    elif _is_bms_diag(m, Y):
        k = len(m)
        r = _diag(Y, k if k <= 1 else k + Y - 1)
    elif isstd(m, 'DBMS'):
        r = m
    elif all(v == 0 for v in m[-1]):
        r = convert(m[:-1], Y) + (tuple([0] * Y),)
    else:
        r = _limit(m, Y)
    _memo[key] = r
    return r


def _is_bms_diag(m: Mat, Y: int) -> bool:
    """m が BMS の対角接頭辞 (0..0)(1..1)...((k-1)..(k-1)) か。"""
    for x, c in enumerate(m):
        if any(v != x for v in c):
            return False
    return True


_dcache: dict = {}


def _diag(Y: int, k: int) -> Mat:
    r = _dcache.get((Y, k))
    if r is None:
        r = diag('DBMS', k, Y)
        _dcache[(Y, k)] = r
    return r


def _limit(m: Mat, Y: int) -> Mat:
    stats['limit'] += 1
    if stats['limit'] > BUDGET[0]:
        raise Budget()
    cache: dict[int, Mat] = {}
    fcache: dict[int, list] = {}

    def X(n: int) -> Mat:
        if n not in cache:
            stats['X'] += 1
            cache[n] = convert(expand(m, n), Y)
            fcache[n] = [v for c in cache[n] for v in c]
        return cache[n]

    def FX(n: int) -> list:
        X(n)
        return fcache[n]

    x1 = X(1)
    lcap = len(x1) + PAD

    def above(e: Mat) -> bool:
        """ord(e) >= sup_n ord(X_n) か。X_n は接頭辞的に増えると仮定。"""
        fe = [v for c in e for v in c]
        n, plen, pn = 1, None, None
        while n <= NMAX:
            fx = FX(n)
            for i in range(min(len(fe), len(fx))):
                if fe[i] != fx[i]:
                    return fe[i] > fx[i]
            if len(fe) <= len(fx):
                return False              # e は X_n の接頭辞 ⇒ e <= X_n
            if plen is not None and len(fx) > plen:
                step = (len(fx) - plen) / (n - pn)
                jump = n + max(1, int((len(fe) - len(fx)) / step) + 1)
            else:
                jump = n + 1
            plen, pn, n = len(fx), n, min(jump, NMAX)
        return True

    k = 0
    while k <= KMAX and not above(_diag(Y, k)):
        k += 1
    if k > KMAX:
        raise RuntimeError('convert: diagonal exhausted for ' + show(m))
    cur = _diag(Y, k)

    while True:
        nxt = None
        for mm in range(MMAX):
            e = expand(cur, mm)
            if cmpmat(e, cur) >= 0 or len(e) > lcap:
                break
            if above(e):
                nxt = e
                break
        if nxt is None:
            return cur
        cur = nxt
