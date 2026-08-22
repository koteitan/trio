"""BMS(BM4) -> DBMS 変換。

原理:
  BM4 の展開規則は BMS と DBMS で完全に同一で、違うのは「標準形の集合」だけ。
  行列 M の表す順序数 ord(M) は展開規則だけで決まる（どちらのシステムかに依存しない）:
      ord(空) = 0
      ord(M)  = ord(M から末尾列を除いたもの) + 1   （末尾列が全零 = 後続）
      ord(M)  = sup_n ord(M[n])                     （それ以外 = 極限）
  よって BMS -> DBMS 変換 f は「同じ順序数を表す DBMS 標準形を返す」写像で、
      f(0) = 空,   f(a+1) = f(a) ++ 全零列,   f(lim) = sup_n f(a[n])
  で計算できる。sup は DBMS の対角から展開で降りて求める（順序数が真に減るので停止）。

注意: sup の判定「e >= sup_n X_n か」は
  「X_n が e より長くなるまで見て、それでも e > X_n なら yes」
という有限近似を使っている（X_n = f(a[n]) が接頭辞的に増えることを仮定）。
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import Mat, expand, cmpmat, diag, rows, show, parse, isstd

MMAX = 24       # 降下で試す展開添字の上限
LCAP = 60       # 降下で試す行列の長さ上限
KMAX = 200      # 対角接頭辞の上限
SLACK = 1       # X_n が e よりこれだけ長くなったら打ち切り
NMAX = 48       # X_n を見る最大の項数

_memo: dict = {}
stats = {'limit': 0, 'X': 0}
BUDGET = [200000]


class Budget(Exception):
    pass


def blocks(m: Mat):
    """行 0 が 0 の列で切る（＝順序数の和の項）。"""
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
    if len(bs) > 1:                      # 加法性: f(A++B) = f(A) ++ f(B)
        r = tuple(c for b in bs for c in convert(b, Y))
        _memo[key] = r
        return r
    if not m:
        r = ()
    elif isstd(m, 'DBMS'):
        # ord は展開規則だけで決まるので、すでに DBMS 標準形ならそれ自身が答え
        r = m
    elif all(v == 0 for v in m[-1]):
        r = convert(m[:-1], Y) + (tuple([0] * Y),)
    else:
        r = _limit(m, Y)
    _memo[key] = r
    return r


def _limit(m: Mat, Y: int) -> Mat:
    stats['limit'] += 1
    if stats['limit'] > BUDGET[0]:
        raise Budget()
    cache: dict[int, Mat] = {}

    def X(n: int) -> Mat:
        if n not in cache:
            stats['X'] += 1
            cache[n] = convert(expand(m, n), Y)
        return cache[n]

    def above(e: Mat) -> bool:
        """ord(e) >= sup_n ord(X_n) か。

        X_n は接頭辞的に増えるので、flat 比較の最初の差の位置が X_n の内側なら
        その大小は n を増やしても変わらない ⇒ そこで確定できる。"""
        fe = [v for c in e for v in c]
        n, plen, pn = 1, None, None
        while n <= NMAX:
            fx = [v for c in X(n) for v in c]
            dec = None
            for i in range(min(len(fe), len(fx))):
                if fe[i] != fx[i]:
                    dec = fe[i] > fx[i]
                    break
            if dec is not None:
                return dec
            if len(fe) <= len(fx):
                return False          # e は X_n の接頭辞 ⇒ e <= X_n
            # X_n が e の真の接頭辞 ⇒ 未確定。長さの伸びから必要な n を見積もって跳ぶ
            if plen is not None and len(fx) > plen:
                step = (len(fx) - plen) / (n - pn)
                jump = n + max(1, int((len(fe) - len(fx)) / step) + 1)
            else:
                jump = n + 1
            plen, pn, n = len(fx), n, min(jump, NMAX)
        return True

    k = 0
    while k <= KMAX and not above(diag('DBMS', k, Y)):
        k += 1
    if k > KMAX:
        raise RuntimeError('convert: diagonal exhausted for ' + show(m))
    cur = diag('DBMS', k, Y)

    while True:
        nxt = None
        for mm in range(MMAX):
            e = expand(cur, mm)
            if cmpmat(e, cur) >= 0 or len(e) > LCAP:
                break
            if above(e):
                nxt = e
                break
        if nxt is None:
            return cur
        cur = nxt
