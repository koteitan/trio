"""BMS -> DBMS 変換（貪欲な正規形構成）。

f(M) は「ord が ord(M) に等しい DBMS 標準形」。正規形どうしは cmpmat（辞書式）順なので、
    f(M) = ord <= ord(M) をみたす DBMS 標準形のうち辞書式最大
であり、列を左から 1 本ずつ「ord を超えない範囲で最大」に選ぶ貪欲法で組める。

終了判定に等号は要らない: ord(N) = ord(M) になったら、どの列を足しても
ord が ord(M) を超えるので「足せる列が無い」で止まる。ocmp は不等号なら速く、
等号だけが遅いので、これで等号判定を完全に避けられる。
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import Mat, isstd, rows
from ocmp import ocmp

MAXCOL = 200


def _cols(x: int, Y: int):
    """列 x に置ける列を辞書式降順に列挙（DBMS の対角上限 max(x-y,0) 以下）。"""
    bounds = [max(x - y, 0) for y in range(Y)]

    def rec(y, acc):
        if y == Y:
            yield tuple(acc)
            return
        for v in range(bounds[y], -1, -1):
            acc.append(v)
            yield from rec(y + 1, acc)
            acc.pop()
    return rec(0, [])


def convert(M: Mat, Y: int | None = None) -> Mat:
    if Y is None:
        Y = rows(M)
    N: Mat = ()
    while len(N) < MAXCOL:
        got = None
        for c in _cols(len(N), Y):
            cand = N + (c,)
            if not isstd(cand, 'DBMS'):
                continue
            if ocmp(cand, 'DBMS', M, 'BMS') <= 0:
                got = cand
                break
        if got is None:
            return N
        N = got
    raise RuntimeError('greedy: too long')
