# -*- coding: utf-8 -*-
"""read3 —— 3 行 DBMS の読み。`bms2dbms/lean/L14Read.lean` の Python 版。

    readMat B = rankify (survivors B true (0,0))
    read3   B = translate3 (readMat B)

`survivors` が影の柱を捨て、`rankify` が各行の値をその行の木での順位に直す。
Lean 側の `#guard` 5 本をこのファイルの `main` で再現する。
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse, show
from rows3 import translate3


# ---------------------------------------------------------------- 影を捨てる
def survivors(cols, first=True, plev=(0, 0)):
    """L14.survivors。影の柱を捨てて、生き残りを元の順で返す。"""
    if not cols:
        return []
    p, r = cols[0], cols[1:]
    head = r[0] if r else None
    if first and (p[1], p[2]) == plev and head == (p[0] + 1, p[1] + 1, p[2]):
        return survivors(r, True, plev)                    # 節 1: p は影
    if first and p[2] == plev[1] and head == (p[0] + 1, p[1] + 1, p[2] + 1):
        return survivors(r, True, plev)                    # 節 2: p は影
    i = 0
    while i < len(r) and p[0] < r[i][0]:
        i += 1
    return ([p] + survivors(r[:i], True, (p[1], p[2]))
                + survivors(r[i:], False, (p[1], p[2])))


# ---------------------------------------------------------------- 順位に直す
def parB(B, y, x):
    """行 y の親。行 0 は直前の小さい柱、行 y+1 は行 y の親鎖をたどる。"""
    if y == 0:
        for p in range(x - 1, -1, -1):
            if B[p][0] < B[x][0]:
                return p
        return None
    q = parB(B, y - 1, x)
    while q is not None:
        if B[q][y] < B[x][y]:
            return q
        q = parB(B, y - 1, q)
    return None


def rankB(B, y, j):
    """行 y の木での順位（親鎖の長さ）。"""
    n = 0
    q = parB(B, y, j)
    while q is not None:
        n += 1
        q = parB(B, y, q)
    return n


def rankify(B):
    return [tuple(rankB(B, y, j) for y in range(3)) for j in range(len(B))]


def readMat(B):
    """DBMS の行列を BMS の行列として読み戻す。"""
    return rankify(survivors([tuple(c) for c in B], True, (0, 0)))


def read3(B):
    """DBMS の読み。`translate3 (readMat B)`。"""
    return translate3(readMat(B))


# ---------------------------------------------------------------- 構造再帰の読み
def readD3(cols, first=True, plev=(0, 0)):
    """`rows2.readD` の 3 行版。**深さを順位に潰さない**直接の読み。

    `translate3` と同じ再帰に、影を捨てる節を 2 つ足しただけ。段は対 (行 1, 行 2)。
    `rankify` を通さないので、深さが飛ぶ DBMS 標準形でも情報が落ちない。
    """
    if not cols:
        return ('Z',)
    p, r = cols[0], cols[1:]
    head = r[0] if r else None
    if first and (p[1], p[2]) == plev and head == (p[0] + 1, p[1] + 1, p[2]):
        return readD3(r, True, plev)
    if first and p[2] == plev[1] and head == (p[0] + 1, p[1] + 1, p[2] + 1):
        return readD3(r, True, plev)
    i = 0
    while i < len(r) and p[0] < r[i][0]:
        i += 1
    lev = (p[1], p[2])
    return ('P', lev, readD3(r[:i], True, lev), readD3(r[i:], False, lev))


# ---------------------------------------------------------------- 確認
def main():
    G = [('[(0,0,0)]', '(0,0,0)', '(0,0,0)'),
         ('対角 v=1', '(0,0,0)(1,0,0)(2,1,0)(3,2,1)', '(0,0,0)(1,1,1)'),
         ('対角 v=2', '(0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,3,1)', '(0,0,0)(1,1,1)(2,2,1)'),
         ('対角 v=3', '(0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,3,1)(5,4,1)',
          '(0,0,0)(1,1,1)(2,2,1)(3,3,1)')]
    bad = 0
    for nm, b, want in G:
        got = readMat(parse(b, 3))
        ok = tuple(got) == tuple(map(tuple, parse(want, 3)))
        bad += not ok
        print('  %-10s readMat %-46s = %-34s %s' % (nm, b, show(got), 'OK' if ok else 'NG 期待 ' + want))
    d = parse('(0,0,0)(1,0,0)(2,1,0)(3,2,1)', 3)
    ok = read3(d) == translate3([tuple(c) for c in parse('(0,0,0)(1,1,1)', 3)])
    bad += not ok
    print('  %-10s read3 が translate と一致: %s' % ('対角 v=1', 'OK' if ok else 'NG'))
    print('Lean の #guard 5 本: 違反 %d' % bad)
    return bad


if __name__ == '__main__':
    sys.exit(1 if main() else 0)
