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


# ---------------------------------------------------------------- readC の 3 行版
def _units3(top, B):
    """`B` の先頭から「`top` と同じ柱 ＋ その引数ブロック」を取れるだけ取る。
    `rows2.units_split` の 3 行版（比較を 3 成分に広げただけ）。"""
    k = 0
    while k < len(B) and B[k] == top:
        s = k + 1
        while s < len(B) and top[0] < B[s][0]:
            s += 1
        k = s
    return B[:k], B[k:]


def _deep3(a, l):
    n = 0
    while n < len(l) and a <= l[n][0]:
        n += 1
    return n


def _unitargs3(top, U):
    """兄弟ユニットの引数ブロックを並べる。"""
    out, k = [], 0
    while k < len(U):
        s = k + 1
        while s < len(U) and top[0] < U[s][0]:
            s += 1
        out.append(list(U[k + 1:s]))
        k = s
    return out


CONTR = [True]          # 縮約の節を切る旗（測定用）
FIRE = []               # 発火の記録（測定用）


def readC3(cols, first=True, plev=(0, 0)):
    """`rows2.readC` の 3 行版。影を捨てる節 2 つ ＋ **縮約の節**。

    `readD` 相当（`L14Read.survivors`）に足りないのは縮約の節である。DBMS の 1 列が
    BMS の複数列に化ける場合があり、捨てるだけの読みでは長さが足りない。
    """
    if not cols:
        return ('Z',)
    # 3 行では影が 2 本続くことがある（対角がそう）ので、続く限り捨てる。
    p = cols[0]
    cur = list(cols)
    nsh = 0
    while True:
        q, r = cur[0], cur[1:]
        h = r[0] if r else None
        s1 = first and (q[1], q[2]) == plev and h == (q[0] + 1, q[1] + 1, q[2])
        s2 = first and q[2] == plev[1] and h == (q[0] + 1, q[1] + 1, q[2] + 1)
        if not (s1 or s2):
            break
        cur = r
        nsh += 1
    shadow = nsh > 0
    top, tail = cur[0], list(cur[1:])
    i = 0
    while i < len(tail) and top[0] < tail[i][0]:
        i += 1
    arg_l, after = tail[:i], tail[i:]
    tlab = (top[1], top[2])
    plab = (p[1], p[2])
    arg = readC3(arg_l, True, tlab)
    U, r2 = _units3(top, after)
    # 引き金の柱は「親の段」に戻る柱でなければならない。2 行では段が 1 本なので
    # `< top[1]` と `== plev` が一致するが、3 行では一致しない（前者は出すぎる）。
    if (CONTR[0] and shadow and r2 and r2[0][0] == top[0]
            and (r2[0][1], r2[0][2]) == plab):
        m = _deep3(top[0], r2)
        FIRE.append((tuple(cols), tuple(top), tuple(p), nsh, tuple(U), tuple(r2), m))
        inner = readC3([top] + list(arg_l) + list(U) + list(r2[:m]), True, plab)
        succ = ('P', plab, inner, readC3(r2[m:], False, plev))
        for ua in reversed(_unitargs3(top, U)):
            succ = ('P', tlab, readC3(ua, True, tlab), succ)
        return ('P', tlab, arg, succ)
    return ('P', tlab, arg, readC3(after, False, tlab))


def untranslate3(t, d=0):
    """`translate3` の逆（項 -> BMS の 3 行行列）。"""
    if t[0] == 'Z':
        return []
    return [(d, t[1][0], t[1][1])] + untranslate3(t[2], d + 1) + untranslate3(t[3], d)


def rank12(B):
    """行 0（深さ）はそのまま、行 1・行 2 だけその行の木での順位に直す。
    `untranslate3` が付ける深さは入れ子の深さ＝順位なので、直す必要が無い。"""
    B = [tuple(c) for c in B]
    return [(B[j][0], rankB(B, 1, j), rankB(B, 2, j)) for j in range(len(B))]


def readBMS(N):
    """DBMS 標準形 -> BMS 標準形。構造再帰（縮約つき）で形を作り、段を順位に直す。"""
    return rank12(untranslate3(readC3([tuple(c) for c in N])))
