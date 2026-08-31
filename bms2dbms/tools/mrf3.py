# -*- coding: utf-8 -*-
"""mrf3 —— 変換関数 `bmsToDbms` の純 Python 版。

出所は MrredsharkFan 氏の `conv.js`:
<https://github.com/MrredsharkFan/w-Y-global-lngi>

`conv.js` の `bmsToDbms` / `dbmsToBms` を、そのままの構造で写したもの。
行数は一般（`n` は列の長さ）で、2 行でも 3 行でも動く。

    b2d(M)   BMS -> DBMS
    d2b(N)   DBMS -> BMS
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


# ---------------------------------------------------------------- 列の道具
def normalize(matrix):
    """全列を共通の行数（最低 2）に 0 で揃える。"""
    if not matrix:
        raise ValueError('行列が空')
    m = max(2, max(len(c) for c in matrix))
    out = []
    for c in matrix:
        c = list(c) + [0] * (m - len(c))
        if any((not isinstance(v, int)) or v < 0 for v in c):
            raise ValueError('列は非負整数だけ: %s' % (c,))
        out.append(c)
    return out


def last_positive_row(col):
    """正の値がある最後の行の番号（1 始まり）。全部 0 なら 0。"""
    for i in range(len(col) - 1, -1, -1):
        if col[i] > 0:
            return i + 1
    return 0


def inc_prefix(col, count):
    if count < 0 or count > len(col):
        raise ValueError('接頭辞の長さが不正: %d' % count)
    return [v + (1 if i < count else 0) for i, v in enumerate(col)]


def dec_prefix(col, count):
    if count < 0 or count > len(col):
        raise ValueError('接頭辞の長さが不正: %d' % count)
    out = list(col)
    for i in range(count):
        if out[i] == 0:
            raise ValueError('先頭 %d 個を 1 ずつ減らせない: %s' % (count, col))
        out[i] -= 1
    return out


def inc_row(col, row):
    if row < 1 or row > len(col):
        raise ValueError('行番号が不正: %d' % row)
    out = list(col)
    out[row - 1] += 1
    return out


def zero_from(col, row):
    if row < 1 or row > len(col) + 1:
        raise ValueError('0 埋め開始行が不正: %d' % row)
    return [(0 if i >= row - 1 else v) for i, v in enumerate(col)]


def first_row_col(v, n):
    return [v] + [0] * (n - 1)


def cmp_arr(a, b):
    for x, y in zip(a, b):
        if x < y: return -1
        if x > y: return 1
    return (len(a) > len(b)) - (len(a) < len(b))


def cmp_seq(A, B):
    for a, b in zip(A, B):
        c = cmp_arr(a, b)
        if c: return c
    return (len(A) > len(B)) - (len(A) < len(B))


# ---------------------------------------------------------------- 祖先索引
class Anc:
    """行ごとの親と祖先。行 0 の親は 1 つ前の列、行 r の親は
    「行 r-1 の祖先のうち、その行の値が真に小さい直近のもの」。"""

    def __init__(self, columns):
        if not columns:
            raise ValueError('空の行列に祖先関係は作れない')
        n = len(columns[0])
        m = len(columns)
        self.n, self.m = n, m
        self.par = [[None] * m for _ in range(n + 1)]
        self.anc = [[frozenset()] * m for _ in range(n + 1)]
        for c in range(m):
            self.par[0][c] = c - 1 if c > 0 else None
            self.anc[0][c] = frozenset(range(c))
        for r in range(1, n + 1):
            ri = r - 1
            for c in range(m):
                p = None
                for cand in sorted(self.anc[r - 1][c], reverse=True):
                    if columns[cand][ri] < columns[c][ri]:
                        p = cand
                        break
                self.par[r][c] = p
                self.anc[r][c] = (self.anc[r][p] | {p}) if p is not None else frozenset()

    def has_anc(self, elem, row, anc):
        return anc in self.anc[row][elem]

    def par_is(self, elem, row, par):
        return self.par[row][elem] == par

    def chain(self, elem, row):
        if row == 0:
            return list(range(elem - 1, -1, -1))
        out, q = [], self.par[row][elem]
        while q is not None:
            out.append(q)
            q = self.par[row][q]
        return out


# ---------------------------------------------------------------- BMS -> DBMS
def b2d(matrix, step_limit=1000000):
    """BMS 標準形 -> DBMS 標準形。`conv.js` の `bmsToDbms`。"""
    cols = normalize([list(c) for c in matrix])
    n = len(cols[0])
    index = steps = 0
    while index < len(cols):
        steps += 1
        if steps > step_limit:
            raise ValueError('段数の上限を超えた')
        x = cols[index]
        k = last_positive_row(x)
        if k >= n - 1:
            index += 1
            continue
        y = inc_prefix(x, k + 1)
        z = inc_row(y, k + 2)
        xs = index + 1
        if xs >= len(cols) or cmp_arr(cols[xs], z) < 0:
            index += 1
            continue
        xe = xs
        while xe < len(cols) and cmp_arr(cols[xe], z) >= 0:
            xe += 1
        anc = Anc(cols)
        xp = []
        for cur in range(xs, xe):
            t = cols[cur]
            rows = [r for r in range(0, k + 2) if anc.has_anc(cur, r, index)]
            if not rows:
                raise ValueError('l が取れない: x@%d t@%d' % (index + 1, cur + 1))
            l = max(rows)
            if cur == xe - 1:                      # ブロックの最後の柱
                if l < 0 or l >= n:
                    raise ValueError('t[l+1] が読めない: l=%d n=%d' % (l, n))
                if anc.par_is(cur, l, index) and t[l] == 0:
                    l -= 1
            if l < 0:
                raise ValueError('最後の柱の調整で l が負になった')
            xp.append(inc_prefix(t, l))
        rest = cols[xe:]
        comp = [y] + xp + [first_row_col(y[0] + 1, n)]
        del cols[xs:xe]
        if cmp_seq(comp, rest) > 0:
            cols[xs:xs] = [y] + xp
        index += 1
    return [tuple(c) for c in cols]


# ---------------------------------------------------------------- DBMS -> BMS
def d2b(matrix):
    """DBMS 標準形 -> BMS 標準形。`conv.js` の `dbmsToBms`。"""
    cols = normalize([list(c) for c in matrix])
    n = len(cols[0])
    index = len(cols) - 1
    while index >= 0:
        x = cols[index]
        if x[n - 2] > 0:
            index -= 1
            continue
        k = last_positive_row(x)
        if k + 2 > n:
            raise ValueError('先頭 k+2 行が作れない: k=%d n=%d' % (k, n))
        y = inc_prefix(x, k + 1)
        z = inc_prefix(y, k + 2)
        yi = index + 1
        ms = index + 2
        if (yi >= len(cols) or cols[yi] != y or ms >= len(cols)
                or cmp_arr(cols[ms], z) < 0):
            index -= 1
            continue
        anc = Anc(cols)
        xp = []
        cur = ms
        last = None
        xend = cur
        while True:
            if cur >= len(cols) or cmp_arr(cols[cur], z) < 0:
                xend = cur
                break
            t = cols[cur]
            rows = [r for r in range(0, k + 2) if anc.has_anc(cur, r, yi)]
            if not rows:
                raise ValueError('l が取れない（逆変換）: t@%d' % (cur + 1))
            l = max(rows)
            stopped = (l <= k) and anc.par_is(cur, l + 1, index)
            tp = dec_prefix(t, l)
            if stopped:
                tp = zero_from(tp, l + 2)
            xp.append(tp)
            cur += 1
            last = (t, l, stopped)
            if stopped:
                xend = cur
                break
        nxt = cols[xend] if xend < len(cols) else None
        keep1 = nxt is not None and cmp_arr(nxt, first_row_col(z[0], n)) >= 0
        keep2 = (last is not None and last[0][last[1]] == 0
                 and anc.par_is(xend - 1, last[1], yi))
        keep3 = (last is not None and last[2] and (last[1] + 1) < n
                 and last[0][last[1] + 1] > 0)
        if keep1 or keep2 or keep3:
            cols[index + 1:index + 1] = xp
        else:
            cols[index + 1:xend] = xp
        index -= 1
    return [tuple(c) for c in cols]
