"""BMS -> DBMS の「素朴な構文的推測」ルール。

R1: 先頭に DBMS 対角の長さ Y-1 の接頭辞 (0)(1)(2,1)... を付け、
    もとの各列 (a_0,...,a_{Y-1}) を (a_0+(Y-1), a_1+(Y-2), ..., a_{Y-1}+0) にずらす。
    根拠: BMS の (0^Y)(1^Y) が DBMS の (0)(1)(2,1)...(Y,Y-1,...,1) に対応するため。

R2: R1 を「行 0 が 0 の列で切ったブロック（＝順序数の和の項）」ごとに適用して連結。
    f は和について加法的なので R1 より筋がよい……はずだが、単項ブロックで壊れる。
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import Mat, diag, rows


def R1(m: Mat, Y: int | None = None) -> Mat:
    if Y is None:
        Y = rows(m)
    if not m:
        return ()
    off = tuple(Y - 1 - y for y in range(Y))
    return diag('DBMS', Y - 1, Y) + tuple(
        tuple(c[y] + off[y] for y in range(Y)) for c in m)


def _blocks(m: Mat):
    out, cur = [], []
    for c in m:
        if c[0] == 0 and cur:
            out.append(tuple(cur)); cur = []
        cur.append(c)
    if cur:
        out.append(tuple(cur))
    return out


def R2(m: Mat, Y: int | None = None) -> Mat:
    if Y is None:
        Y = rows(m)
    return tuple(c for b in _blocks(m) for c in R1(b, Y))


# ---------------------------------------------------------------- R7
from core import pim


def R7(m: Mat, Y: int | None = None) -> Mat:
    """「影つき階段」規則（本命の予想）。

    BMS の列 x を DBMS の 1 列 T に写すが、行 y (y>=1) の親になる列は DBMS では
    「行 y-1 で 1 段深い影の列」でなければならない。足りなければ影の列を挿入する
    （これが階段）。影は使い回されるので、同じ親に対する挿入は 1 回だけ。

      shadow(p, 0) = img[p]
      shadow(p, y) = shadow(p, y-1)                     … 行 y-1 の値が 1 以上なら
                   = 新しい列 shadow(p,y-1)+（行 0..y-1 に +1）  … さもなくば挿入
      T[y] = out[shadow(P_y(x), y)][y] + 1   (1 <= y <= t)
      T[0] = max(out[img[P_0(x)]][0], out[shadow(P_t(x), t)][0]) + 1
    """
    if Y is None:
        Y = rows(m)
    if not m:
        return ()
    P = pim(m)
    out: list = []
    img: list = [None] * len(m)
    sh: dict = {}

    def shadow(p: int, y: int) -> int:
        if y == 0:
            return img[p]
        key = (p, y)
        if key in sh:
            return sh[key]
        s = shadow(p, y - 1)
        if out[s][y - 1] >= 1:
            r = s
        else:
            col = [out[s][z] + 1 if z < y else 0 for z in range(Y)]
            out.append(tuple(col))
            r = len(out) - 1
        sh[key] = r
        return r

    for x, c in enumerate(m):
        nz = [y for y in range(Y) if c[y] > 0]
        if not nz:
            out.append(tuple([0] * Y))
            img[x] = len(out) - 1
            continue
        t = nz[-1]
        base = shadow(P[x][t], t) if P[x][t] != -1 else None
        T = [0] * Y
        for y in range(1, t + 1):
            p = P[x][y]
            T[y] = out[shadow(p, y)][y] + 1 if p != -1 else 0
        p0 = P[x][0]
        T[0] = out[img[p0]][0] + 1 if p0 != -1 else 0
        if base is not None:
            for y in range(0, t + 1):
                T[y] = max(T[y], out[base][y] + 1)
        out.append(tuple(T))
        img[x] = len(out) - 1
    return tuple(out)


# ---------------------------------------------------------------- R8 = R7 + 余分なコピーの縮約
from core import expand, isstd, pim as _pim


def _badroot(Z):
    X = len(Z); x = X - 1; Y = len(Z[0])
    if all(v == 0 for v in Z[x]):
        return None, None
    t = max(y for y in range(Y) if Z[x][y] > 0)
    r = _pim(Z)[x][t]
    if r == -1:
        return None, None
    return r, x - r


def reduce_once(Z):
    """良い部分の末尾がバッド部のコピー 1 個ぶんなら落とす（順序数は不変）。

    expand(Z, n) = G' ++ B ++ n個 、 expand(Z_red, n+1) = G' ++ (n+1)個 なので
    expand(Z_red, n+1) == expand(Z, n) が全 n で成り立てば sup は等しい。
    """
    r, bp = _badroot(Z)
    if r is None or r < bp:
        return None
    cand = Z[:r - bp] + Z[r:]
    for n in range(4):
        if expand(cand, n + 1) != expand(Z, n):
            return None
    return cand


def normalize(Z, limit=64):
    """接頭辞ごとに「余分なコピー 1 個」を落とす縮約を、標準形になるまで繰り返す。"""
    for _ in range(limit):
        if isstd(Z, 'DBMS'):
            return Z
        done = False
        for L in range(len(Z), 1, -1):
            c = reduce_once(Z[:L])
            if c is not None:
                Z = c + Z[L:]
                done = True
                break
        if not done:
            return Z
    return Z


def R8(m: Mat, Y: int | None = None) -> Mat:
    return normalize(R7(m, Y))


# ---------------------------------------------------------------- R9 = R7 + 一般の重複縮約
from core import cmpmat


def cofinal(Z, W, K=3, K2=6):
    """{Z[n]} と {W[m]} が互いに共終か（＝ sup が等しいか）を有限近似で判定。

    展開結果はどちらも DBMS 側の行列なので cmpmat で直接比較できる。
    reduce_once の `expand(Z_red,n+1)==expand(Z,n)` は delta=0 の場合しか通らないが、
    こちらは基本列の形が違っていても sup の一致を拾える。
    """
    ez = [expand(Z, n) for n in range(1, K2 + 1)]
    ew = [expand(W, m) for m in range(1, K2 + 1)]
    for n in range(K):
        if not any(cmpmat(ez[n], w) <= 0 for w in ew):
            return False
    for m in range(K):
        if not any(cmpmat(ew[m], z) <= 0 for z in ez):
            return False
    return True


def dup_candidates(Z):
    """Z[i-L:i] == Z[i:i+L] な逐語重複を 1 個落とした候補（長い方・右から）。"""
    n = len(Z)
    out = []
    for L in range(n // 2, 0, -1):
        for i in range(n - L, L - 1, -1):
            if Z[i - L:i] == Z[i:i + L]:
                out.append(Z[:i] + Z[i + L:])
    return out


def normalize2(Z, limit=24):
    """非標準形のあいだ、共終性を保つ逐語重複の削除を繰り返す。"""
    for _ in range(limit):
        if isstd(Z, 'DBMS'):
            return Z
        nxt = None
        for c in dup_candidates(Z):
            if cofinal(Z, c):
                nxt = c
                break
        if nxt is None:
            return Z
        Z = nxt
    return Z


def R9(m: Mat, Y: int | None = None) -> Mat:
    return normalize2(R7(m, Y))


# ---------------------------------------------------------------- R10 = R7 + 縮約（2 つの健全性判定の OR）
def accept(Z, c):
    if cofinal(Z, c):
        return True
    for n in range(4):                      # delta=0 型（添字が 1 ずれるだけ）
        if expand(c, n + 1) != expand(Z, n):
            return False
    return True


def normalize3(Z, limit=24):
    for _ in range(limit):
        if isstd(Z, 'DBMS'):
            return Z
        nxt = None
        for c in dup_candidates(Z):
            if accept(Z, c):
                nxt = c
                break
        if nxt is None:
            return Z
        Z = nxt
    return Z


def R10(m: Mat, Y: int | None = None) -> Mat:
    return normalize3(R7(m, Y))
