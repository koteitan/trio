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


# ---------------------------------------------------------------- R12 ブロックごとの一様オフセット
def _topt(c):
    nz = [y for y in range(len(c)) if c[y] > 0]
    return nz[-1] if nz else -1


def R12(m: Mat, Y: int | None = None, tfun=None) -> Mat:
    """行 0 の根で切ったブロックごとに、そのブロックの深さ t だけ「階段」を前置して
    一様オフセット (t, t-1, ..., 0) を足す。

    psi(W_(wk)) 族などはこれで完全に一致する:
      BMS  (0,0,0)(1,1,1)(2,1,0)(3,2,1)
      -> 前置 (0)(1) ＋ 各列に (2,1,0) を足す
      =    (0)(1)(2,1)(3,2,1)(4,2)(5,3,1)   （正解）
    """
    if Y is None:
        Y = rows(m)
    out = []
    for b in _blocks(m):
        t = max((_topt(c) for c in b), default=-1)
        if tfun is not None:
            t = tfun(b, t)
        if t <= 0:
            out.extend(b)
            continue
        off = tuple(max(t - y, 0) for y in range(Y))
        out.extend(diag('DBMS', t, Y))
        out.extend(tuple(c[y] + off[y] for y in range(Y)) for c in b)
    return tuple(out)


# ---------------------------------------------------------------- R13 深さを状態にした階段
def R13(m: Mat, Y: int | None = None, deep=None) -> Mat:
    """R7 の階段に「レベル（影の深さ）」の状態を足したもの。

    観測: 印の無い列 (2,1,0) の像の行 1 値は、その列が行 0 の木で葉なら 1、
    子孫を持つなら 2 になる。つまり使う影の深さが 1 段変わる。
    deep(x) が真なら shadow(P_t(x), t+1) を使う。
    """
    if Y is None:
        Y = rows(m)
    if not m:
        return ()
    P = pim(m)

    def has_desc0(x):
        for z in range(x + 1, len(m)):
            j = z
            while j != -1:
                if j == x:
                    return True
                j = P[j][0]
        return False

    if deep is None:
        deep = has_desc0
    out: list = []
    img: list = [None] * len(m)
    sh: dict = {}

    def shadow(p: int, y: int) -> int:
        if y <= 0:
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
            out.append(tuple([0] * Y)); img[x] = len(out) - 1; continue
        t = nz[-1]
        lvl = t + 1 if (t < Y - 1 and deep(x)) else t
        base = shadow(P[x][t], lvl) if P[x][t] != -1 else None
        T = [0] * Y
        for y in range(1, t + 1):
            p = P[x][y]
            T[y] = out[shadow(p, y)][y] + 1 if p != -1 else 0
        p0 = P[x][0]
        T[0] = out[img[p0]][0] + 1 if p0 != -1 else 0
        if base is not None:
            for y in range(0, t + 1):
                T[y] = max(T[y], out[base][y] + 1)
        out.append(tuple(T)); img[x] = len(out) - 1
    return tuple(out)


# ---------------------------------------------------------------- R15 一様オフセット + 深さ状態
def R15(m: Mat, Y: int | None = None, mode='desc') -> Mat:
    """R12（ブロック単位の一様オフセット）に「行 1 のオフセットは列ごと」を足す。

    行 0 のオフセットはブロックの深さ t で一様、行 1 のオフセットは
    その列が「深い」かどうかで t-1 か 0。深さの判定は mode で切り替える:
      'desc'   行 0 の木で子孫を持つ
      'mark'   自分に行 2 の印がある
      'both'   どちらか
    """
    if Y is None:
        Y = rows(m)
    if not m:
        return ()
    P = pim(m)

    def has_desc0(x):
        for z in range(x + 1, len(m)):
            j = z
            while j != -1:
                if j == x:
                    return True
                j = P[j][0]
        return False

    def deep(x, c):
        d = has_desc0(x)
        mk = any(c[y] > 0 for y in range(2, Y))
        return {'desc': d, 'mark': mk, 'both': d or mk}[mode]

    out = []
    base = 0
    for b in _blocks(m):
        t = max((_topt(c) for c in b), default=-1)
        if t <= 0:
            out.extend(b); base += len(b); continue
        out.extend(diag('DBMS', t, Y))
        for i, c in enumerate(b):
            o1 = (t - 1) if deep(base + i, c) else 0
            col = [c[0] + t] + [c[1] + o1 if Y > 1 else 0] + list(c[2:])
            out.append(tuple(col[:Y]))
        base += len(b)
    return tuple(out)


# ================================================================ R23（現時点の最良）
# 設計:
#   1. 階段（影の列）: 行 y (y>=1) の親になる列は DBMS では「行 y-1 で 1 段深い影」で
#      なければならない。足りなければ影を挿入する（親ごとに 1 回、使い回す）。
#   2. 深さ（レベル）: 影を何段まで使うかは列ごとに変わる。実測すると
#      **分岐するのは (a,1,0) 型の列だけ**で、他は常に t 段（浅い方）。
#      (a,1,0) (a>=2) は「次の列」で決まる（シートで曖昧 0.66%）。
#   3. 縮約: BMS は「コピー 1 個 + 印」で書くところを DBMS は「印」だけで書くので、
#      出力に逐語重複が出る。標準形になるまで重複区間を 1 つずつ落とす。
def _blockctx(m: Mat, x: int):
    """列 x が属する行 0 ブロックの中で、x より前／後の行 1 値の最大。"""
    L = len(m)
    b = 0
    for i in range(x + 1):
        if m[i][0] == 0:
            b = i
    nb = L
    for i in range(x + 1, L):
        if m[i][0] == 0:
            nb = i
            break
    pm = max([m[z][1] for z in range(b, x)], default=0)
    lm = max([m[z][1] for z in range(x + 1, nb)], default=0)
    return pm, lm


def is_anchor(n) -> bool:
    """次の列が「アンカー」（新しい加算ユニットの頭 = 対角上の列）か。"""
    return n is not None and n[0] == n[1] and n != (1, 1, 1)


def depth_rule(c, nxt, pm: int = 0, lm: int = 0) -> int:
    """列 c の像が使う影の深さ（t からの追加段数）。0 か 1。

    分岐するのは (a,1,0) 型 (a>=2) の列だけ。浅くなるのは
      * 行列の末尾（次の列が無い）
      * 次がアンカー（新しい加算ユニットの頭）
      * そのブロックで**既に自分より深いレベルが名指し済みで、後にはもう出てこない**
        （pm > c[1] かつ lm == 0）
    pm/lm は同じ行 0 ブロックで、その列より前／後に現れる行 1 の最大値。
    """
    if not (len(c) > 2 and c[1] == 1 and c[2] == 0 and c[0] >= 2):
        return 0
    if nxt is None:
        return 0
    if is_anchor(nxt):
        return 0
    if pm > c[1] and lm == 0:
        return 0
    return 1


def _stair(m: Mat, Y: int, depth) -> Mat:
    P = pim(m)
    out: list = []
    img: list = [None] * len(m)
    sh: dict = {}

    def shadow(p, y):
        if y <= 0:
            return img[p]
        k = (p, y)
        if k in sh:
            return sh[k]
        s = shadow(p, y - 1)
        if out[s][y - 1] >= 1:
            r = s
        else:
            out.append(tuple(out[s][z] + 1 if z < y else 0 for z in range(Y)))
            r = len(out) - 1
        sh[k] = r
        return r

    for x, c in enumerate(m):
        nz = [y for y in range(Y) if c[y] > 0]
        if not nz:
            out.append(tuple([0] * Y)); img[x] = len(out) - 1; continue
        t = nz[-1]
        lvl = min(Y - 1, t + depth(x, c))
        base = shadow(P[x][t], lvl) if P[x][t] != -1 else None
        T = [0] * Y
        for y in range(1, t + 1):
            p = P[x][y]
            T[y] = out[shadow(p, y)][y] + 1 if p != -1 else 0
        p0 = P[x][0]
        T[0] = out[img[p0]][0] + 1 if p0 != -1 else 0
        if base is not None:
            for y in range(0, t + 1):
                T[y] = max(T[y], out[base][y] + 1)
        out.append(tuple(T)); img[x] = len(out) - 1
    return tuple(out)


def _absorb_cands(Z: Mat):
    """吸収: Z = A ++ [P] ++ B ++ [Q] で B が A の接尾辞のコピー、
    Q が P を上書きする（行 0 が同じで行 1 が大きい）なら A ++ [Q] に縮む。

    BMS は「レベル 1 の印を書いてから、レベルを上げ直して書き直す」が、
    DBMS は最初から上のレベルで書くので、この形の重複が出る。
    """
    n = len(Z)
    for j in range(n - 1, 0, -1):
        Q = Z[j]
        for i in range(j - 1, -1, -1):
            P = Z[i]
            if P[0] != Q[0] or Q[1] <= P[1]:
                continue
            L = j - i - 1
            if L <= 0 or i - L < 0:
                continue
            if Z[i - L:i] == Z[i + 1:j]:
                yield Z[:i] + Z[j:]


def dedup(Z: Mat, limit: int = 40) -> Mat:
    """標準形になるまで縮約する。逐語重複の削除 → 吸収 の順に試す。"""
    for _ in range(limit):
        if isstd(Z, 'DBMS'):
            return Z
        nxt = None
        n = len(Z)
        for L in range(n // 2, 0, -1):
            for i in range(n - L, L - 1, -1):
                if Z[i - L:i] == Z[i:i + L]:
                    cand = Z[:i] + Z[i + L:]
                    if isstd(cand, 'DBMS'):
                        return cand
                    if nxt is None:
                        nxt = cand
        for cand in _absorb_cands(Z):
            if isstd(cand, 'DBMS'):
                return cand          # 吸収は標準形になるときだけ使う
        if nxt is None:
            return Z
        Z = nxt
    return Z


def R23(m: Mat, Y: int | None = None) -> Mat:
    if Y is None:
        Y = rows(m)
    if not m:
        return ()
    def dep(x, c):
        pm, lm = _blockctx(m, x)
        return depth_rule(c, m[x + 1] if x + 1 < len(m) else None, pm, lm)
    return dedup(_stair(m, Y, dep))
