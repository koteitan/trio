"""トリオ数列（3 行バシク行列）の実行可能モデル。

展開規則は BM4:
  ユーザーブログ:Koteitan/バシク行列の数式的定義 — バシク行列システム(BM4) の節
  （~/proofs/Koteitan_バシク行列の数式的定義 _ 巨大数研究 Wiki _ Fandom.html）

    B_xy^(a) = S_(r+x)y + a Δ_y A_xy
    Δ_y      = S_(X-1)y - S_ry   (y < t) / 0 (y >= t)
    A_xy     = 1 (∃a  r = (P_y)^a (r+x)) / 0 (otherwise)
    t        = max{y | S_(X-1)y > 0}
    r        = P_t(X-1)
    P_y(x)   = max{p | S_py < S_xy ∧ ∃a>0 p = (P_{y-1})^a(x)}  (y > 0)
               max{p | S_py < S_xy ∧ p < x}                     (y = 0)

行数 Y は一般に取れる（Y=1 で原始数列、Y=2 でペア数列、Y=3 でトリオ数列）。
コピー数は展開ごとの引数 n で与える（公式の f(n)+1 個は n := f(n)+1 で再現できる）。
"""

from __future__ import annotations

Col = tuple  # 長さ Y の自然数タプル


def parent(S: list[Col], y: int, x: int) -> int | None:
    """P_y(x)。存在しなければ None。

    y > 0 の候補は P_{y-1} の真の反復像。連鎖は添字降順に並ぶので、
    近い順に見て最初に条件をみたすものが max。
    """
    if y == 0:
        for p in range(x - 1, -1, -1):
            if S[p][0] < S[x][0]:
                return p
        return None
    p = parent(S, y - 1, x)
    while p is not None:
        if S[p][y] < S[x][y]:
            return p
        p = parent(S, y - 1, p)
    return None


def is_ancestor(S: list[Col], y: int, r: int, j: int) -> bool:
    """∃a>=0  r = (P_y)^a(j)。"""
    while j is not None:
        if j == r:
            return True
        j = parent(S, y, j)
    return False


def expand(S: list[Col], n: int) -> list[Col]:
    """S[n]: 悪い部分のコピーを n 個（a = 0..n-1）並べる。

    末尾の列が全零なら末尾を落とすだけ。バッドルートが無い場合も同様
    （標準形では起きない。Lean 側の Pred 分岐に対応する保険）。
    """
    if not S:
        return []
    X = len(S)
    x = X - 1
    Y = len(S[0])
    if all(v == 0 for v in S[x]):
        return list(S[:x])
    t = max(y for y in range(Y) if S[x][y] > 0)
    r = parent(S, t, x)
    if r is None:
        return list(S[:x])
    delta = [(S[x][y] - S[r][y]) if y < t else 0 for y in range(Y)]
    asc = [[is_ancestor(S, y, r, r + xx) for y in range(Y)] for xx in range(x - r)]
    out = list(S[:r])
    for a in range(n):
        for xx in range(x - r):
            out.append(tuple(
                S[r + xx][y] + (a * delta[y] if asc[xx][y] else 0)
                for y in range(Y)))
    return out


def diag(Y: int, v: int, zcap: int | None = None) -> list[Col]:
    """対角列 (0,..)(1,..)...(v,..)。zcap を与えると最下行をその値で頭打ちにする。

    トリオの z<2 断片の生成元は diag(3, v, zcap=1)
    = (0,0,0)(1,1,1)(2,2,1)...(v,v,1)。これは完全な BM4 では
    (0,0,0)(1,1,1)(2,2,2)[v] に等しい（tools/verify_trio.py で検査）。
    """
    out = []
    for j in range(v + 1):
        c = [j] * Y
        if zcap is not None:
            c[Y - 1] = min(j, zcap)
        out.append(tuple(c))
    return out
