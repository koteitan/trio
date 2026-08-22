"""BMS(BM4) と DBMS の共通エンジン。

展開規則は両者で同一（BM4）。違うのは標準形の判定（対角）だけ:
  BMS : diag[x][y] = x
  DBMS: diag[x][y] = max(x-y, 0)
"""
from __future__ import annotations
from functools import lru_cache

Col = tuple
Mat = tuple  # tuple[Col, ...]


# ---------- parse / print ----------
def parse(s: str, Y: int | None = None) -> Mat:
    s = s.strip()
    if s == "" or s.lower().startswith("empty"):
        return ()
    cols = []
    for part in s.split(")"):
        part = part.strip()
        if not part:
            continue
        assert part.startswith("("), part
        body = part[1:].strip()
        cols.append(tuple(int(v) for v in body.split(",")) if body else (0,))
    if Y is None:
        Y = max(len(c) for c in cols)
    return tuple(tuple(list(c) + [0] * (Y - len(c)))[:Y] for c in cols)


def show(m: Mat, trim: bool = False) -> str:
    if not m:
        return "Empty Matrix"
    out = []
    for c in m:
        cc = list(c)
        if trim:
            while len(cc) > 1 and cc[-1] == 0:
                cc.pop()
        out.append("(" + ",".join(str(v) for v in cc) + ")")
    return "".join(out)


def rows(m: Mat) -> int:
    return len(m[0]) if m else 0


# ---------- comparison ----------
def flat(m: Mat):
    return [v for c in m for v in c]


def cmpmat(a: Mat, b: Mat) -> int:
    fa, fb = flat(a), flat(b)
    for x, y in zip(fa, fb):
        if x != y:
            return 1 if x > y else -1
    if len(fa) != len(fb):
        return 1 if len(fa) > len(fb) else -1
    return 0


# ---------- BM4 expansion (shared) ----------
def pim(S):
    """parent index matrix (yaBMS c/bms.c と同じ)。-1 は親なし。"""
    X = len(S); Y = len(S[0])
    P = [[-1]*Y for _ in range(X)]
    for x in range(X):
        c = S[x][0]
        px = x-1
        while px >= 0 and S[px][0] >= c:
            px -= 1
        P[x][0] = px
        for y in range(1, Y):
            c = S[x][y]
            if c == 0:
                P[x][y] = -1
                continue
            px = P[x][y-1]
            while px != -1 and S[px][y] >= c:
                px = P[px][y-1]
            P[x][y] = px
    return P


_exp_memo = {}


def expand(S: Mat, n: int) -> Mat:
    k = (S, n)
    r = _exp_memo.get(k)
    if r is None:
        r = _expand_raw(S, n)
        _exp_memo[k] = r
    return r


def _expand_raw(S: Mat, n: int) -> Mat:
    if not S:
        return ()
    X = len(S); x = X-1; Y = len(S[0])
    if all(v == 0 for v in S[x]):
        return tuple(S[:x])
    t = max(y for y in range(Y) if S[x][y] > 0)
    P = pim(S)
    r = P[x][t]
    if r == -1:
        return tuple(S[:x])
    delta = [(S[x][y]-S[r][y]) if y < t else 0 for y in range(Y)]
    bp = x - r
    nzs = t+1
    am = [[0]*nzs for _ in range(bp)]
    for y in range(nzs):
        am[0][y] = 1
    for xx in range(1, bp):
        for y in range(nzs):
            pp = P[r+xx][y]
            am[xx][y] = 0 if pp < r else am[pp-r][y]
    out = list(S[:r])
    for a in range(n):
        for xx in range(bp):
            col = []
            for y in range(Y):
                v = S[r+xx][y]
                if y < t and am[xx][y]:
                    v += a*delta[y]
                col.append(v)
            out.append(tuple(col))
    return tuple(out)


# ---------- diagonals ----------
def diagcol(ver: str, x: int, Y: int) -> Col:
    if ver == "BMS":
        return tuple(x for _ in range(Y))
    return tuple(max(x-y, 0) for y in range(Y))


def diag(ver: str, k: int, Y: int) -> Mat:
    return tuple(diagcol(ver, x, Y) for x in range(k))


# ---------- standardness ----------
_isstd_memo = {}


def isstd(b: Mat, ver: str) -> bool:
    k = (b, ver)
    if k in _isstd_memo:
        return _isstd_memo[k]
    r = _isstd_raw(b, ver)
    _isstd_memo[k] = r
    return r


def _isstd_raw(b: Mat, ver: str) -> bool:
    if not b:
        return True
    Y = rows(b)
    s = None
    for x in range(len(b)):
        dc = diagcol(ver, x, Y)
        for y in range(Y):
            v = b[x][y]
            if v > dc[y]:
                return False
            if v < dc[y]:
                s = tuple(list(b[:x]) +
                          [tuple(list(dc[:y]) + [v+1] + [0]*(Y-y-1))])
                break
        if s is not None:
            break
    if s is None:
        return True
    return reach(s, b)


def reach(a: Mat, b: Mat, limit: int = 10000) -> bool:
    for _ in range(limit):
        c = cmpmat(a, b)
        if c == 0:
            return True
        if c < 0:
            return False
        n = fsindex(a, b)
        if n is None:
            return False
        a = expand(a, n)
    raise RuntimeError("reach: too deep")


def fsindex(a: Mat, b: Mat, nmax: int | None = None) -> int:
    """b <= a[n] となる最小の n（expand(a,n) は n について単調増加）。

    expand(a,n) は n に比例して長くなるので、n は len(b) 程度で頭打ちにできる。
    これを付けないと二分探索が巨大な行列を作って一気に遅くなる。"""
    if nmax is None:
        nmax = max(64, len(b) + 4)
    if cmpmat(expand(a, 0), b) >= 0:
        return 0
    lo, hi = 0, 1
    while hi <= nmax:
        if cmpmat(expand(a, hi), b) >= 0:
            break
        lo = hi
        hi *= 2
    else:
        return None
    while lo+1 < hi:
        mid = (lo+hi)//2
        if cmpmat(expand(a, mid), b) >= 0:
            hi = mid
        else:
            lo = mid
    return hi


# ---------- address ----------
def rootindex(m: Mat, ver: str) -> int:
    Y = rows(m)
    k = 0
    while k <= 2000:
        if cmpmat(diag(ver, k, Y), m) >= 0:
            return k
        k += 1
    raise RuntimeError("rootindex too big")


def address(m: Mat, ver: str):
    Y = rows(m)
    k = rootindex(m, ver)
    a = diag(ver, k, Y)
    path = []
    while cmpmat(a, m) != 0:
        n = fsindex(a, m)
        if n is None:
            raise RuntimeError("address: not reachable %s" % show(m))
        path.append(n)
        a = expand(a, n)
        if len(path) > 5000:
            raise RuntimeError("address: too long")
    return k, path


def replay(ver: str, k: int, path, Y: int) -> Mat:
    a = diag(ver, k, Y)
    for n in path:
        a = expand(a, n)
    return a
