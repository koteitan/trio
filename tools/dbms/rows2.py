"""2 行（psi_0(Omega_omega) 未満）の変換を、機構を最小にして確かめる。

**結論（2026-08-24）**

BMS 2 行 -> DBMS の変換は、行列の上で `translate` とまったく同じ形の
2 分岐の構造再帰 `convD` で書ける（`stair` の imperative な親・影の管理は不要）。
読み `readD` も `translate` に**節を 1 つ足しただけ**である。

    readD (convD M 0 0 True False) True 0 = translate M

が、BMS 2 行標準形 5351 個（<=9 列）で全部成り立つ。必要な仮定は 3 つ:

    blockok 0 M   頭が深さ 0、全部 0 以上、行 0 は 1 段ずつ（Pair/Seqlex.lean）
    colOK M       どの列も 行1 <= 行0
    descOK M      同じ深さの後続の鎖では段が増えない（CNF の降下条件）

3 つとも 5351 個で違反 0。

`convD M 0 0 True False` は旧 `stair`（親と影を持ち回る手続き版）と**完全に一致**する。

残る穴: 像が DBMS 標準形でないものが 5351 個中 78 個ある
（`(0,0)(1,1)(1,0)(2,1)(2,0)` 型。DBMS 側の縮約 = 梯子の二役が要る）。

使い方:
    python3 rows2.py [列数上限]
"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse, show, diag, expand, isstd


# ---------------------------------------------------------------- 読み
def split(p, r):
    """引数（深さが p より大きい接頭辞）と後続に割る。"""
    i = 0
    while i < len(r) and p[0] < r[i][0]:
        i += 1
    return r[:i], r[i:]


def translate(cols):
    """BMS の読み（Pair/Term.lean の translate）。"""
    if not cols:
        return ('Z',)
    p, r = cols[0], cols[1:]
    A, B = split(p, r)
    return ('P', p[1], translate(A), translate(B))


def readD(cols, first=True, plev=0):
    """DBMS の読み。translate との違いは影を 1 本捨てる節だけ。"""
    if not cols:
        return ('Z',)
    p, r = cols[0], cols[1:]
    if first and p[1] == plev and r and r[0] == (p[0] + 1, p[1] + 1):
        return readD(r, True, plev)          # p は影
    A, B = split(p, r)
    return ('P', p[1], readD(A, True, p[1]), readD(B, False, p[1]))


# ---------------------------------------------------------------- 変換
def convD(M, d=0, plev=0, first=True, force=False):
    """BMS 2 行 -> DBMS 2 行。`translate` と同じ構造再帰。

    * `d` はいま書いているブロックの深さ、`plev` は親の段
    * `lad`: 段を 1 つ上げるのに影の列が要るとき（段が親の +1 で、
      その深さでは直接書けない、または親の列が影と読まれてしまうとき）
    * `force`: 親の列が影と読まれる危険があるので、影の形で書けという指示
    """
    if not M:
        return []
    p, r = M[0], M[1:]
    s = p[1]
    A, B = split(p, r)
    lad = first and s == plev + 1 and (d <= s or force)
    dd = d + 1 if lad else (s + 1 if (s > 0 and d <= s) else d)
    cols = [(d, plev), (d + 1, s)] if lad else [(dd, s)]
    return (cols
            + convD(A, dd + 1, s, True, (not lad) and first and s == plev)
            + convD(B, d, s, False, False))


# ---------------------------------------------------------------- 仮定
def colOK(M):
    return all(c[1] <= c[0] for c in M)


def descOK(M):
    """同じ深さの後続の鎖で段が増えない。"""
    if not M:
        return True
    p, r = M[0], M[1:]
    A, B = split(p, r)
    if B and B[0][1] > p[1]:
        return False
    return descOK(A) and descOK(B)


# ---------------------------------------------------------------- 補助
def show_term(t):
    return 'Z' if t[0] == 'Z' else 'P%d(%s,%s)' % (t[1], show_term(t[2]), show_term(t[3]))


def seqlex(a, b):
    for p, q in zip(a, b):
        if p != q:
            return p < q
    return len(a) < len(b)


def gen(ver, lim, nmax=3):
    """対角から展開して、`lim` 列以下の標準形を集める。"""
    res = set()
    dq = collections.deque(diag(ver, v, 2) for v in range(1, lim + 1))
    while dq:
        m = dq.popleft()
        if m in res or len(m) > lim:
            continue
        res.add(m)
        for n in range(1, nmax + 1):
            e = expand(m, n)
            if len(e) <= lim and e not in res:
                dq.append(e)
    return res


# ---------------------------------------------------------------- 検査
def main(lim=9):
    A = sorted(gen('BMS', lim), key=lambda m: (list(m), len(m)))   # seqlex 順
    print('BMS 2 行標準形 (<=%d 列): %d' % (lim, len(A)))
    print('  colOK  違反:', sum(1 for m in A if not colOK(m)))
    print('  descOK 違反:', sum(1 for m in A if not descOK(m)))

    W = [tuple(convD(list(m))) for m in A]
    print('  readD(convD M) != translate M:',
          sum(1 for m, w in zip(A, W) if readD(list(w)) != translate(list(m))))
    print('  単射:', len(set(W)) == len(W))
    print('  seqlex 順序保存 NG:',
          sum(1 for i in range(len(A) - 1) if not seqlex(W[i], W[i + 1])))

    ns = [(m, w) for m, w in zip(A, W) if not isstd(w, 'DBMS')]
    print('  像が DBMS 非標準:', len(ns), '（残る穴）')
    for m, w in ns[:3]:
        print('    ', show(m), '->', show(w))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 9)
