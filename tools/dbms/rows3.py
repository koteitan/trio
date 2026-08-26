"""3 行 z<2 の BMS -> DBMS 変換を、設計 -> 検査のループで詰めるための道具。

BMS 3 行の列は (x,y,z) で z<=y<=x、いまは z<2 に制限する。
DBMS 3 行の列は z<y<x（0 は例外）。「弱い降下」を「強い降下」にするのが変換。

**土台になる観測（2026-08-26）**

    BMS でも DBMS でも、標準形の第 y 行の値は**その行の入れ子の深さ**に等しい。
    3 行 <=6 列で BMS 8387 個・DBMS 555 個、違反 0。

だから行 1 の値は保存されるものではなく、行 1 の木に影を挟めばその分ずれる。
2 行の変換を「行 (0,1)」と「行 (1,2)」の**二重**に効かせるのが設計 v6 以降。

**検査**（`main` が回す 4 つ）

  (1) 像が DBMS 標準形
  (2) 単射・順序保存
  (3) 性質 R: 任意の n に対し、ある m と n'>=n で 像<m> = 像(M<n'>)
  (4) z=0 の断片で 2 行版 `rows2.convC` と完全一致

**到達点（<=5 列 1018 個）**: (2) 違反 0、(4) 違反 0、(1) 違反 1、(3) 違反 74。

使い方:
    python3 rows3.py [列数上限]
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse, show, expand, isstd, cmpmat
from rows2 import convC as convC2


# ---------------------------------------------------------------- 生成
def gen3(ver, lim, zcap=None):
    """`lim` 列以下の標準形を全部。接頭辞が標準形であることを使う。"""
    cur = [()]
    out = []
    for _ in range(lim):
        nxt = []
        for S in cur:
            amax = (S[-1][0] + 1) if S else 0
            for a in range(amax + 1):
                bmax = a if ver == 'BMS' else max(a - 1, 0)
                for b in range(bmax + 1):
                    cmax = b if ver == 'BMS' else max(b - 1, 0)
                    if zcap is not None:
                        cmax = min(cmax, zcap)
                    for c in range(cmax + 1):
                        T = S + ((a, b, c),)
                        if isstd(T, ver):
                            nxt.append(T)
        cur = nxt
        out.extend(nxt)
    return out


def key(m):
    return ([v for c in m for v in c], len(m))


# ---------------------------------------------------------------- 木
def split0(p, r):
    """行 0 の引数ブロックと兄弟に割る。"""
    i = 0
    while i < len(r) and p[0] < r[i][0]:
        i += 1
    return r[:i], r[i:]


def translate3(cols):
    """BMS の読み（lean/Term.lean の translate）。段は対 (行1, 行2)。"""
    if not cols:
        return ('Z',)
    p, r = cols[0], cols[1:]
    A, B = split0(p, r)
    return ('P', (p[1], p[2]), translate3(A), translate3(B))


def olt3(a, b):
    """Three の順序（添字対 -> 引数 -> 後続）。"""
    if a[0] == 'Z':
        return b[0] != 'Z'
    if b[0] == 'Z':
        return False
    if a[1] != b[1]:
        return a[1] < b[1]
    if a[2] != b[2]:
        return olt3(a[2], b[2])
    return olt3(a[3], b[3])


# ---------------------------------------------------------------- 変換 v1
def shift1(B):
    return [(a + 1, b, c) for a, b, c in B]


def units_split(p, B, qlab):
    """`B` の先頭から「深さ `p[0]` の柱＋その引数ブロック」を、
    段の対が `qlab`（＝写しの先頭が持つ段の対）に等しい柱に出会うまで取る。

    2 行版は `p` そのものの並びしか数えなかった。深さ 1 では段が 0 か 1 しか
    ないので両者は一致するが、3 行では段の対が (1,0) のような中間の兄弟が
    入りうるので、そこで切れてしまうと縮約が発火しない。
    """
    k = 0
    while k < len(B):
        if B[k][0] != p[0]:
            break
        if (B[k][1], B[k][2]) == qlab:
            break
        t = k + 1
        while t < len(B) and p[0] < B[t][0]:
            t += 1
        k = t
    return B[:k], B[k:]


def predlab(y, z):
    """段の対の順序 (0,0)<(1,0)<(1,1)<(2,0)<(2,1)<... での 1 つ前。z<2 用。"""
    if z > 0:
        return (y, z - 1)
    if y >= 2:
        return (y - 1, 1)
    return (0, 0)


def shiftE(B, e, ps0):
    """写しのずれ。行 0 は必ず +1、行 1 は**親より深い段の柱だけ** +e。

    展開の delta は上昇行列 am が 1 の行にしか効かないので、行 1 が親の段
    `ps0` 以下の柱は行 1 が上がらない。
    """
    return [(a + 1, b + (e if b > ps0 else 0), c) for a, b, c in B]


def contrPre(p, U, A, e, ps0):
    return ([(p[0] + 1, p[1] + e, p[2])]
            + shiftE(A, e, ps0) + shiftE(U, e, ps0))


def ok_place(ST, x, w):
    """深さ `x` に行 1 が `w` の柱を置けるか（行 1 の値 = 行 1 の入れ子の深さ）。"""
    if w == 0:
        return True
    if x <= w:
        return False                      # DBMS は 行1 < 行0
    for y in range(min(x, len(ST)) - 1, -1, -1):
        if ST[y][0] < w:
            return ST[y][0] == w - 1
    return False


def fit(ST, d, w):
    """深さ `d` 以上で行 1 が `w` になれる最小の深さ。無ければ None。"""
    for x in range(d, len(ST) + 1):
        if ok_place(ST, x, w):
            return x
    return None


def conv3(M, d=0, L=(), F=(), ps=(0, 0), pw=(0, 0), first=True, force=False,
          ST=()):
    """設計 v8: 行 0 も行 1 も「入れ子の深さ」として扱い、行 1 の祖先を持ち回る。

    `L[k]` もとの行 1 の深さ `k` の祖先が像で持つ (行 1, 行 2, 子に渡す force1)
    `F[k]` 行 1 の深さ `k` の次の柱がその行 1 ブロックの先頭か
    `ST[x]` **像で**深さ `x` に居る祖先の (行 1, 行 2)（＝いまの祖先の鎖）

    行 1 の値は行 1 の入れ子の深さなので、行 1 が `w` の柱は、
    行 1 が `w` 未満の直近の祖先の行 1 がちょうど `w-1` になる深さにしか置けない。
    `ST` がそれを与える。

    1 本の BMS 列は最大 3 本の柱になる:
        (d,   pw0,  pw1)       行 0 の影
        (dd,  base, pl2)       行 1 の影
        (dd', e1,   e2)        本体

    戻り値は (柱の並び, 更新した ST)。
    """
    if not M:
        return [], ST
    p, r = M[0], M[1:]
    v, s2 = p[1], p[2]
    A, B = split0(p, r)

    if v == 0:
        base, pl2, force1 = 0, 0, False
    else:
        base, pl2, force1 = L[v - 1][0] + 1, L[v - 1][1], L[v - 1][2]
    first1 = F[v] if v < len(F) else True

    lad1 = first1 and s2 == pl2 + 1 and (base <= s2 or force1)
    e1 = base + 1 if lad1 else (s2 + 1 if (s2 > 0 and base <= s2) else base)
    e2 = s2
    h1 = base if lad1 else e1
    lad0 = first and v == ps[0] + 1 and (d <= h1 or force)

    cols = []
    if lad0:
        cols.append((d, pw[0], pw[1]))
        ST = ST[:d] + ((pw[0], pw[1]),)
        dd = d + 1
    else:
        dd = fit(ST, d, h1)
        if dd is None:
            dd = max(d, len(ST))
    if lad1:
        cols.append((dd, base, pl2))
        ST = ST[:dd] + ((base, pl2),)
        dd += 1
    if not ok_place(ST, dd, e1):
        x = fit(ST, dd, e1)
        if x is not None:
            dd = x
    cols.append((dd, e1, e2))
    ST = ST[:dd] + ((e1, e2),)

    fc = (not lad1) and first1 and s2 == pl2
    f0 = (not lad0) and first and (v, s2) == ps
    LA = L[:v] + ((e1, s2, fc),)
    FA = F[:v] + (False,)

    if lad0:
        for e in (0, 1):
            qlab = (ps[0] + e, ps[1])
            U, B2 = units_split(p, B, qlab)
            if not B2:
                continue
            q, r2 = B2[0], B2[1:]
            if (q[1], q[2]) != qlab or q[0] != p[0]:
                continue
            Aq, Bq = split0(q, r2)
            pre = contrPre(p, U, A, e, ps[0])
            if list(Aq[:len(pre)]) != pre:
                continue
            rest2 = list(Aq[len(pre):])
            if not (rest2 and rest2[0][0] == p[0] + 1
                    and (rest2[0][1], rest2[0][2]) < (v + e, s2)):
                continue
            # 写しが行 1 でもずれているとき（e=1）、写しの頭は行 1 の影が
            # 兼ねるので、残余の行 1 の親は影（= base）になる。
            Lr = L[:v] + (((base, pl2, fc) if e else (e1, s2, fc)),)
            cA, ST = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, ST)
            cU, ST = conv3(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, ST)
            cR, ST = conv3(rest2, d + 1 + e, Lr, (False,) * 12,
                           (v, s2), (e1, e2), False, False, ST)
            cB, ST = conv3(Bq, d, L, FA, (v, s2), (e1, e2), False, False, ST)
            return cols + cA + cU + cR + cB, ST

    cA, ST = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, ST)
    cB, ST = conv3(B, d, L, FA, (v, s2), (e1, e2), False, False, ST)
    return cols + cA + cB, ST


def b2d3(M):
    return tuple(conv3(list(M))[0])


# ---------------------------------------------------------------- 検査
def pad(M2):
    return tuple((a, b, 0) for a, b in M2)


def two(M3):
    return [(c[0], c[1]) for c in M3]


def check(f, A, nr=6, mm=10, nn=24, verbose=3):
    """(1) 像が DBMS 標準形 (2) 順序保存 (3) 性質 R (4) z=0 で 2 行版と一致。"""
    W = [f(M) for M in A]
    ns = [(M, N) for M, N in zip(A, W) if not isstd(N, 'DBMS')]
    inj = len(set(W)) == len(W)
    ordbad = [i for i in range(len(A) - 1) if cmpmat(W[i], W[i + 1]) >= 0]
    z0bad = [(M, N) for M, N in zip(A, W)
             if all(c[2] == 0 for c in M) and N != pad(convC2(two(M)))]
    rbad = []
    for M in A:
        if len(M) < 2:
            continue
        N = f(M)
        img = {tuple(expand(N, m)) for m in range(1, mm + 1)}
        for n in range(1, nr + 1):
            if not any(tuple(f(expand(M, np))) in img
                       for np in range(n, n + nn + 1)):
                rbad.append((M, n, N))
                break
    print('  対象 %d 個' % len(A))
    print('  (1) 像が DBMS 非標準 : %d' % len(ns))
    for M, N in ns[:verbose]:
        print('        %-34s -> %s' % (show(M), show(N)))
    print('  (2) 単射 : %s   順序保存の違反 : %d' % (inj, len(ordbad)))
    for i in ordbad[:verbose]:
        print('        %-34s -> %s' % (show(A[i]), show(W[i])))
        print('        %-34s -> %s' % (show(A[i + 1]), show(W[i + 1])))
    print('  (3) 性質 R の違反 : %d' % len(rbad))
    for M, n, N in rbad[:verbose]:
        print('        %-30s -> %s  (n=%d で覆えない)' % (show(M), show(N), n))
    print('  (4) z=0 で 2 行版と食い違い : %d' % len(z0bad))
    for M, N in z0bad[:verbose]:
        print('        %-34s -> %-30s (2 行版 %s)'
              % (show(M), show(N), show(pad(convC2(two(M))))))
    return len(ns) + len(ordbad) + len(rbad) + len(z0bad)


def main(lim=5):
    t0 = time.time()
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    print('BMS 3 行 z<2 標準形 (<=%d 列): %d  (%.1fs)' % (lim, len(A), time.time() - t0))
    n = check(b2d3, A)
    print('合計違反 %d  (%.1fs)' % (n, time.time() - t0))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
