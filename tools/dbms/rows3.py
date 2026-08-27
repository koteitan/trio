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

**到達点（2026-08-27）**

| 検査 | 結果 |
|---|---|
| シート 3 行 z<=1 (1358 対) | **1338 一致**（不一致 20） |
| 生成 <=6 列 8387 個: 像が DBMS 標準形 | 違反 0 |
| 同: z=0 で 2 行版 convC と一致 | 違反 0 |
| 同: 単射 | 違反 0 |
| 同: 順序保存 | 違反 0 |

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


NOTLAST = (2, 2, 0)     # 「後ろにユニットを閉じない列がある」を表す番兵
ANCHOR = (1, 1, 0)      # アンカー（新しい加算ユニットの頭）


def closes_unit(nxt):
    """次の列がこの加算ユニットを閉じるか（rule.py の closes_unit と同じ）。

    閉じるのは (a) 次が無い (b) 次が根元に戻る（行 0 <= 1 かつ 行 2 = 0）。
    アンカー (1,1,0) は (b) に含まれる。閉じるなら分岐列は浅い。
    """
    return nxt is None or (nxt[0] <= 1 and nxt[2] == 0)


def Lat(L, k):
    """段の表 `L` の第 k 要素。表の外は 1 段ずつ伸ばして読む。"""
    if k < len(L):
        return L[k]
    if not L:
        return (0, 0, False, 0)
    a = L[-1]
    j = k - (len(L) - 1)
    return (a[0] + j, a[1], False, a[3] + j)


def is_branch(c):
    """分岐列 (a,1,0) (a>=2)。浅い／深いを選ぶのはこの型だけ。"""
    return c[1] == 1 and c[2] == 0 and c[0] >= 2


def dmap_at(st, k):
    """もとの深さ `k` が像で何段目になるか。表の外は 1 段ずつ伸ばす。"""
    m = st['dmap']
    if not m:
        return k
    return m[k] if k < len(m) else m[-1] + (k - len(m) + 1)


def copy_shift(block, e, ps0, prev0, nxt_after):
    """`block` の写し（深さ +1、行 1 は +e）。

    行 1 が上がるのは「親の段 `ps0` より深い柱」だけ。ただし分岐列 (a,1,0) は
    浅い／深いを選べるので、状態機械を同じ順に回して 1 本ずつ決める。
    もとのブロックで浅く書かれた柱は、写しでも行 1 が上がらない。
    """
    out, prev = [], prev0
    for i, c in enumerate(block):
        nxt = block[i + 1] if i + 1 < len(block) else nxt_after
        if c == ANCHOR:
            prev = 0
        if is_branch(c):
            shallow = (prev == 0) or closes_unit(nxt)
            prev = 0 if shallow else 1
            dl = 0 if shallow else (e if c[1] > ps0 else 0)
        else:
            dl = e if c[1] > ps0 else 0
        out.append((c[0] + 1, c[1] + dl, c[2]))
    return out


def contrPre(p, U, A, e, ps0, prev0, nxt_after):
    return copy_shift([p] + list(A) + list(U), e, ps0, prev0, nxt_after)


def conv3(M, d=0, L=(), F=(), ps=(0, 0), pw=(0, 0), first=True, force=False,
          st=None, nx=None):
    """設計 v9: 二重の梯子 ＋ 分岐列 (a,1,0) の 1 ビット状態機械。

    `L[k]` もとの行 1 の深さ `k` の祖先について
           (深い側の行 1, その行 2, 子に渡す force1, 浅い側の行 1)
           行 1 の影を立てると「深い側」だけが影の値に置き換わる。
    `F[k]` 行 1 の深さ `k` の次の柱がその行 1 ブロックの先頭か
    `st`   線形に持ち回る状態 {'ST': 祖先の鎖, 'prev': 直前の分岐列の選択}
    `nx`   このブロックの**後ろ**に来る列（ブロック分割で見失うので持ち回る）

    分岐列 (a,1,0) (a>=2) だけが浅い／深いを選ぶ（NOTES §6 の観測）。
        浅い <=> prev == 0 / 行列の末尾 / 次がアンカー (1,1,0)
    アンカー (1,1,0) を通過するたびに prev := 0。

    1 本の BMS 列は最大 3 本の柱になる:
        (d,   pw0,  pw1)       行 0 の影
        (dd,  base, pl2)       行 1 の影
        (dd', e1,   e2)        本体
    """
    if st is None:
        st = {'ST': (), 'prev': None, 'dmap': []}
    if not M:
        return []
    p, r = M[0], M[1:]
    v, s2 = p[1], p[2]
    A, B = split0(p, r)

    if v == 0:
        base_d = base_s = 0
        pl2, force1 = 0, False
    else:
        e = Lat(L, v - 1)
        base_d, pl2, force1, base_s = e[0] + 1, e[1], e[2], e[3] + 1
    first1 = F[v] if v < len(F) else True

    if p == (1, 1, 0):
        st['prev'] = 0
    if is_branch(p) and base_s != base_d:
        nxt = M[1] if len(M) > 1 else nx
        shallow = (st['prev'] == 0) or closes_unit(nxt)
        base = base_s if shallow else base_d
        st['prev'] = 0 if shallow else 1
    else:
        base = base_d

    lad1 = first1 and s2 == pl2 + 1 and (base <= s2 or force1)
    e1 = base + 1 if lad1 else (s2 + 1 if (s2 > 0 and base <= s2) else base)
    e2 = s2
    h1 = base if lad1 else e1
    lad0 = first and v == ps[0] + 1 and (d <= h1 or force)

    ST = st['ST']
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
    st['ST'] = ST
    st['dmap'] = st['dmap'][:p[0]] + [dd]      # もとの深さ -> 像の深さ

    fc = (not lad1) and first1 and s2 == pl2
    f0 = (not lad0) and first and (v, s2) == ps
    # 行 1 の影を立てたら、その影が「もとの行 1 の深さ v-1」の祖先を置き換える。
    # 浅い側（影を使わない選択肢）はもとの値を残しておく。
    if e1 == base + 1 and v >= 1:      # 行 1 が水増しされた（影を書いたかは問わない）
        Lb = L[:v - 1] + ((base, pl2, False, Lat(L, v - 1)[3]),)
    else:
        Lb = L
    LA = Lb[:v] + ((e1, s2, fc, e1),)
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
            # 写しの終わりの分岐列は、写しが吸収されるぶん深く書かれることがある。
            # 素直な「次の列 = q」と「深い側」の 2 通りを試す。
            for na in (q, NOTLAST):
                pre = contrPre(p, U, A, e, ps[0], st['prev'], na)
                if list(Aq[:len(pre)]) == pre:
                    break
            else:
                continue
            blk = [p] + list(A) + list(U)
            # 残りが「深く書かれた分岐列」で終わるか（NOTES §7 strip_lift の条件）
            deep_end = is_branch(blk[-1]) and pre[-1][1] > blk[-1][1]
            rest2 = list(Aq[len(pre):])
            if rest2:
                if rest2[0][0] < p[0] + 1:
                    continue
                if (rest2[0][0] == p[0] + 1
                        and (rest2[0][1], rest2[0][2]) >= (v + e, s2) and e == 0):
                    continue
            elif e == 0 or not deep_end:
                # 残余なしの縮約は「行 1 ずれ」かつ「残りが分岐列で終わる」ときだけ
                # （NOTES §7 の strip_lift の適用条件と同じ）
                continue
            Lr = L[:v] + (((base, pl2, fc, base) if e else (e1, s2, fc, e1)),)
            hd = lambda *ls: next((l[0] for l in ls if l), nx)
            # 写しは書かれないので、A から見た「次の列」は写しの後ろ
            # 写しは書かれないので、A から見た「次の列」は写しの後ろ。
            # 何も無くても「レベルが後で綴られている」ので末尾扱いにはしない。
            cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
                       U[0] if U else na)
            cU = conv3(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na)
            # 写しの真下（もとの深さ p[0]+1）なら影の位置、さらに深ければ
            # 「もとの深さ -> 像の深さ」の表で決める。
            rd = (d + 1 + e if (not rest2 or rest2[0][0] == p[0] + 1)
                  else dmap_at(st, rest2[0][0] - 1))
            cR = conv3(rest2, rd, Lr, (False,) * 12,
                       (v, s2), (e1, e2), False, False, st, hd(Bq))
            cB = conv3(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx)
            return cols + cA + cU + cR + cB

    cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
               B[0] if B else nx)
    cB = conv3(B, d, L, FA, (v, s2), (e1, e2), False, False, st, nx)
    return cols + cA + cB


def b2d3(M):
    return tuple(conv3(list(M)))


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
