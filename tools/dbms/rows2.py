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


def shift1(B):
    """ブロックを 1 段深くする（行 0 に +1）。"""
    return [(a + 1, b) for a, b in B]


def units_split(p, B):
    """`B` の先頭から「`p` + その引数ブロック」を取れるだけ取る。

    旧版は `p` そのものが並ぶ本数（`sibRun`）しか数えなかった。
    兄弟が**引数を持つ**とそこで切れてしまい、縮約が発火しない。
    11 列の反例
    `(0,0)(1,1)(2,2)(1,1)(2,1)(1,0)(2,1)(3,2)(2,1)(3,1)(2,0)`
    はこれが原因だった。
    """
    k = 0
    while k < len(B) and B[k] == p:
        s = k + 1
        while s < len(B) and p[0] < B[s][0]:
            s += 1
        k = s
    return B[:k], B[k:]


def contrPre(p, U, A):
    """縮約で使い回される前置き: 本体の列 + その引数 + 兄弟のユニット（全部 1 段深く）。"""
    return [(p[0] + 1, p[1])] + shift1(A) + shift1(U)


def convC(M, d=0, plev=0, first=True, force=False):
    """`convD` に**縮約（梯子の二役）**を足したもの。シート 264 件に 264/264 一致。

    梯子を敷いた直後の後続が「段 plev のノードで、その引数が
    いま書いた（梯子＋本体＋兄弟）とそっくり同じ」で、さらにそのあとに
    同じ深さで段が下がる列が来るとき、DBMS では 2 度目を書かない。
    """
    if not M:
        return []
    p, r = M[0], M[1:]
    s = p[1]
    A, B = split(p, r)
    lad = first and s == plev + 1 and (d <= s or force)
    dd = d + 1 if lad else (s + 1 if (s > 0 and d <= s) else d)
    cols = [(d, plev), (d + 1, s)] if lad else [(dd, s)]
    if lad:
        U, B2 = units_split(p, B)
        if B2:
            q, r2 = B2[0], B2[1:]
            Aq, Bq = split(q, r2)
            if q[1] + 1 == s and q[0] == p[0]:
                pre = contrPre(p, U, A)
                if list(Aq[:len(pre)]) == pre:
                    rest2 = list(Aq[len(pre):])
                    if rest2 and rest2[0][0] == p[0] + 1 and rest2[0][1] < s:
                        return (cols + convC(A, dd + 1, s, True, False)
                                + convC(U, d, s, False, False)
                                + convC(rest2, dd, s, False, False)
                                + convC(Bq, d, s, False, False))
    return (cols + convC(A, dd + 1, s, True, (not lad) and first and s == plev)
                 + convC(B, d, s, False, False))


def _sibLen(t, l):
    n = 0
    while n < len(l) and l[n] == t:
        n += 1
    return n


def _deepLen(a, l):
    n = 0
    while n < len(l) and a <= l[n][0]:
        n += 1
    return n


def readC(cols, first=True, plev=0):
    """`readD` に**梯子二役の枝**を足した読み。`readC(convC M) = translate M`。"""
    if not cols:
        return ('Z',)
    p, rest = cols[0], cols[1:]
    shadow = first and p[1] == plev and rest and rest[0] == (p[0] + 1, p[1] + 1)
    top, tail = (rest[0], rest[1:]) if shadow else (p, rest)
    arg_l, after = split(top, list(tail))
    arg = readC(arg_l, True, top[1])
    U, r2 = units_split(top, after)
    if shadow and r2 and r2[0][0] == top[0] and r2[0][1] < top[1]:
        m = _deepLen(top[0], r2)
        inner = readC([top] + list(arg_l) + list(U) + list(r2[:m]), True, p[1])
        succ = ('P', p[1], inner, readC(r2[m:], False, plev))
        for ua in reversed(_unit_args(top, U)):
            succ = ('P', top[1], readC(ua, True, top[1]), succ)
        return ('P', top[1], arg, succ)
    return ('P', top[1], arg, readC(after, False, top[1]))


def _unit_args(top, U):
    """兄弟ユニットの引数ブロックを並べる。"""
    out, k = [], 0
    while k < len(U):
        s = k + 1
        while s < len(U) and top[0] < U[s][0]:
            s += 1
        out.append(list(U[k + 1:s]))
        k = s
    return out


def untranslate(t, d=0):
    """`translate` の逆（項 -> BMS の行列）。"""
    if t[0] == 'Z':
        return []
    return [(d, t[1])] + untranslate(t[2], d + 1) + untranslate(t[3], d)


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


def gen(ver, lim):
    """`lim` 列以下の標準形を**全部**集める。

    標準形の接頭辞は標準形なので（7774 個で違反 0 を確認）、
    1 列ずつ伸ばしながら `isstd` で篩えば漏れなく数え上げられる。
    対角からの BFS は展開の n を打ち切ると取りこぼす（旧版はこれで数を誤った）。
    """
    cur = [()]
    out = set()
    for _ in range(lim):
        nxt = []
        for S in cur:
            amax = (S[-1][0] + 1) if S else 0
            for a in range(amax + 1):
                bmax = a if ver == 'BMS' else max(a - 1, 0)
                for b in range(bmax + 1):
                    T = S + ((a, b),)
                    if isstd(T, ver):
                        nxt.append(T)
                        out.add(T)
        cur = nxt
    return out


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
    print('  像が DBMS 非標準:', len(ns), '（縮約が要る）')
    for m, w in ns[:3]:
        print('    ', show(m), '->', show(w))

    print('convC（縮約あり）:')
    V = [tuple(convC(list(m))) for m in A]
    print('  readC(convC M) != translate M:',
          sum(1 for m, v in zip(A, V) if readC(list(v)) != translate(list(m))))
    print('  像が DBMS 非標準:', sum(1 for v in V if not isstd(v, 'DBMS')))
    print('  単射:', len(set(V)) == len(V))
    print('  seqlex 順序保存 NG:',
          sum(1 for i in range(len(A) - 1) if not seqlex(V[i], V[i + 1])))

    print('全射（DBMS 標準形 -> readC -> untranslate -> convC で戻るか）:')
    for k in range(3, lim + 1):
        D = gen('DBMS', k)
        bad = sum(1 for N in D if tuple(convC(untranslate(readC(list(N))))) != N)
        print('  <=%d 列: %d 個中 戻らない %d' % (k, len(D), bad))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 9)
