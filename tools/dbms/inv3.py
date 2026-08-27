"""d2b3: DBMS 3 行標準形 -> BMS 3 行標準形（読み戻し）。

2 行では `readC (convC M) = translate M` が主定理の 1 つで、単射も順序保存も
そこから出た。3 行でも同じ道具が要る。ここでは項を経由せず、行列の上で
直接読み戻す。

**土台**（NOTES §「3 行の標準形についての実測」）

    標準形の第 y 行の値は、その行の入れ子の深さに等しい。
    行 y の親は「行 y-1 の親の鎖をたどって最初に自分より行 y が小さくなる柱」。

だから読み戻しは 3 段でよい:

  (i)   影の柱（行 0 の影・行 1 の影）を見分けて落とす。
  (ii)  残った柱の行 0 を、刈り込んだ木の深さで数え直す。
  (iii) 行 1 を「行 1 の祖先の鎖のうち**行 1 の影でない**柱の本数」で数え直す。
        行 2 は変換で保存される（conv3 は e2 = s2）のでそのまま。

(iii) の理由: 行 1 の影 (dd,base,pl2) は本体 (dd+1,base+1,s2) の行 1 の親で、
その影の行 1 の親がもとの BMS の行 1 の親になる。影だけ数えなければ元に戻る。
行 0 の影は親の段をそのまま写した柱なので、行 1 の鎖では 1 本ぶん数える
（親の値に戻るだけ）。

**測った結果（2026-08-27）**

影の見分け（(i)）は**誤り 0**。落ちるのは**縮約（梯子の二役）だけ**。

| 検査 | 結果 |
|---|---|
| 影の見分け 生成 <=6 列 8387 個 = 65327 柱 | 誤り **0** |
| 影の見分け シート 1354 対 = 13533 柱 | 誤り **0** |
| `d2b3(b2d3(M)) == M`  <=5 列 1018 個 | 1013（縮約 5 件だけ落ちる） |
| 同 <=6 列 8387 個 | 8343（縮約 44 件だけ落ちる） |
| 同・**縮約が起きない行列に限れば** | 1013/1013 ・ **8343/8343** |
| `d2b3(D) == B` シート 1358 対 | 1022 |
| 同・縮約なし かつ b2d3 がシートと一致する 1021 対 | **1021/1021** |

つまり `d2b3(b2d3(M)) = M` は、縮約が起きない限り**全数で成り立つ**。
d2b3 は像だけを見る関数なので、これはその範囲での `b2d3` の**単射性の証明**に
なる（像の集合の大きさを数えるのとは別の、構成的な保証）。

縮約が起きた行列では、写しの `q + pre` が像に書かれないので、像から落ちた列を
復元しないと戻らない。`d2b3x` は候補を構造的に並べて前向き写像で 1 つに絞る版。

| 検査 | d2b3 | d2b3x |
|---|---|---|
| 生成 <=6 列の縮約 44 件 | 0 | 41 |
| シート 1358 対 | 1022 | 1061 |
| DBMS 標準形 <=5 列 100 個に逆像 | 85 | **100** |
| 同 <=6 列 528 個 | 376 | 522 |
| 同 <=7 列 3514 個 | 2058 | 3380 |

**まだ無いもの**: 縮約の残余の切れ目 (jR,jB) を**像だけから**決める規則。
342 サイトで測ると、前向き写像で篩えば通る候補は必ず 1 つだけだが、
「BMS 標準形であること」だけを条件にすると候補が 3〜9 個残り、
最短・最長・seqlex 最小・jR 最大／最小のどれで選んでも正解にならない
（342 件中それぞれ 25/4/25/4/29 件しか当たらない）。ここが次の一手。

使い方:
    python3 inv3.py          往復・シート・全射の全数検査（約 15 秒）
    python3 inv3.py x        縮約を戻す版 d2b3x も測る
"""
import sys, os, time, inspect
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse, show, isstd, cmpmat
import rows3
from rows3 import gen3, key, split0

S0, S1, BODY = 'S0', 'S1', 'B'


# ---------------------------------------------------------------- 木
def par0i(N, i):
    """柱 i の行 0 の親の添字（左で行 0 がより小さい直近の柱）。無ければ -1。"""
    for j in range(i - 1, -1, -1):
        if N[j][0] < N[i][0]:
            return j
    return -1


def anc0(N):
    return [par0i(N, i) for i in range(len(N))]


def par1i(N, P0, i):
    """柱 i の行 1 の親（行 0 の祖先の鎖で最初に行 1 が小さくなる柱）。"""
    j = P0[i]
    while j != -1 and N[j][1] >= N[i][1]:
        j = P0[j]
    return j


# ---------------------------------------------------------------- (i) 影の見分け
def is_s0(N, P0, i):
    """行 0 の影: 第一子で、段の対が親と同じで、次の柱が (+1,+1,+0)。

    conv3 の行 0 の影は (d, pw0, pw1)（親の段の対の写し）で、その次に
    本体か行 1 の影が (d+1, pw0+1, pw1) と来る（lad0 は v == ps[0]+1 を要求
    するので、次の柱の行 1 はちょうど 1 つ大きい）。
    生成 <=6 列 65327 柱・シート 13533 柱で、偽陽性 0・偽陰性 0。
    """
    j = P0[i]
    if j != i - 1 or j < 0 or i + 1 >= len(N):
        return False
    if (N[i][1], N[i][2]) != (N[j][1], N[j][2]):
        return False
    return tuple(b - a for a, b in zip(N[i], N[i + 1])) == (1, 1, 0)


def is_s1(N, P0, i):
    """行 1 の影: 第一子で、次の柱が (+1,+1,+1)、**影が要る**、**親が段-1**。

    * 影が要る ⟺ 行 1 <= 行 2 + 1。次の柱の行 2 は c+1 なので、影を抜くと
      本体は（行 1 = b, 行 2 = c+1）になる。b <= c+1 なら DBMS の z<y を破る
      ＝影なしでは書けない。b > c+1 なら影は要らないので、その柱は本体である。
    * 親が段-1: 行 1 の影 (dd, base, pl2) は base = 行 1 の親の段 + 1 で書かれる。
      第一子なので行 0 の親が行 1 の親でもあり、その段はちょうど base-1。

    2 つの条件はどちらも要る（片方だけでは偽陽性が残る）:

    | 条件 | 生成 <=6 列 65327 柱 | シート 13533 柱 |
    |---|---|---|
    | 差 (+1,+1,+1) だけ | 偽陽性 646 | 偽陽性 646 |
    | ＋「影が要る」 | 0 | 偽陽性 17 |
    | ＋「親が段-1」 | 偽陽性 386 | 0 |
    | 両方 | **0** | **0** |
    """
    j = P0[i]
    if j != i - 1 or i + 1 >= len(N):
        return False
    if tuple(b - a for a, b in zip(N[i], N[i + 1])) != (1, 1, 1):
        return False
    return N[i][1] <= N[i][2] + 1 and N[j][1] == N[i][1] - 1


def roles_of(N):
    """像だけを見た役割づけ。像の列と 1:1 の 'S0'/'S1'/'B' の並び。"""
    N = list(N)
    P0 = anc0(N)
    out = []
    for i in range(len(N)):
        if is_s0(N, P0, i):
            out.append(S0)
        elif is_s1(N, P0, i):
            out.append(S1)
        else:
            out.append(BODY)
    return out


# ---------------------------------------------------------------- (ii)(iii) 数え直し
def prep(N):
    """役割 rs、行 0 の親 P0、行 1 の深さ Y、刈り込んだ木の深さ Dp。"""
    N = list(N)
    rs = roles_of(N)
    P0 = anc0(N)
    Y = [0] * len(N)
    for i in range(len(N)):
        if N[i][1] == 0:
            Y[i] = 0
            continue
        j = par1i(N, P0, i)
        Y[i] = (0 if j == -1 else Y[j]) + (0 if rs[i] == S1 else 1)
    Dp = [0] * len(N)
    for i in range(len(N)):
        j = P0[i]
        Dp[i] = 0 if j == -1 else Dp[j] + (0 if rs[j] != BODY else 1)
    return rs, P0, Y, Dp


def rebuild(N, rs, Y, Dp):
    return tuple((Dp[i], Y[i], N[i][2]) for i in range(len(N)) if rs[i] == BODY)


def d2b3(N):
    """DBMS 3 行標準形 -> BMS 3 行標準形（**縮約は戻さない**版）。"""
    N = tuple(N)
    rs, P0, Y, Dp = prep(N)
    return rebuild(N, rs, Y, Dp)


# ---------------------------------------------------------------- 縮約を戻す
def blk_end(N, i):
    """柱 i の部分木の終わり（i より深くない柱が来るところ）。"""
    d = N[i][0]
    for t in range(i + 1, len(N)):
        if N[t][0] <= d:
            return t
    return len(N)


def uncontract(N, pp, i0, jR, jB, e, prev0, na, ysh):
    """行 0 の影 i0 のブロックで縮約を戻す。

    conv3 の縮約の枝は、BMS の

        [p] + A + U + [q] + pre + rest2 + Bq          pre = 写し([p]+A+U)

    のうち **[q] + pre を書かない**。像に残るのは
    cols(影+本体) + cA + cU + cR で、`cR`（= rest2 の像）はブロックの**後ろ側**に
    来る。だから像のブロックを [i0,jR) = 共有部（= [p]+A+U）と
    [jR,jB) = 残余（= rest2）に割り、q と写しを作り直せばよい。

    * `q` の段の対は (親の行 1 + e, 親の行 2) = (Y[i0]+e, N[i0][2])
    * 写しは `rows3.copy_shift`（前向きと同じ関数）
    * 残余の行 0 は「刈り込んだ深さ + 1」（q が 1 段割り込むぶん）
    """
    rs, P0, Y, Dp = pp
    col = lambda t: (Dp[t], Y[t], N[t][2])
    head = [col(t) for t in range(0, i0) if rs[t] == BODY]
    blk = [col(t) for t in range(i0, jR) if rs[t] == BODY]
    if not blk:
        return None
    res = [(Dp[t] + 1, Y[t] + (e if ysh and Y[t] > Y[i0] else 0), N[t][2])
           for t in range(jR, jB) if rs[t] == BODY]
    tail = [col(t) for t in range(jB, len(N)) if rs[t] == BODY]
    q = (blk[0][0], Y[i0] + e, N[i0][2])
    cp = rows3.copy_shift(blk, e, Y[i0], prev0, na)
    return tuple(head + blk + [q] + cp + res + tail)


PARAMS = [(e, p, n, y) for e in (1, 0) for p in (1, 0)
          for n in (None, rows3.NOTLAST) for y in (True, False)]


def d2b3x(N, verify=None):
    """縮約を戻す版。候補を構造的に並べ、`verify` で 1 つに絞る。

    `verify(M) -> bool` の既定は「前向き写像 `rows3.b2d3` で像に戻ること」。
    つまりこれは**読み戻しではなく逆像の構成**（2 行の `onto.py` と同じ立場）。
    残余の切れ目 (jR,jB) を像だけから決める規則はまだ見つかっていないので、
    そこだけ探索している。342 サイトで測ると、通る候補は**必ず 1 つだけ**
    （BMS 標準形であることだけを条件にすると 3 個前後に絞れない）。
    """
    N = tuple(N)
    if verify is None:
        verify = lambda M: rows3.b2d3(M) == N
    R = d2b3(N)
    if verify(R):
        return R
    pp = prep(N)
    rs = pp[0]
    for i0 in [t for t in range(len(N)) if rs[t] == S0]:
        end = blk_end(N, i0)
        b = i0 + 1 + (1 if i0 + 1 < len(N) and rs[i0 + 1] == S1 else 0)
        for jR in range(b + 1, end + 1):
            for jB in range(jR, end + 1):
                for e, p, na, ysh in PARAMS:
                    M = uncontract(N, pp, i0, jR, jB, e, p, na, ysh)
                    if M is not None and verify(M):
                        return M
    return R


# ---------------------------------------------------------------- 正解の役割（追跡）
_SIG = inspect.signature(rows3.conv3)
_ORIG = rows3.conv3
_ORES = rows3.conv_resid
_STACK, _TOP, _INRES = [], [], [0]


def _tr(*a, **k):
    """`rows3.conv3` の薄いラッパ。自分が書いた柱と役割を記録する。

    再帰は module global の `conv3` を通るので、差し替えれば全部拾える。
    `cols` は返り値の**接頭辞**で、残りは子の返り値をこの順に並べたもの。
    """
    bd = _SIG.bind(*a, **k)
    bd.apply_defaults()
    A = bd.arguments
    if A.get('st') is None:
        A['st'] = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(A['M'])}
    if not A['M']:
        return []
    fr = {'kids': 0, 'roles': []}
    _STACK.append(fr)
    try:
        out = _ORIG(**A)
    finally:
        _STACK.pop()
    n = len(out) - fr['kids']
    cols = out[:n]
    if n == 3:
        rs = [S0, S1, BODY]
    elif n == 2:
        s0 = (A['first'] and cols[0][0] == A['d']
              and (cols[0][1], cols[0][2]) == tuple(A['pw']))
        rs = [S0 if s0 else S1, BODY]
    elif n == 1:
        rs = [BODY]
    else:
        raise AssertionError('cols %d 本' % n)
    my = rs + fr['roles']
    if _STACK:
        _STACK[-1]['kids'] += len(out)
        _STACK[-1]['roles'].extend(my)
    else:
        _TOP.append((tuple(out), my))
    return out


def trace_roles(M):
    """(像, 正解の役割の並び, 縮約の回数) を返す。"""
    global _TOP
    _TOP = []
    nres = [0]

    def tres(*a, **k):
        nres[0] += 1
        _INRES[0] += 1
        try:
            return _ORES(*a, **k)
        finally:
            _INRES[0] -= 1
    rows3.conv3, rows3.conv_resid = _tr, tres
    try:
        out = tuple(rows3.conv3(list(M)))
    finally:
        rows3.conv3, rows3.conv_resid = _ORIG, _ORES
    assert len(_TOP) == 1 and _TOP[0][0] == out
    return out, _TOP[0][1], nres[0]


# ---------------------------------------------------------------- 検査
def check_gen(lim, xtra=False, verbose=3):
    A = gen3('BMS', lim, zcap=1)
    rok = cok = ok = okx = ncontr = 0
    cols = colerr = 0
    bad = []
    for M in A:
        N, rs, nc = trace_roles(M)
        pr = roles_of(N)
        rok += (pr == rs)
        cols += len(rs)
        colerr += sum(1 for x, y in zip(rs, pr) if x != y)
        ncontr += (nc > 0)
        good = (d2b3(N) == tuple(M))
        ok += good
        if nc == 0:
            cok += good
        if xtra:
            okx += (d2b3x(N) == tuple(M))
        if not good and len(bad) < verbose:
            bad.append((M, N, rs, pr))
    print('BMS 3 行 z<2 標準形 <=%d 列: %d 個（うち縮約が起きるもの %d）'
          % (lim, len(A), ncontr))
    print('  影の見分け: 行列 %d/%d 一致   柱 %d 本中 誤り %d'
          % (rok, len(A), cols, colerr))
    print('  d2b3(b2d3(M)) == M : %d/%d   （縮約なしに限れば %d/%d）'
          % (ok, len(A), cok, len(A) - ncontr))
    if xtra:
        print('  d2b3x（縮約を戻す）  : %d/%d' % (okx, len(A)))
    for M, N, rs, pr in bad:
        print('    %-34s -> %s' % (show(M), show(N)))
        print('      真 %s' % ' '.join(rs))
        print('      予 %s' % ' '.join(pr))
    return ok, len(A)


def check_sheet(xtra=False, verbose=3):
    import sheet3
    T = sheet3.load(1)
    ok = okx = cok = ncontr = nfwd = 0
    bad = []
    for row, b, d in T:
        N, rs, nc = trace_roles(b)
        if N != tuple(d):
            nfwd += 1
        ncontr += (nc > 0)
        good = (d2b3(d) == tuple(b))
        ok += good
        if nc == 0:
            cok += good
        if xtra:
            okx += (d2b3x(tuple(d)) == tuple(b))
        if not good and len(bad) < verbose:
            bad.append((row, b, d))
    print('シート 3 行 z<=1: %d 対（b2d3 が外す %d、縮約が起きる %d）'
          % (len(T), nfwd, ncontr))
    print('  d2b3(D) == B : %d/%d   （縮約なしに限れば %d/%d）'
          % (ok, len(T), cok, len(T) - ncontr))
    if xtra:
        print('  d2b3x（縮約を戻す） : %d/%d' % (okx, len(T)))
    for row, b, d in bad:
        print('  行%-5d D %s' % (row, show(d)))
        print('        正 %s' % show(b))
        print('        誤 %s' % show(d2b3(d)))
    return ok, len(T)


def check_dbms(lim, verbose=3):
    """逆向き: DBMS 標準形をぜんぶ読み戻して、前向きで戻るか（全射の検査）。"""
    D = gen3('DBMS', lim, zcap=1)
    std = back = backx = 0
    for N in D:
        R = d2b3(N)
        std += isstd(R, 'BMS')
        b = (rows3.b2d3(R) == tuple(N))
        back += b
        if not b:
            backx += (rows3.b2d3(d2b3x(N)) == tuple(N))
    print('DBMS 3 行 z<2 標準形 <=%d 列: %d 個' % (lim, len(D)))
    print('  d2b3(N) が BMS 標準形     : %d' % std)
    print('  b2d3(d2b3(N)) == N        : %d' % back)
    print('  d2b3x まで使えば逆像あり  : %d' % (back + backx))
    return back + backx, len(D)


def main(xtra=False):
    t0 = time.time()
    for L in (5, 6):
        check_gen(L, xtra)
    check_sheet(xtra)
    for L in (5, 6, 7):
        check_dbms(L)
    print('%.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main('x' in sys.argv[1:])
