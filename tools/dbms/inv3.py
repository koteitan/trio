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

**縮約（梯子の二役）＝「同じ区間をもう一度読む」（2026-08-27）**

2 行の `readC` は、縮約を「写しを作り直す」のではなく
**同じ像の柱をもう一度、1 段深い文脈で読む**ことで戻していた
（`inner = readC ([top] + arg_l + U + r2[:m])`）。3 行でも同じことが成り立つ。

conv3 の縮約は BMS の

    [p] + A + U + [q] + pre + rest2 + Bq        pre = 写し([p]+A+U)

から **[q] + pre を書かない**。像に残るのは 共有部（= [p]+A+U の像）と
残余（= rest2 の像）だけである。ここで

    **q の影** = e=1 なら行 1 の影、e=0 なら行 0 の影

を「影ではなく実際の柱」として数え直すと、同じ像の区間が

    e=0 のとき 写し（行 1 のずれ無し）、e=1 のとき 写し（行 1 が +1）

に化ける。行 0 も行 1 も**深さを数えるだけ**なので、
「q の影を 1 本数える」だけで `copy_shift` の状態機械（浅い／深い、`prev`、
`na`、`after_w` …）を一切再現しなくてよい。よって復元は

    R = head + blk + [q] + two + tail
      blk = 像[i0,jR) を**ふつうに**読む          （= [p]+A+U）
      two = 像[i0,jB) を**q の影を数えて**読む    （= pre + rest2）
      q   = (blk[0] の深さ, 行1(i0) + e, 像[i0] の行 2)
      head/tail = 像[0,i0) / 像[jB,) をふつうに読む

の 1 行で済む。`copy_shift` も `prev0`/`na`（旧 `PARAMS` の 16 通り）も要らない。
**正解の (i0,jR,jB,e) を与えると 378 サイト全部で復元できる**（旧版は 335/378）。

**(i0,jR,jB,e) の決め方**

候補を全部並べ、次の**像だけを見る**条件で篩う:

  * 復元 R が BMS 標準形（`isstd(R,'BMS')`）
  * `blk = [p] + (p の引数ブロック) + (単位の並び U)` と切れていて、
    その直後が q（深さ = p の深さ、段の対 = (行1(i0)+e, 行2(i0))）
  * 残余は q より深く、尾部は q 以下の深さ
  * conv3 の残余ガード（残余の先頭の深さ・段の対、残余が空なら e=1 かつ deep_end）
  * 残余の像の深さ = 像[i0] の深さ + 1 + e（残余が「写しの真下」のとき）

残ったものから **(i0 最小, jR 最小, jB 最大)** を選ぶ。
これで 378 サイト全部が一意に当たる（`python3 inv3.py` が数える）。

**測った結果（2026-08-27, `python3 inv3.py 7` = 278 秒）**

往復 `d2b3(b2d3(M)) == M`（BMS 3 行 z<2 標準形）:

| 列数 | 個数 | 一致 | 縮約が起きるもの | 落ちた分の正体 |
|---|---|---|---|---|
| <=4 |    144 |    144 |   0/0   | － |
| <=5 |   1018 |   1018 |   5/5   | － |
| <=6 |   8387 |   8380 |  44/44  | 7 件とも conv3 の単射性の破れ |
| <=7 |  77282 |  77116 | 338/338 | 166 件とも conv3 の単射性の破れ |
| シート 1354 対 | | 1352 | 333/333 | 2 件とも同じ |

**縮約サイトは 5/5・44/44・338/338・333/333 で全部戻る**（旧版は 0/44）。
`d2b3` が外すのは、下の「単射性の破れ」だけになった。
影の見分けは <=7 列 687776 柱・シート 13533 柱で誤り 0（前と同じ）。

逆向き `b2d3(d2b3(N)) == N`（DBMS 3 行 z<2 標準形。全射の目安）:

| 列数 | 個数 | d2b3(N) が BMS 標準形 | 前向きで戻る | 率 | 旧 |
|---|---|---|---|---|---|
| <=5 |   100 |   100 |   100 | 100.0% | 85 |
| <=6 |   528 |   528 |   524 |  99.2% | 376 |
| <=7 |  3514 |  3514 |  3432 |  97.7% | 2058 |
| <=8 | 27932 | 27930 | 26763 |  95.8% | － |

戻らないものは**逆写像の失敗ではなく conv3 の全射性の穴**らしい。代表 3 つ

    (0,0,0)(1,0,0)(2,1,0)(3,2,1)(3,y,0)(2,0,0)      y=0,1,2

は、BMS 3 行 z<2 標準形 <=8 列 **781605 個を全数**当たっても逆像が無い
（1 列ずつ伸ばしながら `b2d3` を当てる素朴な全数探索、8 列で 485 秒）。

**副産物: conv3 v10 は単射でない（2026-08-27, 新しい発見）**

    A = (0,0,0)(1,1,1)(2,1,0)(3,2,1)(3,0,0)(2,1,0)                     6 列
    B = A (1,1,0)(2,2,1)(3,2,0)(4,3,1)(4,0,0)(3,2,0)                  12 列
    どちらも BMS 標準形で b2d3(A) = b2d3(B)
      = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,2,0)(5,3,1)(5,0,0)(4,2,0)

B は A に「q ＋ A の本体まるごとの写し」を継いだもの。conv3 の
**残余なしの縮約**（`rest2` が空・`e=1`・`deep_end`）がそれをまるごと飲み込む。
`rows3.check` の単射検査は**同じ列数の集合の中でしか比べない**ので、
6 列 vs 12 列のこの衝突は見えない（NOTES の「全射性: 列数を揃えて比べては
いけない」と同じ罠が単射側にもあった）。
<=6 列で 7 件・<=7 列で 166 件・シートで 2 件。
`d2b3` はこの手のとき長い方（縮約を戻した方）を返すので、往復が落ちる。

**構造再帰になっているか（Lean に載せるための整理）**

* **読みそのものは構造再帰**である。`_walk`/`_read` は像の木を左から降りて
  祖先スタック（像深さ, 像レベル, BMS 深さ, BMS 行 1, 本体か）を持ち回るだけで、
  `rows2.readC` の `(first, plev)` を 3 行ぶんに太らせたものに等しい。
  縮約の枝も `readC` と**同じ形**（同じ区間をもう一度、深い文脈で読む）。
  `copy_shift`・`prev`・`na`・`after_w`・`closes_hi_unit` は 1 つも要らない。
* **切れ目 (i0,jR,jB,e) の決定だけが構造再帰でない**。下記。

**まだ無いもの: 切れ目を局所に決める規則**

2 行の `readC` は縮約の切れ目を `r2[0][1] < top[1]` という**局所の条件**で
決めていた。3 行では見つかっていない。いまの `find_sites` は
**復元 R が BMS 標準形であること**（大域の判定）に頼っている。
これを安い局所条件（行 y の値 = その行の入れ子の深さ、colOK、行 0 は 1 段ずつ）
に置き換えると <=5 列で 1018/1018 -> **113/1018** に落ちる（フィルタ無しと同じ）。
つまり大域の標準形判定が実際に効いている。Lean に載せるときの残る穴はここ 1 つ。

使い方:
    python3 inv3.py          往復・シート・全射の全数検査
    python3 inv3.py 7        <=7 列まで
"""
import sys, os, time, inspect
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse, show, isstd, cmpmat
import rows3
from rows3 import gen3, key, split0, is_branch

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


def d2b3p(N):
    """縮約を戻さない素の読み（影を落として深さを数え直すだけ）。"""
    N = tuple(N)
    rs, P0, Y, Dp = prep(N)
    return rebuild(N, rs, Y, Dp)


# ---------------------------------------------------------------- 二役の読み
def _walk(N, rs, lo, hi, ST, prom):
    """区間 [lo,hi) の各柱に (BMS 深さ, BMS 行 1) を与える。

    `ST` は外側の祖先スタック [(像深さ, 像レベル, BMS 深さ, BMS 行 1, 本体か)]。
    `prom` は「影だが**本体として数える**」添字の集合（縮約の q の影）。
    深さも行 1 も「祖先のうち本体の本数」なので、q の影を 1 本数えるだけで
    写し（1 段深く、行 1 が +e）が出てくる。
    """
    st = list(ST)
    bd, by, sts = {}, {}, {}
    for t in range(lo, hi):
        while st and st[-1][0] >= N[t][0]:
            st.pop()
        p = st[-1] if st else None
        bd[t] = 0 if p is None else p[2] + (1 if p[4] else 0)
        if N[t][1] == 0:
            by[t] = 0
        else:
            j = None
            for k in range(len(st) - 1, -1, -1):
                if st[k][1] < N[t][1]:
                    j = st[k]
                    break
            by[t] = (0 if j is None else j[3]) + \
                    (0 if (rs[t] == S1 and t not in prom) else 1)
        sts[t] = list(st)
        st.append((N[t][0], N[t][1], bd[t], by[t],
                   rs[t] == BODY or t in prom))
    return bd, by, sts


def _read(N, rs, lo, hi, ST, prom, sites):
    """像の区間 [lo,hi) を BMS 列に読む。`sites` = {i0: (jR,jB,e)}。

    縮約サイトでは、同じ区間 [i0,jB) を **q の影を数える文脈で**もう一度読む。
    2 行の `rows2.readC` の `inner = readC ([top]+arg_l+U+r2[:m])` と同じ形。
    """
    bd, by, sts = _walk(N, rs, lo, hi, ST, prom)
    out, t = [], lo
    while t < hi:
        s = sites.get(t)
        if s is not None:
            jR, jB, e = s
            qi = t if e == 0 else t + 1
            sub = {k: v for k, v in sites.items() if k != t}
            blk = _read(N, rs, t, jR, sts[t], prom, sub)
            q = (bd[t], by[t] + e, N[t][2])
            two = _read(N, rs, t, jB, sts[t], prom | {qi}, sub)
            out += blk + [q] + two
            t = jB
            continue
        if rs[t] == BODY:
            out.append((bd[t], by[t], N[t][2]))
        t += 1
    return out


# ---------------------------------------------------------------- サイトの条件
def _units_ok(p, U, q):
    """`units_split(p, U+[q]+…, qlab)` がちょうど U で切れるか。"""
    if q[0] != p[0]:
        return False
    qlab = (q[1], q[2])
    k = 0
    while k < len(U):
        if U[k][0] != p[0] or (U[k][1], U[k][2]) == qlab:
            return False
        t = k + 1
        while t < len(U) and p[0] < U[t][0]:
            t += 1
        k = t
    return k == len(U)


def _site_ok(N, rs, i0, jR, jB, e, blk, q, two, tail):
    """conv3 の縮約枝がこの切れ目で発火することを、復元 R だけを見て確かめる。"""
    if not blk:
        return False
    p = blk[0]
    cp, res = two[:len(blk)], two[len(blk):]
    if len(cp) != len(blk):
        return False
    A, U = split0(p, list(blk[1:]))
    if not _units_ok(p, U, q):
        return False
    if any(c[0] <= q[0] for c in res):
        return False
    if tail and tail[0][0] > q[0]:
        return False
    # 写しの整合: 二役の読みで出た cp が、前向きの `copy_shift` の出力でもあること。
    # 縮約が本当に発火するサイトでは必ず一致する（378 サイトで確認）。
    # 偽のサイトはここで落ちる（分岐列の浅い／深いが `copy_shift` の
    # 状態機械で作れない並びになる）。
    ps0 = q[1] - e
    if not any(list(rows3.copy_shift(blk, e, ps0, pv, na)) == list(cp)
               for pv in (1, 0) for na in (q, rows3.NOTLAST)):
        return False
    v, s2 = p[1], p[2]
    if res:
        if res[0][0] < p[0] + 1:
            return False
        if (res[0][0] == p[0] + 1 and (res[0][1], res[0][2]) >= (v + e, s2)
                and e == 0):
            return False
        # 残余の像は「写しの真下」なら深さ d+1+e に書かれる（conv3 の rd）
        if res[0][0] == p[0] + 1 and N[jR][0] != N[i0][0] + 1 + e:
            return False
    else:
        # 残余なしの縮約は「行 1 ずれ」かつ「残りが深く書かれた分岐列で終わる」
        if e == 0 or not (is_branch(blk[-1]) and cp[-1][1] > blk[-1][1]):
            return False
    return True


def _try(N, rs, sites, i0, jR, jB, e):
    """サイト (i0,jR,jB,e) を足したときの復元 R。条件を満たさなければ None。"""
    qi = i0 if e == 0 else i0 + 1
    if qi >= len(N) or (e == 1 and rs[qi] != S1):
        return None
    st = dict(sites)
    st[i0] = (jR, jB, e)
    bd, by, sts = _walk(N, rs, 0, len(N), [], frozenset())
    blk = _read(N, rs, i0, jR, sts[i0], frozenset(), sites)  # sites に i0 は無い
    if not blk:
        return None
    q = (bd[i0], by[i0] + e, N[i0][2])
    two = _read(N, rs, i0, jB, sts[i0], frozenset({qi}), sites)
    tail = (_read(N, rs, jB, len(N), sts[jB], frozenset(), sites)
            if jB < len(N) else [])
    if not _site_ok(N, rs, i0, jR, jB, e, blk, q, two, tail):
        return None
    R = tuple(_read(N, rs, 0, len(N), [], frozenset(), st))
    if not isstd(R, 'BMS'):
        return None
    return R, st


def find_sites(N, rs):
    """像だけを見て縮約サイトを決める。**(i0 最小, jR 最小, jB 最大)**。"""
    sites = {}
    for i0 in range(len(N)):
        if rs[i0] != S0:
            continue
        best = None
        for jR in range(i0 + 1, len(N) + 1):
            for jB in range(len(N), jR - 1, -1):
                for e in (1, 0):
                    r = _try(N, rs, sites, i0, jR, jB, e)
                    if r is not None:
                        best = (jR, jB, e)
                        break
                if best:
                    break
            if best:
                break
        if best:
            sites[i0] = best
    return sites


def d2b3(N):
    """DBMS 3 行標準形 -> BMS 3 行標準形（縮約も戻す）。"""
    N = tuple(N)
    rs = roles_of(N)
    if S0 not in rs:
        return rebuild(N, rs, *prep(N)[2:])
    sites = find_sites(N, rs)
    return tuple(_read(N, rs, 0, len(N), [], frozenset(), sites))


def d2b3x(N, verify=None):
    """互換用。いまの `d2b3` は縮約を戻すので、そのまま呼ぶだけ。"""
    return d2b3(N)


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
def check_gen(lim, verbose=3):
    A = gen3('BMS', lim, zcap=1)
    rok = ok = ncontr = cok = 0
    cols = colerr = 0
    coll = []
    bad = []
    for M in A:
        N, rs, nc = trace_roles(M)
        pr = roles_of(N)
        rok += (pr == rs)
        cols += len(rs)
        colerr += sum(1 for x, y in zip(rs, pr) if x != y)
        ncontr += (nc > 0)
        R = d2b3(N)
        good = (R == tuple(M))
        ok += good
        if nc > 0:
            cok += good
        if not good:
            # conv3 が単射でないだけか（別の BMS 標準形が同じ像を持つ）
            if isstd(R, 'BMS') and rows3.b2d3(R) == N:
                coll.append((M, R, N))
            elif len(bad) < verbose:
                bad.append((M, N, R))
    print('BMS 3 行 z<2 標準形 <=%d 列: %d 個（うち縮約が起きるもの %d）'
          % (lim, len(A), ncontr))
    print('  影の見分け: 行列 %d/%d 一致   柱 %d 本中 誤り %d'
          % (rok, len(A), cols, colerr))
    print('  d2b3(b2d3(M)) == M : %d/%d   （縮約が起きるもので %d/%d）'
          % (ok, len(A), cok, ncontr))
    print('  うち conv3 の単射性の破れ（別の標準形が同じ像）: %d' % len(coll))
    for M, R, N in coll[:verbose]:
        print('    %-34s と' % show(M))
        print('    %-34s が同じ像 %s' % (show(R), show(N)))
    for M, N, R in bad:
        print('    %-34s -> %-30s (戻り %s)' % (show(M), show(N), show(R)))
    return ok, len(A), len(coll)


def check_sheet(verbose=3):
    import sheet3
    T = sheet3.load(1)
    ok = cok = ncontr = nfwd = 0
    coll = []
    bad = []
    for row, b, d in T:
        N, rs, nc = trace_roles(b)
        if N != tuple(d):
            nfwd += 1
            continue                      # シートの誤記 4 件は勘定に入れない
        ncontr += (nc > 0)
        R = d2b3(d)
        good = (R == tuple(b))
        ok += good
        if nc > 0:
            cok += good
        if not good:
            if isstd(R, 'BMS') and rows3.b2d3(R) == tuple(d):
                coll.append((row, b, R))
            elif len(bad) < verbose:
                bad.append((row, b, d, R))
    n = len(T) - nfwd
    print('シート 3 行 z<=1: %d 対（b2d3 が外す %d は除外、縮約が起きる %d）'
          % (len(T), nfwd, ncontr))
    print('  d2b3(D) == B : %d/%d   （縮約が起きるもので %d/%d）'
          % (ok, n, cok, ncontr))
    print('  うち conv3 の単射性の破れ: %d' % len(coll))
    for row, b, d, R in bad:
        print('  行%-5d D %s' % (row, show(d)))
        print('        正 %s' % show(b))
        print('        誤 %s' % show(R))
    return ok, n


def check_dbms(lim, verbose=3):
    """逆向き: DBMS 標準形をぜんぶ読み戻して、前向きで戻るか（全射の検査）。"""
    D = gen3('DBMS', lim, zcap=1)
    std = back = 0
    bad = []
    for N in D:
        R = d2b3(N)
        s = isstd(R, 'BMS')
        std += s
        b = (rows3.b2d3(R) == tuple(N))
        back += b
        if not b and len(bad) < verbose:
            bad.append((N, R, s))
    print('DBMS 3 行 z<2 標準形 <=%d 列: %d 個' % (lim, len(D)))
    print('  d2b3(N) が BMS 標準形     : %d' % std)
    print('  b2d3(d2b3(N)) == N        : %d  (%.1f%%)'
          % (back, 100.0 * back / max(1, len(D))))
    for N, R, s in bad:
        print('    %-32s -> %-32s (標準形 %s, 像 %s)'
              % (show(N), show(R), s, show(rows3.b2d3(R))))
    return back, len(D)


def main(lim=6):
    t0 = time.time()
    for L in range(4, lim + 1):
        check_gen(L)
    check_sheet()
    for L in range(5, lim + 2):
        check_dbms(L)
    print('%.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 6)
