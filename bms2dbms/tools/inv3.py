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

**v12 `mark` への追いつき（2026-08-27, 課題 F3）**

`conv3` v12 の `mark` は「残余なしの縮約は、写しを飲んだ**印が像に残る**ときだけ
発火する」（`rows3.leaves_mark_local`）。印が残らないと `conv3(R)` は縮約せずに
像が伸びるので、**その像は短い側からしか来ない**。v11 用の `d2b3` はこの条項を
知らず、印の無い像に「双子」`R = 本体 ++ (1,1,0) ++ 写し` を返していた
（生成 <=6 列で 7 件、<=7 列で 164 件）。

直したのは `_try` の 1 行だけ:

    if len(two) == len(blk) and rows3.b2d3(R) != N:
        return None          # 残余なし（＝`mark` の枝）で、前向きが像を再現しない

`len(two) == len(blk)` は「残余が空」＝ `mark` が効く枝そのもの。`_site_ok` を
通り `isstd(R)` も通った候補にしか当たらないので、前向き呼び出しの回数は
生成 <=7 列の全数で数百回にとどまる（<=6 列の全数検査は 11.2s -> 13s）。
縮約は 1 つの行列に高々 1 回しか発火しない（生成 <=7 列 338 個・<=8 列 2414 個で
`nc` は全部 0 か 1）ので、部分的なサイト集合で前向きを当てても取りこぼさない。

**印は像から直に読める（測定, 誤り 0）**

    分岐列 (a,1,0) の像が **深い** <=> その像の**行 1 の親が行 1 の影**（S1）

  | 対象 | 浅い／深いの選択肢がある柱 | 誤り |
  |---|---|---|
  | 生成 <=6 列（縮約なしの行列） |  3272 | **0** |
  | 生成 <=7 列（同上）          | 40183 | **0** |

深い側は行 1 が「影の行 1 ＋ 1」で書かれるので、行 1 の親がその影になる。
浅い側は影より上の祖先が親になる。`mark` の局所条件（`prev != 0` かつ
`after_w` も `closes_hi_unit` も発火しない）を**像だけ**から書き直すときの土台で、
いまの前向き呼び出しを置き換える道はここにある（未実装）。

**測った結果（2026-08-27, 課題 F3 のあと）**

往復 `d2b3(b2d3(M)) == M`（BMS 3 行 z<2 標準形）:

| 列数 | 個数 | 一致 | 縮約が起きるもの | 影の見分け | 落ちた分の正体 |
|---|---|---|---|---|---|
| <=4 |    144 |    144 |   0/0   | 768 柱 誤り 0 | － |
| <=5 |   1018 |   1018 |   5/5   | 6726 柱 誤り 0 | － |
| <=6 |   8387 |   **8387** |  44/44  | 65327 柱 誤り 0 | － |
| <=7 |  77282 |  **77280** | 338/338 | 687776 柱 誤り 0 | 2 件とも conv3 の単射性の破れ |
| <=8 | 781605 | **781574** | 2414/2414 | － | 31 件とも同じ |
| シート 1354 対 | | **1353** | 333/333 | － | 1 件とも同じ |

前（v11 用）は <=6 列 8380 / <=7 列 77116 / シート 1352 で、落ちた分は
全部「双子を返した」ぶんだった。**いま残っているのは conv3 側の単射性の
破れだけ**（`check_gen` の内訳で「逆写像が古い」0 件・「本当の失敗」0 件。
<=8 列の全数 781605 個でも 0 件 / 0 件）。
縮約は <=8 列で 2414 個の行列に発火し、**2414/2414 全部戻る**。

逆向き `b2d3(d2b3(N)) == N`（DBMS 3 行 z<2 標準形。全射の目安）は変わらない:
<=5 列 100/100、<=6 列 524/528、<=7 列 3432/3514（どれも `d2b3(N)` は
BMS 標準形）。戻らないものは**逆写像の失敗ではなく conv3 の全射性の穴**。代表

    (0,0,0)(1,0,0)(2,1,0)(3,2,1)(3,y,0)(2,0,0)      y=0,1,2

は BMS 3 行 z<2 標準形 <=8 列 781605 個を全数当たっても逆像が無い。

**残る単射性の破れ（conv3 側。`inv3` の欠陥ではない）**

`mark` が残余なしの 164 組を直したあとに残るのは、**残余ありの縮約**（`rest2` が
空でない・`deep_end` が偽）の 2 組（生成 <=7 列）:

    短 (0,0,0)(1,1,1)(2,1,0)(3,2,1)(3,2,0)(3,1,0)(1,1,1)                7 列
    長 ...(3,1,0)(1,1,0)(2,2,1)(3,2,0)(4,3,1)(4,3,0)(4,1,0)(2,2,1)     13 列
    像 (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,2,0)(5,3,1)(5,3,0)(5,1,0)(3,2,1)

長い側の縮約は 残余 `rest2 = (2,2,1)` を深さ `rd = 3` に書き、その像は `(3,2,1)`。
短い側の末尾 `(1,1,1)` を素直に深さ 1 に書いた像も `(3,2,1)` で、**残余が写しの
シフトをちょうど打ち消して印が消える**。`copy_shift` の逆 `(a-1, b-e, c)` が
短い側の続きに一致し、`rd` がそのシフトを打ち消すのが collapse の形。

**31 組（生成 <=8 列の全数）の形は 1 種類だけ**（`d2b3` が見つけた組を数えた）:

| 残余 | rd | 残余の像 | 組数 |
|---|---|---|---|
| (2,2,1)                | 3 | (3,2,1)                | 22 |
| (2,2,1) ++ 1 列        | 3 | (3,2,1) ++ 1 列        |  9 |

先頭は**必ず `(2,2,1)`・`rd = 3`・像 `(3,2,1)`**。短い側の対応する列は
`(1,1,1)` で、深さ 1 に素直に綴った像も `(3,2,1)`。2 列目以降も
`(3,0,0)->(4,0,0)`・`(3,1,0)->(4,1,0)`・`(3,2,1)->(4,2,1)`・`(3,3,0)->(4,3,0)`
のように**シフトがそのまま打ち消される**。シートで落ちる 1 件（行 1532）も同じ形。
足りない規則は `mark` の残余版:

    縮約は「縮約しないで綴った像と違う」ときだけ発火してよい。
    残余版の局所形: conv_resid(rest2, rd, ...) が
                    conv3((a-1, b-e, c) に戻した rest2 を深さ d で綴った像)
                    と一致するなら発火しない。

（規則の実装は `rows3.py` 側の仕事。ここでは形だけ記録する。）

**像が DBMS 非標準になる 84 件（生成 <=8 列）の正しい像（測定, 課題 F3）**

`rule.R23` の像と突き合わせた:

  * `rule.R23` の像は **84/84 で DBMS 標準形**
  * その像を `d2b3` で読み戻すと **80/84 でもとの M に戻る**（構成的な裏づけ）
  * 最初に食い違う柱は 1 種類に集中する

    | conv3 | rule.R23 | 件数 |
    |---|---|---|
    | (5,1,0) | (6,2,0) | 54 |
    | (2,1,0) | (3,2,0) | 16 |
    | (6,1,0) | (7,2,0) | 12 |
    | (2,1,0) | (3,1,0) |  1 |
    | (2,1,0) | (3,0,0) |  1 |

つまり **conv3 は分岐列 (a,1,0) を「行 1 の影の横（深さ d・浅い段）」に置き、
`rule` は「本体の横（深さ d+1・深い段）」に置く**。conv3 の綴りは行 1 の影と
同じ柱をもう一度書くので `(5,1,0)(6,2,1)(5,1,0)(6,2,1)` のような重複ができ、
そこが非標準になる。代表:

    M     (0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)(4,0,0)
    conv3 ...(6,2,1)(5,1,0)(6,2,1)(6,0,0)     非標準
    R23   ...(6,2,1)(6,2,0)(7,3,1)(7,0,0)     標準形・d2b3 で M に戻る

`x_spell.py` の「(b) の本丸は sibbody ではなく段の表のリセット」と同じ結論
（`(2,0,0)` で L がリセットされて `base_s == base_d` になり、深い側が選べない）。
`sibbody2` は深さだけ動かして段は浅いまま `(6,1,0)(7,2,1)` にするので、
**R23 の綴りとは別物**である。

戻らない 4 件は `d2b3` 側の小さな穴（`(3,2,1)` の直後の同深さの兄弟を
1 段浅く読む）。いまの conv3 はその像を作らないので往復には出てこない。

**構造再帰になっているか（Lean に載せるための整理）**

* **読みそのものは構造再帰**である。`_walk`/`_read` は像の木を左から降りて
  祖先スタック（像深さ, 像レベル, BMS 深さ, BMS 行 1, 本体か）を持ち回るだけで、
  `rows2.readC` の `(first, plev)` を 3 行ぶんに太らせたものに等しい。
  縮約の枝も `readC` と**同じ形**（同じ区間をもう一度、深い文脈で読む）。
  `copy_shift`・`prev`・`na`・`after_w`・`closes_hi_unit` は 1 つも要らない。
* **切れ目 (i0,jR,jB,e) の決定だけが構造再帰でない**。下記。

**`mark` の判定は局所（像だけ）でできる（測定, 2026-08-27）**

`LOCALMARK = True`（既定）なら `_mark_local` が像だけを見て `mark` を決める。
`LOCALMARK = False` にすると前向き `rows3.b2d3(R) != N` を 1 回当てる道に落ちる。
**生成 <=7 列 77282 個の全数で 2 つの道の出力は完全一致**（食い違い 0、
往復もどちらも 77280）。局所版が使う事実は 2 つ:

  * 縮約の直後は必ずアンカー `q=(1,1,0)` なので `closes_hi_unit`
    （次が (1,1,1) を要求）は決して発火せず、`closes_unit(q)` は必ず真。
    よって「自然な綴り＝浅い」「強制の綴り＝深い <=> prev != 0」に縮まる。
  * 深い／浅いは像から直に読める（上の `_deep_img`）。

    印が残る <=> 像が末尾の分岐列を深く綴っている
                 かつ （直前が「x w」の柱 かつ prev == 1）でない

`prev` も像から読める（`_prev_at`。本体の柱を左から見て、行 0 が 0 で None に
戻し、選択肢のある分岐列でだけ 0/1 を書き換える）。**Lean に載る形はこれ**。

**まだ無いもの: 切れ目を局所に決める規則**

2 行の `readC` は縮約の切れ目を `r2[0][1] < top[1]` という**局所の条件**で
決めていた。3 行では見つかっていない。いまの `find_sites` は
**復元 R が BMS 標準形であること**（大域の判定）に頼っている。
これを安い局所条件（行 y の値 = その行の入れ子の深さ、colOK、行 0 は 1 段ずつ）
に置き換えると <=5 列で 1018/1018 -> **113/1018** に落ちる（フィルタ無しと同じ）。
つまり大域の標準形判定が実際に効いている。Lean に載せるときの残る穴はここ 1 つ。

使い方:
    python3 inv3.py          往復・シート・全射の全数検査（<=6 列、約 20 秒）
    python3 inv3.py 7        <=7 列まで（約 8 分）

**目安の速さ**（1 件あたりの `d2b3`）: 6 列 1.1ms / 7 列 2.7ms / 8 列 10.5ms。
生成 <=8 列 781605 個の全数は 1 コアで約 2 時間なので、列で 8 分割して並列に回した
（8 プロセスで 21 分）。走らせる前に 200〜300 件で 1 件あたりの秒を測ること。
"""
import sys, os, time, inspect
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse, show, isstd, cmpmat
import rows3
from rows3 import gen3, key, split0, is_branch

S0, S1, BODY = 'S0', 'S1', 'B'

# v12 `mark` の判定を像だけの局所条件でやるか（False なら前向きを 1 回当てる）
LOCALMARK = True


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


_PREP1 = [None, None]      # prep(N) の 1 個だけの覚え書き（サイト探索で何度も引く）


def prep1(N):
    if _PREP1[0] != N:
        _PREP1[0], _PREP1[1] = N, prep(N)
    return _PREP1[1]


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


def _deep_img(N, rs, P0, t):
    """像の柱 `t`（分岐列の本体）が**深く**綴られているか。

    深い <=> その像の**行 1 の親が行 1 の影**（S1）。深い側は行 1 が
    「影の行 1 ＋ 1」で書かれるので、行 1 の親がちょうどその影になる。
    浅い側は影より上の祖先が親になる。
    測定: 生成 <=6 列 3272 柱・<=7 列 40183 柱（縮約なしの行列）で誤り 0。
    """
    j = par1i(N, P0, t)
    return j >= 0 and rs[j] == S1


def _has_choice(N, rs, P0, Y, t):
    """柱 `t` に浅い／深いの選択肢があるか（`rows3` の base_s != base_d）。

    深い側は「行 1 の深さ Y[t]-1 の祖先に立てた行 1 の影」を親にする。
    その影が無ければ深い側と浅い側が同じ値になり、選択肢が無い（`'tie'`）。
    """
    w = Y[t] - 1
    j = P0[t]
    while j != -1:
        if rs[j] == S1 and Y[j] == w:
            return True
        j = P0[j]
    return False


def _prev_at(N, rs, P0, Y, Dp, jR):
    """像の柱 `jR-1` を決める直前の段 `st['prev']`（None / 0 / 1）。

    `conv3` は行列を左から右へ歩くので、`[0, jR-1)` の本体の柱を同じ順に
    なぞればよい。行 0 が 0 の柱で None に戻る（v12 `newterm`）。
    選択肢の無い分岐列（`'tie'`）は段を書き換えない。
    """
    prev = None
    for t in range(jR - 1):
        if rs[t] != BODY:
            continue
        c = (Dp[t], Y[t], N[t][2])
        if c[0] == 0:
            prev = None
        if rows3.is_branch(c) and _has_choice(N, rs, P0, Y, t):
            prev = 1 if _deep_img(N, rs, P0, t) else 0
    return prev


def _mark_local(N, rs, P0, Y, Dp, jR, pv):
    """v12 `mark` の局所版（`rows3.leaves_mark_local` を像から読み直したもの）。

    残余なしの縮約は「写しを飲んだ印が像に残る」ときだけ発火する。縮約の
    直後は必ずアンカー `q=(1,1,0)` なので `closes_unit(q)` は真、
    `closes_hi_unit`（次が (1,1,1) を要求）は決して発火しない。残るのは

        印が残る <=> 像が末尾の分岐列を**深く**綴っている
                     かつ （直前の段 prev == 1 かつ 直前が「x w」の柱）でない

    `pv` は復元 `R` の中で末尾の分岐列の 1 つ前に来る列。
    """
    t = jR - 1
    if not _deep_img(N, rs, P0, t):
        return False
    if rows3.is_w_col(pv) and _prev_at(N, rs, P0, Y, Dp, jR) == 1:
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
    if len(two) == len(blk):
        # v12 `mark`（`rows3.leaves_mark_local`）: 残余なしの縮約は「写しを飲んだ
        # 印が像に残る」ときだけ発火する。印が残らないと conv3(R) は縮約せず、
        # 像は伸びる（＝この N は「双子」R ではなく短い側から来ている）。
        # `len(two) == len(blk)` が「残余が空」＝ `mark` の枝そのもの。
        if LOCALMARK:
            head = _read(N, rs, 0, i0, [], frozenset(), sites) if i0 else []
            pv = blk[-2] if len(blk) >= 2 else (head[-1] if head else None)
            _rs, _P0, _Y, _Dp = prep1(N)
            if not _mark_local(N, _rs, _P0, _Y, _Dp, jR, pv):
                return None
        elif rows3.b2d3(R) != N:
            # 前向きを 1 回当てる道（`_site_ok` と `isstd(R)` を通った候補だけ）
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
_OMARK = (rows3.leaves_mark_local, rows3.leaves_mark)
_STACK, _TOP, _INRES = [], [], [0]
_SPEC = [0]        # v12 `mark` の**下見**の中か（下見の柱は像に出ない）


def _spec(f):
    """`leaves_mark(_local)` を包む。中で走る `conv3` は像に出ないので、
    役割の追跡から外す（外さないと親フレームの `kids` が水増しされ、
    `n = len(out) - kids` がずれて役割づけを取り違える）。"""
    def g(*a, **k):
        _SPEC[0] += 1
        try:
            return f(*a, **k)
        finally:
            _SPEC[0] -= 1
    return g


def _tr(*a, **k):
    """`rows3.conv3` の薄いラッパ。自分が書いた柱と役割を記録する。

    再帰は module global の `conv3` を通るので、差し替えれば全部拾える。
    `cols` は返り値の**接頭辞**で、残りは子の返り値をこの順に並べたもの。
    """
    bd = _SIG.bind(*a, **k)
    bd.apply_defaults()
    A = bd.arguments
    if A.get('st') is None:
        A['st'] = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(A['M']),
                   'nc': 0, 'rec': {}}
    if not A['M']:
        return []
    if _SPEC[0]:
        return _ORIG(**A)        # `mark` の下見。像には出ない
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
    rows3.leaves_mark_local = _spec(_OMARK[0])
    rows3.leaves_mark = _spec(_OMARK[1])
    try:
        out = tuple(rows3.conv3(list(M)))
    finally:
        rows3.conv3, rows3.conv_resid = _ORIG, _ORES
        rows3.leaves_mark_local, rows3.leaves_mark = _OMARK
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
