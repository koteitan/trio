"""3 行 z<2 の BMS -> DBMS 変換を、設計 -> 検査のループで詰めるための道具。

BMS 3 行の列は (x,y,z) で z<=y<=x、いまは z<2 に制限する。
DBMS 3 行の列は z<y<x（0 は例外）。「弱い降下」を「強い降下」にするのが変換。

**土台になる観測（2026-08-26）**

    BMS でも DBMS でも、標準形の第 y 行の値は**その行の入れ子の深さ**に等しい。
    3 行 <=6 列で BMS 8387 個・DBMS 555 個、違反 0。

だから行 1 の値は保存されるものではなく、行 1 の木に影を挟めばその分ずれる。
2 行の変換を「行 (0,1)」と「行 (1,2)」の**二重**に効かせるのが設計 v6 以降。

**検査**（`main` が回す = `check`）

  (1) 像が DBMS 標準形
  (2) 単射・順序保存。**単射はこの集合の中でしか見ていない**（`gen3(lim)` なので
      lim 列を超える相手との衝突は見えない）。それは (5) が拾う。
  (3) 性質 R: 任意の n に対し、ある m と n'>=n で 像<m> = 像(M<n'>)
      **3 行では偽と確定している**（NOTES §性質 R）。目標にしてはいけないので
      **既定では回さない**（`check(..., rprop=True)` で回る）。
  (4) z=0 の断片で 2 行版 `rows2.convC` と完全一致
  (5) 逆写像 `inv3.d2b3` で戻る。落ちた分は 2 つに分ける:
      **単射性の破れ**（戻り B が BMS 標準形で f(B) が同じ像 = 列数をまたぐ衝突）と
      **本当の失敗**（B が逆像ですらない = 逆写像の欠陥）。
  (6) 共終性 C1/C2

        C1: 任意の m<=mm に ある n<=nn で  f(M)<m> <= f(M<n>)
        C2: 任意の n<=nn に ある m<=mc で  f(M<n>) <= f(M)<m>

      **証明済みの 2 行版でちょうど 0 になる**（z=0 の 3 行標準形 <=6 列
      1285 個で C1 破れ 0・C2 破れ 0）。だから C1/C2 の違反は本物の欠陥。
  (7) ImgClosedT: 任意の m>=1 に ある BMS 標準形 B で (f M)<m> = f B
      **これが RD1（3 行版 ReindexD）の要**（NOTES §3 行の証明の骨組み）。
      z=0 では破れ 0（3852 対）。既定は `imgclosed_fast`（逆写像を 1 発当てる
      速い道）で、当たれば逆像の**構成的な証明**、外れは破れの**上界**。
      `imgfull=True` で `m_imgclosed` の梯子つき探索まで降りる（重い）。
      ImgClosedT は C1 より細かい: <=5 列で C1 の破れ 7 個は ImgClosedT の
      破れ 28 個に**含まれる**。

**到達点（2026-08-27, conv3 v11 = v10 ＋ アンカーで段をリセットしない）**

v11 の変更は 1 行（`p == ANCHOR` での `st['prev'] = 0` を消しただけ）。
**生成 <=7 列の 77282 個では像が 1 ビットも変わらない**ので、シート・非標準・
単射・順序・z=0・往復はすべて v10 と同じ数字である。変わるのは展開を通して
見える指標だけで、そこは**片側にしか動かない**（直すだけ・壊さない）。

| 検査 | v10 | v11（いま） |
|---|---|---|
| シート 3 行 z<=1 (1358 対) | 1354 一致 | **1354 一致**（不一致 4 はシート側の誤り） |
| シートの `d2b3` 往復（1358 対） | 1356 / 単射の破れ 2 | 1356 / 単射の破れ 2 |
| 生成 <=5 列 1018 個: 非標準 / 単射 / 順序 / z=0 | 0 / ok / 0 / 0 | 0 / ok / 0 / 0 |
| 生成 <=6 列 8387 個: 同 | 0 / ok / 0 / 0 | 0 / ok / 0 / 0 |
| 生成 <=7 列 77282 個: 同 | 3 / ok / 0 / 0 | 3 / ok / 0 / 0 |
| 生成 <=8 列 781605 個: 同 | 84 / ok / 0 / 0 | **84 / ok / 未測定 / 0** |
| `d2b3` 往復（<=5 / <=6 / <=7 列） | 1018 / 8380 / 77116 | 同じ（落ちた 7・166 は**全部**単射性の破れ） |
| 共終性 C1 の破れ（<=5 / <=6 / <=7 列） | 7 / 136 / 1897 | **7 / 121 / 1572** |
| 共終性 C2 の破れ（<=5 / <=6 / <=7 列） | 0 / 0 / 2 | 0 / 0 / 2 |
| ImgClosedT 破れ A（<=5 / <=6 / <=7 列） | 28 / 342 / — | **28 / 327 / 3779** |
| 展開閉包 28158 個: 非標準 / 潰れ / 順序違反 | 103 / 1 / 4 | 103 / 1 / 4 |
| 展開閉包の `d2b3` 往復（一致 / 単射の破れ / 本当の失敗） | 28031 / 125 / 2 | **28046 / 110 / 2** |

v9 -> v10 の 4 条項（resid / L / after_w / closes_hi_unit）を 1 つずつ足した
ときのシート成績は `python3 m_residue.py fix` で再現できる:
v9 1338 / +resid 1350 / +L 1340 / resid+L 1352 / +after_w 1353 /
+closes_hi_unit 1353 / 4 つ全部（v10）1354。どの段でも <=6 列は 0 / ok / 0。

<=8 列の内訳（`gen3` を貯めずに流して測った, 699 秒 / RSS 0.7GB）: v10 と像が
違うのは **8 列の 78 個だけ**（<=7 列は差 0）。非標準は 84（7 列 3 ＋ 8 列 81）で
v10 と同数、像のハッシュ衝突 0（＝ 781605 個の中では単射）。順序保存だけは
`key` 順に並べ直す必要があるので測っていない。
z=0 の断片は **<=9 列 295014 個で 2 行版 `rows2.convC` と食い違い 0**
（<=8 列 44653 個では v10 とも像の差 0）。z=0 は Lean で答えが確定している
断片なので、ここが 0 であることが変換器の一番強い足場である。

ImgClosedT の内訳（m<=3, 速い道）: <=5 列 2996/3051 対（外れ 55 対 = 28 個の A。
`m_imgclosed` の梯子つき全数探索でも同じ 55 対だったので**この範囲では確定**）、
<=6 列 24505/25158 対（外れ A 327）、<=7 列 224178/231843 対（外れ A 3779。
列数別に 4 列 2 / 5 列 26 / 6 列 299 / 7 列 3452）。
外れの集合は v10 ⊇ v11（342 ⊃ 327）で、直った 15 個は逆像 B を実際に持つ。

**v11 を採用した根拠（課題 D5, `y_fix.py` の候補4）**

型D の破れ = 「写しの中のアンカーで `prev` が 0 に戻り、もとでは深く綴られた
分岐列が写しでは浅く綴られる」。段の状態機械が写しをまたいで一貫していない。
リセットをやめると:

  * 生成 <=7 列 77282 個で像は不変（差 0）。展開閉包 28158 個で変わるのは 45 個だけ
  * 共終性 C1 の破れ 136 -> 121（<=6 列）、1897 -> 1572（<=7 列）。**破れ集合は真部分集合**
  * ImgClosedT の外れ 342 -> 327（<=6 列）。**これも真部分集合**
  * 像が変わった 45 個の `d2b3` 往復は 30/45 -> **45/45**（v10 の衝突 15 個が消える）。
    閉包 28158 個ぜんぶで見ても 28031 -> 28046 一致・衝突 125 -> 110・
    本当の失敗は 2 -> 2（v11 で新しく落ちたものは無い）
  * 悪化した指標は 1 つも無い

**残る欠陥（2026-08-27, v11 で残っている全部）**

  (a) ImgClosedT の破れ（<=5 列で 28 個の A・55 対が**確定**。<=7 列で 3779 個）。
      破れ方は 1 種類だけ: 目標 (f A)<m> の**末尾 1 列の行 1** が、届く像より
      1 だけ大きい。性質 R の反例・C1 の型D と同じ病気。
      足りないもの: 行 1 の入れ子を 1 段深く綴る規則。P6 では
      `rule.convert` の綴り ...(6,2,1)(6,2,0)(7,3,1) が正解だと決まっている
      （NOTES §D2）が、`rule.convert` は z=0 で 2 行版と 35 件食い違うので採れない。
  (b) 共終性 C1 の破れ（<=6 列 121、<=7 列 1572）。型D 74 と型I 47 に割れる
      （v10 の 136 での分類。v11 は型D を 15 直した残り）。
      足りないもの: 型I は f(M<n>) が浅い柱を先に挟む（行 0 が像側で +1）ので、
      行 0 の影の置き方の規則。型D は (a) と同根。
  (c) 単射性の破れ（<=6 列 7 組、<=7 列 166 組、シート 2 組、閉包 110 組）。
      A と「A ＋ q ＋ A の本体まるごとの写し」が同じ像になる。
      足りないもの: 残余なしの縮約（rest2 が空・e=1・deep_end）のガード。
  (d) 像が DBMS 非標準（<=7 列 3 件、<=8 列 84 件（v10 で測定）、閉包 103 件）。
      足りないもの: 兄弟を「行 1 の影の横」ではなく「本体の横」に付ける規則。
      ただし素朴な sibbody2 は共終性を新しく壊す（下の表）。
  (e) 全射の穴: (0,0,0)(1,0,0)(2,1,0)(3,2,1)(3,y,0)(2,0,0) (y=0,1,2) は
      BMS <=8 列 781605 個を全数当たっても逆像が無い（NOTES §逆写像）。
  (f) 逆写像 `d2b3` の本当の失敗が閉包で 2 件（どちらも
      (0,0,0)(1,1,1)(2,1,0)(3,0,0)(2,1,0) の反復系列で、戻りが 5 列短い）。
      足りないもの: 縮約の切れ目を像だけから決める**局所**条件
      （いまは大域の `core.isstd` に頼っており、Lean に載らない）。

  シート 4 件（592, 891, 897, 898）はシート側の誤りなので欠陥ではない
  （NOTES §シート行 891/897/898）。

**採らなかった規則: sibbody2 / sibbody3（x_spell.py, 2026-08-27）**

「行 1 の影を立てた柱の兄弟を、影の横（深さ d）ではなく本体の横（深さ dd）に
付ける」規則。上の系列を狙い撃ちにするので生成の非標準は減るが、**共終性を
新しく壊す**ので入れなかった。同じ土俵で測った表:

| 検査 | v10（当時の採用版） | +sibbody2 |
|---|---|---|
| シート | 1354/1358 | 1354/1358 |
| 生成 <=6 列 非標準 / 単射 / 順序 | 0 / ok / 0 | 0 / ok / 0 |
| 生成 <=7 列 非標準 | 3 | **1** |
| 生成 <=8 列 非標準 | 84 | **42** |
| 展開閉包 {M<n>: M in gen<=6, n<=4} 22805 個の非標準 | 103 | **115**（+12） |
| 共終性 C1 の破れ（<=5 / <=6 列） | 7 / 136 | **8 / 149** |
| 共終性 C2 の破れ（<=5 / <=6 列） | 0 / 0 | 0 / **4** |
| 性質 R の破れ（<=5 / <=6 列） | 58 / 646 | **59 / 663** |

破れはどれも**片側**（sibbody2 だけが壊し、直すものは 0）。
再現: `python3 x_spell.py cof 6`。
`not A`（子を持たない柱に限る）と `B[0][1] >= 1`（兄弟が行 1 を使う）を
足すと展開閉包の +12 と C2 の +4 は消える（103 / 0）が、共終性 C1 は
8 / 147 のままで +1 / +11 が残る。
壊れる代表例:

    M = (0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)
    v10       ...(6,2,1)(5,1,0)     C1 成立
    sibbody2  ...(6,2,1)(6,1,0)     像<2> が f(M<n>) をどの n でも追い越す

`rule.convert` はこの系列に第 3 の像 ...(6,2,1)(6,2,0)(7,3,1) を出す。
**この綴りが P6 の正解であることは決着した**（課題 D2）: M<2> = P6 のとき
DBMS 側の基本列 f(M)<2> がちょうどこの綴りになる。しかし `rule.convert`
そのものは変換器としては採れない —— 展開閉包の z=0 の部分 3961 個で
**証明済みの 2 行版 `rows2.convC` と 35 件食い違う**（直和が 1 個ぶんに潰れる）。
だから足すべきは「行 1 の入れ子を 1 段深く綴る」規則だけで、`rule.depths` の
機構ごと持ってくることではない。ここが次の一手（残る欠陥 (a)）。

使い方:
    python3 rows3.py [列数上限] [ImgClosedT の m の上限] [full]

      python3 rows3.py 5          <=5 列（15 秒）
      python3 rows3.py 6          <=6 列（4 分）
      python3 rows3.py 6 0        ImgClosedT を回さない（速い）
      python3 rows3.py 5 3 full   ImgClosedT を梯子つき探索まで降ろす（重い）
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
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


def par0(m, x):
    """柱 `x` の行 0 の親（左にある、行 0 の値がより小さい直近の柱）の添字。
    無ければ -1。core.pim の第 0 列と同じものを 1 箇所ぶんだけ持つ。"""
    for q in range(x - 1, -1, -1):
        if m[q][0] < m[x][0]:
            return q
    return -1


def hi_block(m, x):
    """`x` の属するブロック（直前のアンカーより後ろ）に行 2 を使う柱があるか。

    W_(w^2) 系の regime にいるかどうかの目印（`rule.py` の hi_block と同じ）。
    段の上げ下げの規則はこの regime の内と外で違うので、分岐列の浅い／深いを
    決めるときにこれを見る。
    """
    b = max([q for q in range(x) if m[q][0] == m[q][1] and m[q][0] >= 1],
            default=0)
    return any(m[z][2] > 0 for z in range(b + 1, x))


def is_repeat(m, x):
    """m[..x] の末尾が、その直前の同じ長さの区間の逐語コピーか。

    コピーされた区間はもとの区間と同じ深さで書かれるので、段を上げ直さない。
    """
    for L in range(1, (x + 1) // 2 + 1):
        if m[x - 2 * L + 1:x - L + 1] == m[x - L + 1:x + 1]:
            return True
    return False


def is_w_col(c):
    """「x w」の柱 (k,0,0), k>=1。段を上げずに項を伸ばすだけの柱。"""
    return c is not None and c[1] == 0 and c[0] >= 1


def closes_hi_unit(c, nxt, pv, pv2, hi, rep):
    """W_(w^2) 系で (a,2,1)(a,2,0) と積んだ直後の (a,1,0) は、
    次がアンカー (1,1,1) なら段を上げずにユニットを閉じる（＝浅い）。

    ただしその区間が直前の逐語コピーなら、もとの深さを引き継ぐ（rep）。
    `rule.py` の closes_hi_unit と同じ。
    """
    return (hi and not rep and nxt is not None and tuple(nxt) == (1, 1, 1)
            and pv is not None and tuple(pv) == (c[0], 2, 0)
            and pv2 is not None and tuple(pv2) == (c[0], 2, 1))


def Lat(L, k):
    """段の表 `L` の第 k 要素。表の外は 1 段ずつ伸ばして読む。"""
    if k < len(L):
        return L[k]
    if not L:
        return (0, 0, False, 0)
    a = L[-1]
    j = k - (len(L) - 1)
    return (a[0] + j, a[1], False, a[3] + j)


def padL(L, v):
    """段の表 `L` を長さ `v` まで `Lat` で埋めてから切る。

    もとは `L[:v]` だった。`len(L) < v` のときは黙って詰まってしまい、
    「第 v 段として継ぎ足したつもりのもの」が第 len(L) 段に化ける（表に穴があく）。
    表の外は 1 段ずつ伸ばして読む約束（`Lat`）なので、埋めてから継ぐのが正しい。
    """
    if len(L) < v:
        return tuple(Lat(L, k) for k in range(v))
    return L[:v]


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
          st=None, nx=None, off=0):
    """設計 v10: 二重の梯子 ＋ 分岐列 (a,1,0) の 1 ビット状態機械。

    `L[k]` もとの行 1 の深さ `k` の祖先について
           (深い側の行 1, その行 2, 子に渡す force1, 浅い側の行 1)
           行 1 の影を立てると「深い側」だけが影の値に置き換わる。
    `F[k]` 行 1 の深さ `k` の次の柱がその行 1 ブロックの先頭か
    `st`   線形に持ち回る状態 {'ST': 祖先の鎖, 'prev': 直前の分岐列の選択,
           'dmap': もとの深さ -> 像の深さ, 'Mo': もとの行列まるごと}
    `nx`   このブロックの**後ろ**に来る列（ブロック分割で見失うので持ち回る）
    `off`  この `M` がもとの行列 `st['Mo']` の何列目から始まるか。
           `M` はつねに `Mo` の連続部分なので、これで前後の列が引ける。

    分岐列 (a,1,0) (a>=2) だけが浅い／深いを選ぶ（NOTES §6 の観測）。
        浅い <=> prev == 0 / 行列の末尾 / 次がアンカー (1,1,0)
                 / after_w（直前が「x w」でユニットの端）
                 / closes_hi_unit（(a,2,1)(a,2,0)(a,1,0) の次が (1,1,1)）
    アンカー (1,1,0) を通過するたびに prev := 0。

    **v9 -> v10 で足した 4 条項**（どれも `m_residue.py` で 1 つずつ測った）

      resid    縮約の残余は「開始深さ 1 つの木」ではなく**もとの深さを保った森**。
               残余の先頭より浅い柱で切って再帰する（`conv_resid`）。
      L        `L[:v]` は `len(L) < v` のとき黙って詰まる。`padL` で長さ v
               まで `Lat` で埋めてから継ぐ。
      after_w  直前が「x w」の柱 (k,0,0) でユニットの端なら段は落ちる。
               W_(w^2) 系で直前が根に付いていないときだけ段が残る。
      closes_hi_unit
               (a,2,1)(a,2,0)(a,1,0) の直後が (1,1,1) なら段を上げずに閉じる。

    after_w と closes_hi_unit は**直前 2 本の柱**を見る規則なので、ブロックに
    切ってしまうと見えなくなる。`st['Mo']` ともとの添字 `off` を持ち回って引く。

    1 本の BMS 列は最大 3 本の柱になる:
        (d,   pw0,  pw1)       行 0 の影
        (dd,  base, pl2)       行 1 の影
        (dd', e1,   e2)        本体
    """
    if st is None:
        st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0}
    if not M:
        return []
    p, r = M[0], M[1:]
    v, s2 = p[1], p[2]
    A, B = split0(p, r)
    oA, oB = off + 1, off + 1 + len(A)      # 引数ブロック / 兄弟の先頭の添字

    if v == 0:
        base_d = base_s = 0
        pl2, force1 = 0, False
    else:
        e = Lat(L, v - 1)
        base_d, pl2, force1, base_s = e[0] + 1, e[1], e[2], e[3] + 1
    first1 = F[v] if v < len(F) else True

    # v11: アンカー (1,1,0) での段のリセット `st['prev'] = 0` は**やめた**。
    # 写しの中のアンカーで prev が 0 に戻ると、もとで「深い」と綴られた分岐列が
    # 写しでは「浅い」と綴られ、f(M<n>) が像の展開に追いつかない（C1 の型D）。
    # 課題 D5 の測定（2026-08-27）:
    #   gen<=7 の 77282 個で像は 1 ビットも変わらない（7 列の 68895 個で差 0）
    #   展開閉包 28158 個で像が変わるのは 45 個だけ。非標準 / 潰れ / 順序違反は
    #     103 / 1 / 4 で v10 と同数
    #   共終性 C1 の破れ（<=6 列）136 -> 121。破れ集合は 121 ⊂ 136（片側だけ）
    #   ImgClosedT の速い道の外れ（<=6 列）342 -> 327 個、集合は 327 ⊂ 342
    #   直った 15 個は逆像 B を実際に持っている（構成的）
    if is_branch(p) and base_s != base_d:
        nxt = M[1] if len(M) > 1 else nx
        shallow = (st['prev'] == 0) or closes_unit(nxt)
        # ここから先はもとの行列 Mo を直接見る。ブロックに切ってしまうと
        # 「直前の柱」が見えなくなるが、段の規則は直前 2 本を見て決まる。
        Mo = st['Mo']
        pv = Mo[off - 1] if off >= 1 else None
        pv2 = Mo[off - 2] if off >= 2 else None
        onx = Mo[off + 1] if off + 1 < len(Mo) else None
        hi = hi_block(Mo, off)
        # after_w（rule.py）: 直前が「x w」の柱 (k,0,0) で、しかもユニットの
        # 端にいるなら、段はふつう 1 に落ちる（浅い）。W_(w^2) 系（hi）で
        # 直前の柱が根に付いていないときだけ、段が残る（深い）。
        if st['prev'] == 1 and is_w_col(pv) and closes_unit(onx):
            pnt = off > 0 and par0(Mo, off - 1) == 0
            shallow = not (hi and not pnt)
        # closes_hi_unit（rule.py）: (a,2,1)(a,2,0)(a,1,0) と積んだ直後が
        # アンカー (1,1,1) なら、段を上げずにユニットを閉じる（浅い）。
        if closes_hi_unit(p, onx, pv, pv2, hi, is_repeat(Mo, off)):
            shallow = True
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
        Lb = padL(L, v - 1) + ((base, pl2, False, Lat(L, v - 1)[3]),)
    else:
        Lb = L
    LA = padL(Lb, v) + ((e1, s2, fc, e1),)
    FA = F[:v] + (False,)

    if lad0:
        for e in (0, 1):
            qlab = (ps[0] + e, ps[1])
            U, B2 = units_split(p, B, qlab)
            if not B2:
                continue
            oU, oq = oB, oB + len(U)
            q, r2 = B2[0], B2[1:]
            if (q[1], q[2]) != qlab or q[0] != p[0]:
                continue
            Aq, Bq = split0(q, r2)
            oAq, oBq = oq + 1, oq + 1 + len(Aq)
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
            oR = oAq + len(pre)
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
            Lr = padL(L, v) + (((base, pl2, fc, base) if e else (e1, s2, fc, e1)),)
            hd = lambda *ls: next((l[0] for l in ls if l), nx)
            # 写しは書かれないので、A から見た「次の列」は写しの後ろ
            # 写しは書かれないので、A から見た「次の列」は写しの後ろ。
            # 何も無くても「レベルが後で綴られている」ので末尾扱いにはしない。
            cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
                       U[0] if U else na, oA)
            cU = conv3(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na,
                       oU)
            # 写しの真下（もとの深さ p[0]+1）なら影の位置、さらに深ければ
            # 「もとの深さ -> 像の深さ」の表で決める。
            rd = (d + 1 + e if (not rest2 or rest2[0][0] == p[0] + 1)
                  else dmap_at(st, rest2[0][0] - 1))
            # 残余は 1 本の木ではなく**森**。深さをそろえずに読む（conv_resid）。
            cR = conv_resid(rest2, rd, Lr, (v, s2), (e1, e2), st, hd(Bq), oR)
            cB = conv3(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                       oBq)
            st['nc'] = st.get('nc', 0) + 1      # 縮約が発火した回数
            return cols + cA + cU + cR + cB

    # ここで「行 1 の影を立てた柱の兄弟を、影の横（深さ d）ではなく本体の横
    # （深さ dd）に付ける」規則（x_spell.py の sibbody2/3）を試したが、
    # **採らなかった**。gen<=7 の非標準を 3->1、gen<=8 を 84->42 に減らす代わりに、
    # 共終性 C1 を 1 件（<=5 列）・11 件（<=6 列）新しく壊す。詳しくは
    # モジュール docstring の「採らなかった規則」。
    cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
               B[0] if B else nx, oA)
    cB = conv3(B, d, L, FA, (v, s2), (e1, e2), False, False, st, nx, oB)
    return cols + cA + cB


def conv_resid(rest, rd, Lr, ps, pw, st, nx, off):
    """縮約の残余を「もとの深さを保った森」として読む。

    残余（写しに吸われずに残った列）は 1 本の木とは限らず**森**でありうる。
    まるごと深さ `rd` の 1 本の木として読むと、残余の先頭より行 0 が小さい
    ＝もっと浅い柱まで `rd` にそろえてしまい、木の形が変わる。
    先頭より浅い柱のところで切り、もとの深さの差だけ浅くして読み直す。
    """
    out = []
    while rest:
        m0 = rest[0][0]
        i = 1
        while i < len(rest) and rest[i][0] >= m0:
            i += 1
        head, tail = rest[:i], rest[i:]
        nx2 = tail[0] if tail else nx
        out += conv3(head, rd, Lr, (False,) * 12, ps, pw, False, False,
                     st, nx2, off)
        if not tail:
            break
        rd = max(0, rd - (m0 - tail[0][0]))   # もとの深さの差だけ浅くする
        off += i
        rest = tail
    return out


def b2d3n(M):
    """(像, 縮約が発火した回数) の対。回数は逆写像 `inv3.d2b3` の
    既知の穴（縮約は像から列が落ちるので読み戻せない）を数えるのに使う。"""
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0}
    return tuple(conv3(list(M), st=st)), st['nc']


def b2d3(M):
    return b2d3n(M)[0]


# ---------------------------------------------------------------- 検査
def pad(M2):
    return tuple((a, b, 0) for a, b in M2)


def two(M3):
    return [(c[0], c[1]) for c in M3]


def imgclosed_fast(f, A, mmax=3, d2b3=None):
    """ImgClosedT の**速い道**（逆写像 `inv3.d2b3` を 1 発当てるだけ）。

        ImgClosedT: 任意の BMS 標準形 A (|A|>1) と m>=1 に対し、ある BMS
                    標準形 B があって  (f A)<m> = f B

    T = (f A)<m> に `d2b3` を当て、出た B が BMS 3 行 z<2 標準形で
    f(B) == T なら**逆像の存在の証明**（B そのものを持っている）。
    外れは「この道では見つからなかった」だけなので破れの**上界**である。
    ただし <=5 列 x m<=3 の 3051 対では、外れ 55 対が `m_imgclosed` の
    梯子つき全数探索の破れ 55 対（相異なる A が 28 個）と**ちょうど一致**した
    （2026-08-27 実測）。本物の破れかどうかは `m_imgclosed.py` で確かめる。

    返り値 (当たり, 対の総数, 外れた A の集合)。"""
    if d2b3 is None:
        try:
            from inv3 import d2b3
        except Exception:
            return 0, 0, set()
    ok, tot, bad = 0, 0, set()
    for i, M in enumerate(A):
        if len(M) < 2:
            continue
        if i % 500 == 0:
            # `d2b3` は `isstd` を大量に呼ぶ。<=7 列（77282 個）でここを
            # 2000 ごとにすると RSS が 2.5GB を超えた（2026-08-27 実測）。
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        N = f(M)
        for m in range(1, mmax + 1):
            T = tuple(expand(N, m))
            tot += 1
            try:
                B = d2b3(T)
            except Exception:
                B = None
            if (B and isstd(B, 'BMS') and all(c[2] <= 1 for c in B)
                    and tuple(f(list(B))) == T):
                ok += 1
            else:
                bad.add(tuple(M))
    return ok, tot, bad


def check(f, A, nr=6, mm=10, nn=24, verbose=3, inv=True, mc=40,
          rprop=False, imgc=3, imgfull=False):
    """(1) 像が DBMS 標準形 (2) 単射・順序保存 (4) z=0 で 2 行版と一致
    (5) 逆写像 `inv3.d2b3` で戻る (6) 共終性 C1/C2 (7) ImgClosedT。

    (3) 性質 R（添字まで一致）は **3 行では偽と確定している**（NOTES §性質 R）。
    目標にしてはいけないので `rprop=True` のときだけ回す（既定は回さない）。
    代わりに要るのは (6) と (7):

        C1: 任意の m<=mm に ある n<=nn で  f(M)<m> <= f(M<n>)
        C2: 任意の n<=nn に ある m<=mc で  f(M<n>) <= f(M)<m>
        ImgClosedT: 任意の m>=1 に ある BMS 標準形 B で  (f M)<m> = f B

    C1/C2 は**証明済みの 2 行版でちょうど 0** になる（z=0 の 3 行標準形
    <=6 列 1285 個で破れ 0）。ImgClosedT も z=0 では破れ 0（3852 対）。
    だからどちらの違反も変換器の本物の欠陥である。ImgClosedT は C1 より
    細かい: <=5 列で C1 の破れ 7 個は ImgClosedT の破れ 28 個に**含まれる**。

    (2) の単射は `A` の中でしか比べていない。`A` は `gen3(lim)` なので
    **lim 列を超える相手との衝突は見えない**（実例: 6 列と 12 列が同じ像。
    NOTES §逆写像）。それは (5) が拾う: 往復が落ちて、しかも戻り B が
    BMS 標準形で f(B) が同じ像なら、それは**単射性の破れの証拠**である。

    `imgc` は ImgClosedT の m の上限（0 で回さない）。`imgfull=True` なら
    `m_imgclosed` の梯子つき探索（速い道が外れたものだけ・**重い**）。
    """
    W = [f(M) for M in A]
    ns = [(M, N) for M, N in zip(A, W) if not isstd(N, 'DBMS')]
    inj = len(set(W)) == len(W)
    ordbad = [i for i in range(len(A) - 1) if cmpmat(W[i], W[i + 1]) >= 0]
    z0bad = [(M, N) for M, N in zip(A, W)
             if all(c[2] == 0 for c in M) and N != pad(convC2(two(M)))]
    rbad, c1bad, c2bad = [], [], []
    for i, M in enumerate(A):
        if len(M) < 2:
            continue
        if i % 2000 == 0:
            # 展開のメモは M ごとに独立なので、ときどき捨てないと
            # <=7 列（77282 個）で RSS が 10GB を超える。
            core._exp_memo.clear()
            core._isstd_memo.clear()
            core._flat_memo.clear()
        N = f(M)
        E = [tuple(expand(N, m)) for m in range(1, mc + 1)]
        G = [tuple(f(expand(M, np))) for np in range(1, nn + nr + 1)]
        if rprop:
            img = set(E[:mm])
            for n in range(1, nr + 1):
                if not any(g in img for g in G[n - 1:n + nn]):
                    rbad.append((M, n, N))
                    break
        # (6) 共終性。
        if any(not any(cmpmat(E[m], g) <= 0 for g in G[:nn]) for m in range(mm)):
            c1bad.append((M, N))
        if any(not any(cmpmat(g, e) <= 0 for e in E) for g in G[:nn]):
            c2bad.append((M, N))
    # (5) 逆写像。`inv3` は `rows3` を import するので、ここで遅延 import する。
    rtbad, rtinj, d2b3 = [], [], None
    if inv:
        try:
            from inv3 import d2b3
        except Exception:
            d2b3 = None
    if d2b3 is not None:
        for M, N in zip(A, W):
            B = d2b3(N)
            if B == tuple(M):
                continue
            if (B and isstd(B, 'BMS') and all(c[2] <= 1 for c in B)
                    and tuple(f(list(B))) == tuple(N)):
                rtinj.append((M, B, N))   # 別の BMS 標準形が同じ像 = 単射の破れ
            else:
                rtbad.append((M, N))
    # (7) ImgClosedT
    icok = ictot = 0
    icbad, iccap = set(), []
    if imgc:
        icok, ictot, icbad = imgclosed_fast(f, A, imgc, d2b3)
        if imgfull and icbad:
            # 速い道が外れたものだけ梯子つき探索に降ろす。梯子は **安いほう**
            # （`LADDER_SCAN`）。既定の `LADDER` は 1 件あたり 54 万節点まで
            # 歩くので、<=4 列でも 5 分・RSS 5GB を超えた（2026-08-27 実測）。
            # 「なし」と出ても打ち切りが付いていれば探索不足の疑いが残る。
            from m_imgclosed import find, LADDER_SCAN
            still, iccap = set(), []
            for M in sorted(icbad, key=key):
                for m in range(1, imgc + 1):
                    T = tuple(expand(f(M), m))
                    _, B, _, _, cap = find(M, m, f=f, ladder=LADDER_SCAN, T=T)
                    core._isstd_memo.clear(); core._flat_memo.clear()
                    if B is None:
                        still.add(tuple(M))
                        if cap:
                            iccap.append((tuple(M), m))
            icbad = still
    print('  対象 %d 個' % len(A))
    print('  (1) 像が DBMS 非標準 : %d' % len(ns))
    for M, N in ns[:verbose]:
        print('        %-34s -> %s' % (show(M), show(N)))
    print('  (2) 単射（この集合の中で） : %s   順序保存の違反 : %d'
          % (inj, len(ordbad)))
    for i in ordbad[:verbose]:
        print('        %-34s -> %s' % (show(A[i]), show(W[i])))
        print('        %-34s -> %s' % (show(A[i + 1]), show(W[i + 1])))
    if rprop:
        print('  (3) 性質 R の違反 : %d   （3 行では偽。目安どまり）' % len(rbad))
        for M, n, N in rbad[:verbose]:
            print('        %-30s -> %s  (n=%d で覆えない)' % (show(M), show(N), n))
    else:
        print('  (3) 性質 R : 回さない（3 行では偽。rprop=True で回る）')
    print('  (4) z=0 で 2 行版と食い違い : %d' % len(z0bad))
    for M, N in z0bad[:verbose]:
        print('        %-34s -> %-30s (2 行版 %s)'
              % (show(M), show(N), show(pad(convC2(two(M))))))
    print('  (5) d2b3(b2d3(M)) != M : %d   （うち単射性の破れ %d = 別の '
          'BMS 標準形が同じ像）' % (len(rtbad) + len(rtinj), len(rtinj)))
    for M, N in rtbad[:verbose]:
        print('        %-34s -> %-30s (戻り %s)' % (show(M), show(N), show(d2b3(N))))
    for M, B, N in rtinj[:verbose]:
        print('        %-34s と %s が同じ像 %s' % (show(M), show(B), show(N)))
    print('  (6) 共終性 C1 の破れ : %d   C2 の破れ : %d' % (len(c1bad), len(c2bad)))
    for M, N in (c1bad + c2bad)[:verbose]:
        print('        %-34s -> %s' % (show(M), show(N)))
    if imgc:
        print('  (7) ImgClosedT（m<=%d, %s）: 逆像あり %d / %d   '
              '破れた A %d 個%s'
              % (imgc, '梯子つき全数' if imgfull else '速い道のみ',
                 icok, ictot, len(icbad),
                 '   うち打ち切り %d' % len(iccap) if imgfull else ''))
        for M in sorted(icbad, key=key)[:verbose]:
            print('        %-34s -> %s' % (show(M), show(f(M))))
    return (len(ns) + len(ordbad) + len(rbad) + len(z0bad) + len(rtbad)
            + len(rtinj) + len(c1bad) + len(c2bad) + len(icbad))


def main(lim=5, imgc=3, imgfull=False, rprop=False):
    t0 = time.time()
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    print('BMS 3 行 z<2 標準形 (<=%d 列): %d  (%.1fs)' % (lim, len(A), time.time() - t0))
    n = check(b2d3, A, imgc=imgc, imgfull=imgfull, rprop=rprop)
    print('合計違反 %d  (%.1fs)' % (n, time.time() - t0))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 5,
         imgc=int(sys.argv[2]) if len(sys.argv) > 2 else 3,
         imgfull=len(sys.argv) > 3 and sys.argv[3] == 'full')
