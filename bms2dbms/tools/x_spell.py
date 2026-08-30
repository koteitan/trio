"""課題 C3:「綴り直し」の山（`rows3.conv3` の残り 4 件）を測った記録と実験台。

`rows3.py` / `m_residue.py` は読むだけ。`m_residue.conv3G` のコピー `conv3X` を
ここに置いて実験する。既定の修正セットは `BASE = (resid, L, afterw, hiclose)`。

## 結論 1: (a) の 3 行（シート 891 / 897 / 898）は**シートの誤り**

「正解の像が入力より長くなる」山は、規則で埋める山ではなかった。
シートのその 3 行の DBMS 欄は、**別の（もっと小さい）BMS 行列の像**である。

    M    = (0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)(4,1,0)(5,2,0)          （シート行 897）
    双子 = (0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)(4,1,0)(1,1,1)(2,1,0)(3,2,0)
    双子 < M、両方とも BM4 標準形（yaBMS `bms -s -v 4` で 1）。
    シートの 897 の DBMS = conv3X(双子) = (0)(1)(2,1)(3,2,1)(4,2)(5,3)(6,3)(6,2)(3,2,1)(4,2)(5,3)

双子は「短い綴り (5,2,0)」を「長い綴り (1,1,1)(2,1,0)(3,2,0)」に開いたもの。
891 / 898 も同じ形の双子を持つ（`evidence()` が 3 組とも出す）。

**測った証拠**（`window()`）: 接頭辞 (0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)(4,1,0) を
持つ BMS 標準形 11689 個（<=10 列）で

    | 変換器                       | 単射 | 順序違反 |
    |------------------------------|------|----------|
    | rule.convert（シート 3 行 z<=1 で 1357/1358, 592 のみ外す） | ×（衝突 466 組） | 70 |
    | conv3X(BASE)                  | ○   | 0        |

衝突の根は {双子, M} -> 同じ像。つまり**シートの 891/897/898 に合わせる限り、
単射な変換器は作れない**。

順序も合っている（yaBMS `bms -c` で確認、どちらも -1）:
    BMS  双子 < M
    DBMS シートの 897 の像 (= conv3X(双子)) < conv3X(M)
つまり conv3X は「シートが 897 に貼った像」を**双子の像として正しく使っている**。

シート内部の食い違いも同じことを言う。シートは 856/858 で

    856 W_(w+1)*W_w                          -> ...(5,3)(6,2)(3,2,1)
    858 = 856 ++ (2,1,0)(3,2,0)              -> ...(5,3)(6,2)(3,2,1)(4,2)(5,3)

としているので「像に (4,2)(5,3) を足す」＝「ocf に + psi_W_(w+1)(W_(w+1))」。
896 は W_(w+1)^2*W_w -> ...(6,3)(6,2)(3,2,1) だから、シートの 897 の像は
ocf で読むと psi(W_(w+1)^2*W_w + psi_W_(w+1)(W_(w+1)))。
ところがシートの 897 の ocf 欄は psi(W_(w+1)^2 * psi_W_(w+1)(W_(w+1)))。
874（W_(w+1)*psi_W_(w+1)(W_(w+1)) -> ...(5,3)(6,2)(7,3)）の型に合わせるなら
897 の像は ...(6,3)(6,2)(7,3) で、それは**いまの conv3X が出しているもの**。

したがって (a) について直すところは無い。シート採点の実質満点は
1358 - 592（既知の誤記）- 891/897/898 = **1354**。

## 追記（課題 C5, 2026-08-27）: `sibbody2` は **採らなかった**

C3 の測定（シート・生成 <=8 列）では悪化が見えなかったが、**もっと長い行列**で
測ると片側に壊れる。`cofcheck()` が再現する。

| 検査 | BASE | BASE+sibbody2 |
|---|---|---|
| 展開閉包 {M<n> : M in gen<=6, n<=4} 22805 個の非標準 | 103 | **115**（+12、直すのは 0） |
| 共終性 C1 の破れ（生成 <=5 / <=6 列） | 7 / 136 | **8 / 149** |
| 共終性 C2 の破れ（生成 <=5 / <=6 列） | 0 / 0 | 0 / **4** |
| 性質 R の破れ（生成 <=5 / <=6 列） | 58 / 646 | **59 / 663** |

ここでいう共終性は

    C1: 任意の m<=8 に ある n<=24 で  f(M)<m> <= f(M<n>)
    C2: 任意の n<=24 に ある m<=40 で  f(M<n>) <= f(M)<m>

で、**証明済みの 2 行版ではちょうど 0 になる**（z=0 の 3 行標準形 <=6 列 1285 個で
C1 破れ 0・C2 破れ 0）。だから C1 の破れは指標の雑音ではなく本物の欠陥である。

壊れる代表例（`sibbody` の狙った系列そのもの）:

    M = (0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)
    BASE      ...(6,2,1)(5,1,0)     C1 成立
    sibbody2  ...(6,2,1)(6,1,0)     像<2> がどの n の f(M<n>) も追い越す

`not A`（子を持たない柱に限る）と `B[0][1] >= 1`（兄弟が行 1 を使う）を足すと
展開閉包の +12 と C2 の +4 は消える（103 / 0）が、C1 は 8 / 147 で +1 / +11 が
残る。よって `rows3.conv3` は
BASE のまま（v10）に据え置いた。本丸は C3 が書いたとおり `rule.depths` の機構。

## 結論 2: (b) は `sibbody2` で**きっちり半分**になる（<=7 列 3->1、<=8 列 84->42）

`sibbody`（行 1 の影を立てた柱の兄弟を本体の横に付ける）は無条件だとシートが
1219 に落ちる。`lad0` を立てた柱を除く（`sibbody0`）とシートは戻るが
<=6 列で非標準が 4 件出る。発火条件をもう 1 つ足したのが `sibbody2`:

    lad1 かつ not lad0 かつ**祖先の鎖に行 2 を使った柱がある**（ST[y][1]>=1, y<dd）

`sibbody3` は同じ条件を BMS 側（p の行 0 の祖先に行 2 を使う柱がある）で書いたもの。
<=7 列 77282 個で `sibbody2` と `sibbody3` の出力は完全一致（食い違い 0）。
BEST と `rule.convert` は <=7 列 77282 個のうち 1853 個で食い違う。

| 修正 | シート | <=6 列 非標準/単射/順序/z0 | <=7 列 非標準/順序/単射 |
|---|---|---|---|
| BASE | 1354/1358 | 0 / ○ / 0 / 0 | **3** / 0 / ○ |
| BASE+sibbody | 1219/1358 | 0 / × / 2 / 0 | - |
| BASE+sibbody0 | 1354/1358 | **4** / ○ / 0 / 0 | **48** / 0 / ○ |
| **BASE+sibbody2** | **1354/1358** | 0 / ○ / 0 / 0 | **1** / 0 / ○ |
| BASE + ruledepth（rule.depths を差し込む） | 1112/1358 | 1 / ○ / 0 / - | （測らず） |
| （参考）rule.convert | 1357/1358（592 のみ） | 0 / ○ / 0 / 0 | 0 / **6** / **×** |
| BASE+sibbody2+shadow2 | 887/1358 | 2381 / × / 281 / 676 | 28407 / 2955 / × |
| BASE+sibbody2+shadow3 | 1196/1358 | 116 / × / 100 / 0 | （測らず） |

**`sibbody2` はシートからは見えない**: シート 1358 行のうち像が変わる行は **0**。
生成した標準形では <=6 列 8387 個のうち 42 個、<=7 列 77282 個のうち 652 個の像が変わる。
（NOTES「シート採点だけでは足りない」のもう 1 つの実例）

シート 1358 行を BMS 順に並べたときの BEST の像: 順序違反 0・単射 ○・非標準 0。

**<=8 列 全数 781605 個**（`big()`, 930 秒・RSS 7.3GB。BASE と BEST を同じ生成で比較）:

| | 非標準 | 順序違反 | 単射 |
|---|---|---|---|
| BASE | 84 | 0 | ○ |
| **BEST (=BASE+sibbody2)** | **42** | 0 | ○ |

像が変わるのは 9062 / 781605（1.16%）。非標準はちょうど半分になり、
順序・単射はどちらも保たれる。新しく出る非標準は (b) と同じ族で、
どれも `(a,1,1)(a,1,0)(b,2,1)` のあとに兄弟が来る形:

    (0,0,0)(1,1,1)(1,1,1)(1,0,0)(2,1,1)(2,1,0)(3,2,1)(3,0,0)
      -> (0)(1)(2,1)(3,2,1)(3,2,1)(1)(2,1)(3,2,1)(2,1)(3,2,1)(3)   ← 非標準
    (0,0,0)(1,1,1)(2,0,0)(1,0,0)(2,1,1)(2,1,0)(3,2,1)(3,1,0)  など

窓での確認（`window()`）:

| 窓（接頭辞） | 個数 | BASE 非標準 | +sibbody2 非標準 |
|---|---|---|---|
| (0,0,0)(1,1,1)(2,0,0)(3,1,1) <=9 列 | 24329 | 431 | **187** |
| 同 ++(3,1,0) <=10 列 | 39512 | 3591 | **1698** |
（どちらも単射 ○・順序違反 0、BASE も +sibbody2 も）

## 残っている非標準（<=7 列で 1 件、<=8 列で 42 件）

    (0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)(4,2,0)
      -> (0)(1)(2,1)(3,2,1)(4)(5,1)(6,2,1)(6,1)(7,2,1)(7,2,0)   ← 非標準

6 列の接頭辞までは正しい（総当たりの正解と一致: ...(6,2,1)(6,1,0)(7,2,1) = D9）。
D9 の 1 列拡張で DBMS 標準形になるのは (7,1,0) までで **(7,2,0) は無い**。
D9 の次に大きい標準形は D9++(7,1,0)++... なので、BMS の (4,2,0) は
**DBMS の 2 列 (7,1,0)(8,2,0) に開く**はず（D9++(7,1,0) の 1 列拡張に (8,2,0) はある）。
つまり「行 2 を使わない柱 (e1>=2, e2=0) の前にもう 1 枚影を敷く」規則が要る。
素朴に入れた `shadow2`（直上の 行1=e1-1 の柱が影として書かれていないときに敷く）は
効きすぎてシートが 887 に落ちた。`shadow3`（兄弟であること・直前の同深さの柱が
「同じ行 1・より大きい行 2」であることを足したもの）でも 1196。
**発火条件は見つかっていない。**

### 注意: `rule.convert` はこの族にまったく別の像を出す（そちらの方が筋が良い）

    P6 = (0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)
    rule      ...(6,2,1)(6,2,0)(7,3,1)     ← (3,1,0) を**深い**分岐列にして 行 1 を 2 に上げる
    BEST      ...(6,2,1)(6,1,0)(7,2,1)     ← sibbody2（総当たりが出したという像）
    BASE      ...(6,2,1)(5,1,0)(6,2,1)     ← 重複

`rule` の像は P6 の 1 列 BMS 拡張 10 個すべてで DBMS 標準形になる（BEST は (4,2,0) で崩れる）。
窓での非標準の数も rule の方が少ない:

| 窓 | 個数 | BASE | BEST | rule.convert |
|---|---|---|---|---|
| (0,0,0)(1,1,1)(2,0,0)(3,1,1) <=8 列 | 3694 | 42 | 16 | **0** |
| 同 ++(3,1,0) <=9 列 | 5621 | 416 | 178 | **0**（ただし順序違反 2） |
| (0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)(4,1,0) <=9 列 | 1418 | 0 | 0 | 2（単射 ×・順序違反 2） |

rule の順序違反 2 件は (a) と同じ「短い綴りの敷き直し」由来なので、(b) とは別件。
`conv3X` がこの族で分岐列 (3,1,0) を深くできないのは、(2,0,0) で段の表 L が
リセットされて `base_s == base_d` になり、**浅い／深いの選択肢そのものが消える**から。
つまり (b) の本丸は sibbody ではなく**「段の表がリセットされた後の分岐列にも深い側を残す」**
かもしれない。`rule.depths` をそのまま差し込む（`b2d3X(..., ruledepth=True)`）のは
シートが 1112/1358 に落ちるので駄目（2 つの機構が噛み合わない）。

sandwich 検査（f(M)<n-1> <= f(M<n>) <= f(M)<n+1>, n=1..5）は BASE / BEST / rule
どれも通る（自己整合的なので、この検査では決められない）。

絞り込めたところまで（どれも 1 例ずつしか材料が無い）:

* 壊れる修正が必ず巻き込む正しい形（(a,y,1) の直後に兄弟 (a,y,0)）:
    - シート 312  ...(3,2,1)(3,2,0)(4,3,1)(4,3,0)
    - シート 1030 ...(4,2,0)(5,3,1)(5,3,0)
    - シート 1094 ...(5,3,1)(6,2,0)(5,3,0)
  どれも「影を足さない」のが正しい。
* 直さねばならない形は (7,2,1)@7 の兄弟 (7,2,0)@7 の 1 例だけ。
* 見えている差: 正しい 3 例では、(a,y,1) の**親**の 行 1 は y-1 で、その親自身が
  兄弟であっても 行 1 は落ちていない。壊れる 1 例では、親 (6,1,0)@6 は
  （sibbody2 が本体の横に動かした）兄弟で、**行 1 が 2 から 1 へ落ちている**。
  この「落ちた兄弟の下でだけ影を足す」を条件にできるかは未検証（材料 1 例）。

使い方:
    python3 x_spell.py evidence   (a) がシート誤りである証拠を出す
    python3 x_spell.py window     897 / (b) の窓で単射・順序・標準形性を測る
    python3 x_spell.py fix        修正案の採点（シート ＋ <=6 列 ＋ <=7 列）
    python3 x_spell.py big [列数] <=8 列の全数検査（15〜20 分・RSS 6〜7GB、要 background）
    python3 x_spell.py trace <BMS>  入力列 -> 出力列の対応
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import parse, show, expand, isstd, cmpmat, pim
import rows3
from rows3 import (split0, units_split, ok_place, fit, NOTLAST, ANCHOR,
                   closes_unit, Lat, is_branch, dmap_at, gen3, key)
import rule as RULE
import sheet3


# ---- m_residue の小道具のコピー（m_residue / rows3 の改稿に巻き込まれないため）
def closes_unitF(nxt, FIX):
    if nxt is None:
        return 'tailfirm' not in FIX
    if 'anchorC' in FIX and nxt == (1, 1, 1):
        return True
    return nxt[0] <= 1 and nxt[2] == 0


def padL(L, v, FIX):
    if 'L' in FIX and len(L) < v:
        return tuple(Lat(L, k) for k in range(v))
    return L[:v]


def copy_shiftF(block, e, ps0, prev0, nxt_after, FIX):
    out, prev = [], prev0
    for i, c in enumerate(block):
        nxt = block[i + 1] if i + 1 < len(block) else nxt_after
        if c == ANCHOR or ('anchorP' in FIX and c == (1, 1, 1)):
            prev = 0
        if is_branch(c):
            shallow = (prev == 0) or closes_unitF(nxt, FIX)
            prev = 0 if shallow else 1
            dl = 0 if shallow else (e if c[1] > ps0 else 0)
        else:
            dl = e if c[1] > ps0 else 0
        out.append((c[0] + 1, c[1] + dl, c[2]))
    return out


def gen_pref(pref, lim, zcap=1, ver='DBMS'):
    """`pref` を接頭辞に持つ `ver` の標準形を、全長 `lim` 列以下で全部。"""
    cur = [tuple(pref)]
    out = [tuple(pref)] if isstd(tuple(pref), ver) else []
    if not out:
        return []
    for _ in range(lim - len(pref)):
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

TR = []          # (出力列の添字, もとの列の添字 off, 役割) の記録
DBG = []


def conv3X(M, d=0, L=(), F=(), ps=(0, 0), pw=(0, 0), first=True, force=False,
           st=None, nx=None, FIX=(), D=None, off=0):
    """conv3F ＋ 分岐列の浅い/深いを `rule.depths` の表 `D` から読む版。

    `M` はつねに**もとの行列の連続部分**なので、先頭の添字 `off` を持ち回れば
    `D[off+k]` でその列の深さが引ける。写しの側 `pre` も `Aq` の添字で引く。
    """
    if st is None:
        st = {'ST': (), 'prev': None, 'dmap': []}
    if not M:
        return []
    p, r = M[0], M[1:]
    v, s2 = p[1], p[2]
    A, B = split0(p, r)
    oA, oB = off + 1, off + 1 + len(A)

    if v == 0:
        base_d = base_s = 0
        pl2, force1 = 0, False
    else:
        e = Lat(L, v - 1)
        base_d, pl2, force1, base_s = e[0] + 1, e[1], e[2], e[3] + 1
    first1 = F[v] if v < len(F) else True

    if p == ANCHOR:
        st['prev'] = 0
    if is_branch(p) and base_s != base_d:
        if D is not None:
            shallow = (D[off] == 0)
        else:
            nxt = M[1] if len(M) > 1 else nx
            shallow = (st['prev'] == 0) or closes_unitF(nxt, FIX)
            Mo = st.get('Mo')
            if Mo is not None and ('afterw' in FIX or 'hiclose' in FIX):
                pv = Mo[off - 1] if off >= 1 else None
                pv2 = Mo[off - 2] if off >= 2 else None
                onx = Mo[off + 1] if off + 1 < len(Mo) else None
                hi = RULE.hi_block(Mo, off)
                # after_w: 直前が「×w」の列 (k,0,0) でユニットの端にいるとき、
                # W_(w^2) 系（hi）で直前の分岐列が深いなら段は残る＝深い。
                if ('afterw' in FIX and st['prev'] == 1
                        and RULE.is_w_col(pv) and closes_unitF(onx, FIX)):
                    pnt = off > 0 and st['pim'][off - 1][0] == 0
                    shallow = not (hi and not pnt)
                # closes_hi_unit: (a,2,1)(a,2,0)(a,1,0) と積んだ直後に (1,1,1)
                # が来るなら段を上げずに閉じる＝浅い。
                if 'hiclose' in FIX and RULE.closes_hi_unit(
                        p, onx, pv, pv2, hi, RULE.is_repeat(Mo, off)):
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
        TR.append((off, p, 'lad0'))
        ST = ST[:d] + ((pw[0], pw[1]),)
        st.setdefault('sh', set()).add(d)
        dd = d + 1
    else:
        dd = fit(ST, d, h1)
        if dd is None:
            dd = max(d, len(ST))
    if lad1:
        cols.append((dd, base, pl2))
        TR.append((off, p, 'lad1'))
        ST = ST[:dd] + ((base, pl2),)
        st.setdefault('sh', set()).add(dd)
        dd += 1
    # 'shadow2': 行 2 を使わない柱 (e1>=2, e2=0) は、直上の 行 1 = e1-1 の柱が
    # **影として書かれた柱でない**ときだけ、もう 1 枚影を敷いてから本体を置く。
    # 'shadow3': 'shadow2' をきつく絞ったもの。兄弟として書かれ、直前の同深さの
    # 柱が「同じ行 1・より大きい行 2」で、直上の柱が影として書かれていないときだけ。
    if ('shadow3' in FIX and not lad1 and not lad0 and not first
            and e2 == 0 and e1 >= 2 and 1 <= dd < len(ST)
            and ST[dd][0] == e1 and ST[dd][1] > e2
            and ST[dd - 1][0] == e1 - 1
            and (dd - 1) not in st.get('sh', ())):
        cols.append((dd, e1 - 1, 0))
        TR.append((off, p, 'lad1c'))
        ST = ST[:dd] + ((e1 - 1, 0),)
        st.setdefault('sh', set()).add(dd)
        dd += 1
    if ('shadow2' in FIX and not lad1 and e2 == 0 and e1 >= 2
            and 1 <= dd <= len(ST) and ST[dd - 1][0] == e1 - 1
            and (dd - 1) not in st.get('sh', ())):
        cols.append((dd, e1 - 1, 0))
        TR.append((off, p, 'lad1b'))
        ST = ST[:dd] + ((e1 - 1, 0),)
        st.setdefault('sh', set()).add(dd)
        dd += 1
    if not ok_place(ST, dd, e1):
        x = fit(ST, dd, e1)
        if x is not None:
            dd = x
    cols.append((dd, e1, e2))
    TR.append((off, p, 'body'))
    DBG.append(dict(off=off, p=p, d=d, dd=dd, lad0=lad0, lad1=lad1, base=base,
                    e1=e1, e2=e2, v=v, s2=s2, pl2=pl2, first=first, first1=first1,
                    L=L, ST=tuple(ST), nB=len(B), nA=len(A)))
    ST = ST[:dd] + ((e1, e2),)
    st['ST'] = ST
    st['dmap'] = st['dmap'][:p[0]] + [dd]

    fc = (not lad1) and first1 and s2 == pl2
    f0 = (not lad0) and first and (v, s2) == ps
    if e1 == base + 1 and v >= 1:
        Lb = padL(L, v - 1, FIX) + ((base, pl2, False, Lat(L, v - 1)[3]),)
    else:
        Lb = L
    LA = padL(Lb, v, FIX) + ((e1, s2, fc, e1),)
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
            oAq = oq + 1
            oBq = oAq + len(Aq)
            blk = [p] + list(A) + list(U)
            for na in (q, NOTLAST):
                if D is not None:
                    # 写しの側の深さは、写しが載っている Aq の添字から引く
                    pre = [(c[0] + 1,
                            c[1] + ((e if c[1] > ps[0] else 0)
                                    if (not is_branch(c)
                                        or (oAq + i < len(D) and D[oAq + i]))
                                    else 0),
                            c[2]) for i, c in enumerate(blk)]
                else:
                    pre = copy_shiftF(blk, e, ps[0], st['prev'], na, FIX)
                if list(Aq[:len(pre)]) == pre:
                    break
            else:
                continue
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
                continue
            Lr = padL(L, v, FIX) + (((base, pl2, fc, base) if e else (e1, s2, fc, e1)),)
            hd = lambda *ls: next((l[0] for l in ls if l), nx)
            rd = (d + 1 + e if (not rest2 or rest2[0][0] == p[0] + 1)
                  else dmap_at(st, rest2[0][0] - 1))
            cA = conv3X(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
                        U[0] if U else na, FIX, D, oA)
            cU = conv3X(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na,
                        FIX, D, oU)
            if 'resid' in FIX:
                cR = conv_residX(rest2, rd, Lr, (v, s2), (e1, e2), st, hd(Bq),
                                 FIX, D, oR)
            else:
                cR = conv3X(rest2, rd, Lr, (False,) * 12,
                            (v, s2), (e1, e2), False, False, st, hd(Bq), FIX, D, oR)
            cB = conv3X(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                        FIX, D, oBq)
            return cols + cA + cU + cR + cB

    # 'sibbody': 行 1 の影を立てた柱の**兄弟**は、影の横ではなく本体の横に付く。
    db = dd if ('sibbody' in FIX and lad1) else d
    dc = dd if ('sibbody0' in FIX and lad1 and not lad0) else d
    if 'sibbody0' in FIX:
        db = dc
    # 'sibbody2': 行 1 の影を立てた柱でも、行 0 の影を立てていない（lad0=False）で、
    # かつ**祖先の鎖に行 2 を使った柱がある**ときだけ、兄弟を本体の横に付ける。
    if 'sibbody2' in FIX and lad1 and not lad0:
        if any(ST[y][1] >= 1 for y in range(min(dd, len(ST)))):
            db = dd
    # 'sibbody3': 同じだが「直前の 行 2 を使った柱」ではなく「p の行 0 の祖先」で見る。
    if 'sibbody3' in FIX and lad1 and not lad0:
        Mo = st.get('Mo')
        if Mo is not None:
            x = off
            while True:
                q = None
                for k in range(x - 1, -1, -1):
                    if Mo[k][0] < Mo[x][0]:
                        q = k
                        break
                if q is None:
                    break
                if Mo[q][2] >= 1:
                    db = dd
                    break
                x = q
    cA = conv3X(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
                B[0] if B else nx, FIX, D, oA)
    cB = conv3X(B, db, L, FA, (v, s2), (e1, e2), False, False, st, nx, FIX, D, oB)
    return cols + cA + cB


def conv_residX(rest, rd, Lr, ps, pw, st, nx, FIX, D, off):
    out = []
    while rest:
        m0 = rest[0][0]
        i = 1
        while i < len(rest) and rest[i][0] >= m0:
            i += 1
        head, tail = rest[:i], rest[i:]
        nx2 = tail[0] if tail else nx
        out += conv3X(head, rd, Lr, (False,) * 12, ps, pw, False, False,
                      st, nx2, FIX, D, off)
        if not tail:
            break
        rd = max(0, rd - (m0 - tail[0][0]))
        off += i
        rest = tail
    return out


def b2d3X(M, FIX=(), ruledepth=False):
    del TR[:]
    del DBG[:]
    D = RULE.depths(tuple(M)) if ruledepth else None
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M),
          'pim': pim(tuple(M)) if M else []}
    return tuple(conv3X(list(M), FIX=FIX, D=D, st=st))


def score_X(FIX, A6=None, A7=None, zc=1):
    f = lambda M: b2d3X(M, FIX)
    T = sheet3.load(1)
    bad = [(row, b, dd, tuple(f(b))) for row, b, dd in T if tuple(f(b)) != dd]
    res = {'sheet': (len(T) - len(bad), len(T)), 'bad': bad}
    if A6 is not None:
        W = [f(M) for M in A6]
        res['ns'] = sum(1 for N in W if not isstd(N, 'DBMS'))
        res['inj'] = len(set(W)) == len(W)
        res['ord'] = sum(1 for i in range(len(A6) - 1) if cmpmat(W[i], W[i + 1]) >= 0)
        import rows2
        res['z0'] = sum(1 for M, N in zip(A6, W)
                        if all(c[2] == 0 for c in M)
                        and N != rows3.pad(rows2.convC(rows3.two(M))))
    if A7 is not None:
        W7 = [f(M) for M in A7]
        res['ns7'] = sum(1 for N in W7 if not isstd(N, 'DBMS'))
        res['ord7'] = sum(1 for i in range(len(A7) - 1) if cmpmat(W7[i], W7[i + 1]) >= 0)
        res['inj7'] = len(set(W7)) == len(W7)
    return res


BASE = ('resid', 'L', 'afterw', 'hiclose')


def trace(s, FIX=None):
    FIX = BEST if FIX is None else FIX
    M = parse(s, 3) if isinstance(s, str) else tuple(s)
    N = b2d3X(M, FIX)
    print('入力 %s' % show(M))
    print('出力 %s' % show(N))
    for i, (c, (off, p, role)) in enumerate(zip(N, TR)):
        print('  d%-2d %-9s <- c%-2d %-9s %s' % (i, str(c), off, str(p), role))
    return N, list(TR)


# ---------------------------------------------------------------- 検査台
_A = {}


def pool(lim):
    if lim not in _A:
        _A[lim] = sorted(gen3('BMS', lim, zcap=1), key=key)
    return _A[lim]


def battery(FIX=None, lim7=True, tag=''):
    """シート採点 ＋ <=6 列（標準形性/単射/順序/z=0）＋ <=7 列（標準形性/順序/単射）。"""
    FIX = BASE if FIX is None else FIX
    import rows2
    f = lambda M: b2d3X(M, FIX)
    t0 = time.time()
    T = sheet3.load(1)
    bad = [(row, b, d, tuple(f(b))) for row, b, d in T if tuple(f(b)) != d]
    r = {'FIX': FIX, 'sheet': (len(T) - len(bad), len(T)), 'bad': bad}
    A6 = pool(6)
    W = [f(M) for M in A6]
    r['ns6'] = [(M, N) for M, N in zip(A6, W) if not isstd(N, 'DBMS')]
    r['inj6'] = len(set(W)) == len(W)
    r['ord6'] = [i for i in range(len(A6) - 1) if cmpmat(W[i], W[i + 1]) >= 0]
    r['z06'] = [(M, N) for M, N in zip(A6, W)
                if all(c[2] == 0 for c in M)
                and N != rows3.pad(rows2.convC(rows3.two(M)))]
    if lim7:
        A7 = pool(7)
        W7 = [f(M) for M in A7]
        r['ns7'] = [(M, N) for M, N in zip(A7, W7) if not isstd(N, 'DBMS')]
        r['ord7'] = [i for i in range(len(A7) - 1) if cmpmat(W7[i], W7[i + 1]) >= 0]
        r['inj7'] = len(set(W7)) == len(W7)
    r['sec'] = time.time() - t0
    print('%-42s シート %4d/%d | <=6列 非標準 %d 単射 %s 順序 %d z0 %d%s (%.0fs)'
          % (tag or (','.join(FIX) or '(なし)'), r['sheet'][0], r['sheet'][1],
             len(r['ns6']), r['inj6'], len(r['ord6']), len(r['z06']),
             (' | <=7列 非標準 %d 順序 %d 単射 %s'
              % (len(r['ns7']), len(r['ord7']), r['inj7'])) if lim7 else '',
             r['sec']))
    return r


BEST = BASE + ('sibbody2',)

# (a) の 3 行と、その「長い綴りの双子」
TWINS = [
    (891, '(0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)(3,2,0)(4,1,0)(5,2,0)',
          '(0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)(3,2,0)(4,1,0)(1,1,1)(2,1,0)(3,2,0)'),
    (897, '(0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)(4,1,0)(5,2,0)',
          '(0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)(4,1,0)(1,1,1)(2,1,0)(3,2,0)'),
    (898, '(0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)(4,1,0)(5,2,0)(6,2,0)',
          '(0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)(4,1,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)'),
]


def evidence(FIX=None):
    """(a) の 3 行がシート誤りである証拠。

    各行について「長い綴りの双子」を出し、双子が BMS 標準形で M より小さく、
    conv3X(双子) がシートの DBMS 欄そのものであることを示す。
    """
    FIX = BEST if FIX is None else FIX
    T = {row: (b, d) for row, b, d in sheet3.load(1)}
    for row, ms, ts in TWINS:
        M, Tw = parse(ms, 3), parse(ts, 3)
        b, d = T[row]
        assert b == M
        print('シート行 %d' % row)
        print('  M    %-58s std=%s' % (show(M), isstd(M, 'BMS')))
        print('  双子 %-58s std=%s  双子<M=%s'
              % (show(Tw), isstd(Tw, 'BMS'), cmpmat(Tw, M) < 0))
        print('  シートの DBMS     %s' % show(d))
        print('  conv3X(双子)      %s   一致=%s'
              % (show(b2d3X(Tw, FIX)), tuple(b2d3X(Tw, FIX)) == d))
        print('  conv3X(M)         %s   std=%s'
              % (show(b2d3X(M, FIX)), isstd(b2d3X(M, FIX), 'DBMS')))


def window(lim=10, FIXES=None):
    """窓を切って 単射・順序・標準形性 を測る。`rule.convert` とも比べる。"""
    import functools
    FIXES = FIXES or [('BASE', BASE), ('+sibbody2', BEST)]
    wins = [('897 の窓', '(0,0,0)(1,1,1)(2,1,0)(3,2,0)(4,2,0)(4,1,0)', lim),
            ('(b) の窓', '(0,0,0)(1,1,1)(2,0,0)(3,1,1)', lim - 1),
            ('(b) の窓2', '(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)', lim)]
    for nm, pref, lm in wins:
        B = sorted(gen_pref(parse(pref, 3), lm, zcap=1, ver='BMS'),
                   key=functools.cmp_to_key(cmpmat))
        cases = list(FIXES) + [('rule.convert', None)]
        for tag, FIX in cases:
            W = [tuple(RULE.convert(m)) if FIX is None else b2d3X(m, FIX)
                 for m in B]
            ns = sum(1 for w in W if not isstd(w, 'DBMS'))
            od = sum(1 for i in range(len(W) - 1) if cmpmat(W[i], W[i + 1]) >= 0)
            print('%-10s %-12s %6d 個: 非標準 %5d 単射 %-5s 順序違反 %4d'
                  % (nm, tag, len(B), ns, len(set(W)) == len(W), od))


def big(lim=8, FIX=None):
    """<=`lim` 列を全数で 標準形性 / 順序 / 単射 だけ測る。

    <=8 列は 781605 個。生成だけで約 460 秒、全部で 15〜20 分、RSS は 6〜7GB。
    必ず `run_in_background` で回すこと。
    """
    import core, resource
    FIX = BEST if FIX is None else FIX
    t0 = time.time()
    cur, allm = [()], []
    for k in range(1, lim + 1):
        nxt = []
        for S in cur:
            amax = (S[-1][0] + 1) if S else 0
            for a in range(amax + 1):
                for b in range(a + 1):
                    for c in range(min(b, 1) + 1):
                        T = S + ((a, b, c),)
                        if isstd(T, 'BMS'):
                            nxt.append(T)
        cur = nxt
        allm.extend(cur)
        print('%d 列 %d 個 累計 %d (%.0fs, RSS %.1fGB)'
              % (k, len(cur), len(allm), time.time() - t0,
                 resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6), flush=True)
    core._isstd_memo.clear(); core._exp_memo.clear(); core._flat_memo.clear()
    allm.sort(key=key)
    W = [b2d3X(M, FIX) for M in allm]
    ns = []
    for i, w in enumerate(W):
        if not isstd(w, 'DBMS'):
            ns.append(i)
        if i % 200000 == 0:
            core._isstd_memo.clear(); core._flat_memo.clear()
    od = [i for i in range(len(W) - 1) if cmpmat(W[i], W[i + 1]) >= 0]
    print('<=%d 列 %d 個: 非標準 %d 順序違反 %d 単射 %s (%.0fs)'
          % (lim, len(allm), len(ns), len(od), len(set(W)) == len(W),
             time.time() - t0), flush=True)
    for i in ns[:10]:
        print('   非標準 %-46s -> %s' % (show(allm[i]), show(W[i])), flush=True)
    return allm, W, ns, od


def cofcheck(lim=6, nn=4, FIXES=None):
    """課題 C5 の判定台: 展開閉包の非標準と、共終性 C1/C2 を BASE と BEST で。

    `check()` の性質 R は 3 行では偽なので目安どまり。代わりに使うのが
    共終性 C1/C2 で、**証明済みの 2 行版ではちょうど 0 になる**（下の zc=True）。
    """
    FIXES = FIXES or [('BASE', BASE), ('+sibbody2', BEST)]
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    S = set()
    for M in A:
        if len(M) > 1:
            for n in range(1, nn + 1):
                S.add(tuple(expand(M, n)))
    S = sorted(S, key=key)
    core._exp_memo.clear()
    print('展開閉包 {M<n> : M in gen<=%d, n<=%d} : %d 個' % (lim, nn, len(S)),
          flush=True)
    base_ns = None
    for tag, FIX in FIXES:
        f = lambda M, FIX=FIX: tuple(b2d3X(M, FIX))
        ns = set()
        for i, X in enumerate(S):
            if not isstd(f(X), 'DBMS'):
                ns.add(X)
            if i % 40000 == 0:
                core._isstd_memo.clear(); core._flat_memo.clear()
        d = ('' if base_ns is None
             else '  (新しく壊す %d / 直す %d)'
                  % (len(ns - base_ns), len(base_ns - ns)))
        if base_ns is None:
            base_ns = ns
        print('  %-11s 非標準 %d%s' % (tag, len(ns), d), flush=True)
    # 共終性
    for L in (5, lim):
        AL = sorted(gen3('BMS', L, zcap=1), key=key)
        for tag, FIX in FIXES:
            f = lambda M, FIX=FIX: tuple(b2d3X(M, FIX))
            print('  <=%d 列 %-11s C1 破れ %4d  C2 破れ %4d'
                  % ((L, tag) + cof_counts(f, AL)), flush=True)
            core._exp_memo.clear(); core._isstd_memo.clear()
        # 証明済みの 2 行版（z=0 の断片）はちょうど 0 になる
        z = [M for M in AL if all(c[2] == 0 for c in M)]
        print('  <=%d 列 z=0 だけ %d 個（証明済みの 2 行版）: C1 破れ %d  C2 破れ %d'
              % ((L, len(z)) + cof_counts(lambda M: tuple(b2d3X(M, BASE)), z)),
              flush=True)
        core._exp_memo.clear(); core._isstd_memo.clear()


def cof_counts(f, A, mm=8, nn=24, mc=40):
    """(C1 の破れ, C2 の破れ) の個数。"""
    b1 = b2 = 0
    for M in A:
        if len(M) < 2:
            continue
        N = f(M)
        E = [tuple(expand(N, m)) for m in range(1, mc + 1)]
        G = [tuple(f(expand(M, n))) for n in range(1, nn + 1)]
        if any(not any(cmpmat(E[m], g) <= 0 for g in G) for m in range(mm)):
            b1 += 1
        if any(not any(cmpmat(g, e) <= 0 for e in E) for g in G):
            b2 += 1
    return b1, b2


def fixreport(lim7=True):
    for tag, FIX in [('BASE', BASE),
                     ('BASE+sibbody', BASE + ('sibbody',)),
                     ('BASE+sibbody0', BASE + ('sibbody0',)),
                     ('BASE+sibbody2', BEST),
                     ('BASE+sibbody3', BASE + ('sibbody3',)),
                     ('BASE+sibbody2+shadow2', BEST + ('shadow2',))]:
        r = battery(FIX, lim7=lim7, tag=tag)
        if r.get('ns7'):
            for M, N in r['ns7'][:3]:
                print('      非標準: %-46s -> %s' % (show(M), show(N)))


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'fix'
    if cmd == 'evidence':
        evidence()
    elif cmd == 'window':
        window(int(sys.argv[2]) if len(sys.argv) > 2 else 10)
    elif cmd == 'fix':
        fixreport()
    elif cmd == 'cof':
        cofcheck(int(sys.argv[2]) if len(sys.argv) > 2 else 6)
    elif cmd == 'big':
        big(int(sys.argv[2]) if len(sys.argv) > 2 else 8)
    elif cmd == 'trace':
        trace(sys.argv[2])
    else:
        print(__doc__)
