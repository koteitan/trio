"""課題 E1: 単射性から攻める（双子の分離）。

**この規則は採用され、`rows3.conv3` に `V12['mark']` として入った**（課題 E5,
2026-08-27）。既定は局所版 `leaves_mark_local`。このファイルは実験の記録として
残してあるが、`conv3` のコピーは **v11 のまま**（`newterm` は入っていない）ので、
採点に使うなら `z1.score(f=rows3.b2d3)` のように `f` を渡すこと。

`rows3.conv3` (v11) のコピー ＋ **残余なしの縮約に「印」のガード**を足したもの。

    python3 z1.py inj 7        単射の破れを列挙（<=7 列, 170 秒）
    python3 z1.py score 6      7 つの土俵で採点

**旗**（`OPT`。既定は空 = v11 と完全に同じ挙動）

    OPT['mark']       残余なしの縮約に「像に印が残るか」のガードを付ける（採用案）
    OPT['mark_local'] 同じものの**局所版**（Lean に載る形）。gen<=7 で `mark` と差 0
    OPT['drop_empty'] 残余なしの縮約を丸ごと落とす（**不採用**。シート -34）

--------------------------------------------------------------------------
1. 双子の形（実測、v11・<=7 列 77282 個）
--------------------------------------------------------------------------

単射の破れは 166 組（本当の失敗 0）。**そのうち 164 組は同じ 1 つの枝**から出る:
縮約の `rest2 が空・e=1・deep_end` の枝。143 組はぴったり

    双子 B = M ++ (1,1,0) ++ { (a+1, b+1 if b>0 else 0, c) : (a,b,c) in M[1:] }

の形（`twin`）。残り 23 組も「もと ++ アンカー ++ 写し」の変種である。
例:

    もと (0,0,0)(1,1,1)(2,1,0)(3,2,1)(3,0,0)(2,1,0)                       6 列
    双子 ++ (1,1,0)(2,2,1)(3,2,0)(4,3,1)(4,0,0)(3,2,0)                   12 列
    像   (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,2,0)(5,3,1)(5,0,0)(4,2,0)        同じ

--------------------------------------------------------------------------
2. どの柱の浅い／深いが違うべきか（決着）
--------------------------------------------------------------------------

縮約は「写しを書かない代わりに、本体の**末尾の分岐列**を番兵 `NOTLAST` で
深く綴る」ことで写しを記録する。分離できている手本（シート行338/385）:

    (0,0,0)(1,1,1)(2,1,0)            -> ...(4,1,0)   末尾の分岐列が**浅い**
    その双子 ++(1,1,0)(2,2,1)(3,2,0) -> ...(4,2,0)   縮約が**深く**した

ところが本体の末尾がもともと深く綴られていると（`after_w` の上書きなどで）、
深くしても像は 1 ビットも変わらず、写しが像から消える:

    (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,0,0)(2,1,0)  -> ...(5,0,0)(4,2,0)  末尾が既に深い
    （この像は**シート行1578 で正しいと確認済み**。もとの側は直してはいけない）

**シートが決着させた**: もとの像は正しい。誤っているのは双子の側で、
双子は写しを書き出した長い像 `img(M) ++ img(M)[2:]` にならなければならない
（シート行1583/1584 がまさにその形: psi(X) と psi(X + psi_1(X))）。

--------------------------------------------------------------------------
3. 入れた規則（`leaves_mark` / `leaves_mark_local`）
--------------------------------------------------------------------------

    残余なしの縮約は「写しを飲んだ印が像に残る」ときだけ許す。

大域版 `leaves_mark`: 本体を 2 通り（次の列 = `NOTLAST` / 次の列 = アンカー q）
走らせ、像が違うときだけ縮約する。局所版 `leaves_mark_local`（Lean 向け）:

    印が残る <=> 末尾の分岐列を決める直前の段 prev != 0
                 かつ after_w が firing しない
                 かつ closes_hi_unit が firing しない

（q はアンカーなので `closes_unit(q)` は真 = 自然な綴りは浅い。上書きの 2 つは
2 通りで同じ結論を出すので、firing したら印は残らない。）
両者は **gen<=7 の 77282 個で像の差 0**、シートも同じ 1354。

--------------------------------------------------------------------------
4. 採点（すべて実測）
--------------------------------------------------------------------------

| 土俵 | v11 | mark（採用案） |
|---|---|---|
| シート 3 行 z<=1 (1358) | 1354 | **1354** |
| z=0 <=7 列 7256 個で `rows2.convC` と食い違い | 0 | **0** |
| z=0 <=8 列 44653 個で同 | 0 | **0** |
| 単射: 閉包 15611 個の衝突 | 24 | **0** |
| 単射: 閉包 127182 個の衝突 | 24 | **0** |
| 単射: v11 の破れ 166 組のうち残るもの | 166 | **2** |
| 非標準 <=6 列 8387 個 | 0 | **0** |
| 非標準 <=7 列 77282 個 | 3 | **3** |
| 順序違反 <=7 列 | 0 | **0** |
| 像のハッシュ衝突 <=7 列 | 0 | **0** |
| ImgClosedT 速い道 <=5 列 m<=3 | 2996/3051, A 28 個 | **同じ（集合も同一）** |
| ImgClosedT 辞書 <=5 列 m<=3 | 2971/3051, A 43 個 | **同じ（集合も同一）** |
| 共終性 <=5 列 C1 / C2 | 7 / 0 | **7 / 0（C1 の集合も同一）** |
| 共終性 <=6 列 C1 / C2 | 121 / 0 | **121 / 0** |

局所版 `mark_local` はどの欄も `mark` と同じ数字（共終性 <=5 列 7/0、
<=6 列 121/0、閉包 127182 の衝突 0、シート 1354、gen<=7 の像も差 0）。
C1 の破れの集合も <=5 列・<=6 列とも v11 と**まったく同じ**。

**片側にしか動かない**。もっと強く、像が変わるのは**双子だけ**である:

    gen3(<=7 列) 77282 個  v11 と mark の像の差 **0**
    双子 3609 個（gen3(<=6) の双子で標準形のもの）  像の差 **24**

つまり <=7 列の中で測れる指標（非標準・順序・z=0・シート・ImgClosedT・共終性）は
**定義から動きようがない**。動くのは長い双子だけで、そこは 24 個ぜんぶが
「潰れていたものが分離した」側である。

不採用: `OPT['drop_empty']`（縮約の枝を丸ごと落とす）はシート 1354 -> 1320。
落ちる 34 件はすべて「もともと浅い末尾を深くして分離できていた」正解である。

--------------------------------------------------------------------------
5. 残った 2 組（別の病気）
--------------------------------------------------------------------------

    (0,0,0)(1,1,1)(2,1,0)(3,2,1)(3,2,0)(3,1,0)(1,1,1)
    (0,0,0)(1,1,1)(2,2,1)(3,2,1)(3,2,0)(3,1,0)(1,1,1)

こちらは `rest2 が空でない・deep_end=False` の縮約で、残余 (2,2,1) の像が
もとの末尾 (1,1,1) の像と同じ (3,2,1) になって潰れる。`mark` の枝ではない。

注意: `inv3.d2b3` は v11 に合わせて作られているので、`mark` を入れると
往復検査（`inj_pairs` の「本当の失敗」）に 7 件出る。中身を見ると全部
「d2b3 が双子を返し、その双子の像が今は長くなっている」だけで、
単射は直っている（`inj_closure` が `inv3` に頼らずにそれを示す）。
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import parse, show, expand, isstd, cmpmat
import rows3
from rows3 import (gen3, key, split0, translate3, olt3, shift1, units_split,
                   predlab, ok_place, fit, NOTLAST, ANCHOR, closes_unit, par0,
                   hi_block, is_repeat, is_w_col, closes_hi_unit, Lat, padL,
                   is_branch, dmap_at, pad, two, check, imgclosed_fast)
from rows2 import convC as convC2

# ---------------------------------------------------------------- 実験の切替
# 既定は v11 と完全に同じ挙動。旗を立てて実験する。
OPT = {}
TRACE = None    # リストを入れると縮約の発火を記録する
TRACE2 = None   # リストを入れると分岐列の浅い／深いを記録する


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



def _snap(st):
    return (st['ST'], st['prev'], list(st['dmap']), st.get('nc', 0))


def _restore(st, s):
    st['ST'], st['prev'], st['dmap'], st['nc'] = s[0], s[1], list(s[2]), s[3]


def leaves_mark(A, U, dd, d, LA, L, FA, v, s2, e1, e2, st, na, q, oA, oU):
    """残余なしの縮約が像に印を残すか（課題 E1）。

    縮約は「写しを書かない代わりに、本体の末尾の分岐列を `NOTLAST` で深く綴る」
    ことで写しを記録する。ところが本体の末尾がもともと深く綴られていると
    （after_w などで）、深くしても何も変わらず、写しは像から消えてしまう。
    そのとき `M` と `M ++ q ++ 写し` が同じ像になる（単射性の破れ）。

    自然な綴り（次の列 = `q`）と強制の綴り（次の列 = `na`）を両方走らせて、
    像が違うときだけ縮約を許す。`st` は 2 回とも同じ状態から始めて戻す。
    """
    s0 = _snap(st)
    rec0 = dict(st['rec'])
    a1 = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
               U[0] if U else na, oA)
    u1 = conv3(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na, oU)
    _restore(st, s0)
    a2 = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
               U[0] if U else q, oA)
    u2 = conv3(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, q, oU)
    _restore(st, s0)
    st['rec'] = rec0
    return (a1, u1) != (a2, u2)



def leaves_mark_local(A, U, dd, d, LA, L, FA, v, s2, e1, e2, st, na, oA, oU,
                      ob):
    """`leaves_mark` の**局所版**（Lean に載せられる形）。

    2 通り走らせて像を比べる代わりに、印が残る条件を直接書く。
    印は「本体の末尾の分岐列 c = Mo[ob] が `NOTLAST` で深く綴られ、
    自然な綴り（次の列 = アンカー q）では浅く綴られる」こと。
    `q` はアンカーなので `closes_unit(q)` はいつも真、したがって

        自然 = 浅い（上書きが無ければ）
        強制 = 深い <=> 決める直前の段 prev != 0（上書きが無ければ）
                        （prev は None / 0 / 1 の 3 値。None は「まだ分岐列を
                          1 本も見ていない」で、`prev == 0` は偽なので深い側）

    上書きは 2 つ。どちらも 2 通りで**同じ**結論を出すので、
    firing したら印は残らない:

        after_w        prev==1 かつ 直前が「x w」 かつ 次がユニットを閉じる
        closes_hi_unit (a,2,1)(a,2,0)(a,1,0) の次が (1,1,1)

    したがって
        印が残る <=> prev != 0 かつ after_w も closes_hi_unit も firing しない
    （`prev == 'tie'`、つまり浅い／深いの選択肢が無いときも印は残らない）。
    """
    s0 = _snap(st)
    rec0 = dict(st['rec'])
    conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
          U[0] if U else na, oA)
    conv3(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na, oU)
    prev_in = st['rec'].get(ob, 'none')
    _restore(st, s0)
    st['rec'] = rec0
    if prev_in == 0 or prev_in == 'tie' or prev_in == 'none':
        return False        # prev==0 なら強制でも浅い / tie なら選択肢が無い
    Mo = st['Mo']
    c = Mo[ob]
    pv = Mo[ob - 1] if ob >= 1 else None
    pv2 = Mo[ob - 2] if ob >= 2 else None
    onx = Mo[ob + 1] if ob + 1 < len(Mo) else None
    if prev_in == 1 and is_w_col(pv) and closes_unit(onx):
        return False                     # after_w が両方を同じにする
    if closes_hi_unit(c, onx, pv, pv2, hi_block(Mo, ob), is_repeat(Mo, ob)):
        return False                     # closes_hi_unit が両方を浅くする
    return True


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
        st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0,
              'rec': {}}
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
        # 課題 E1: 局所版のガードのために「決める直前の段」を残す。
        st['rec'][off] = st['prev']
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
        if TRACE2 is not None:
            TRACE2.append({'off': off, 'p': tuple(p), 'shallow': shallow,
                           'base_s': base_s, 'base_d': base_d, 'd': d,
                           'nxt': tuple(nxt) if nxt else None})
    else:
        base = base_d
        if is_branch(p):
            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い
        if TRACE2 is not None and is_branch(p):
            TRACE2.append({'off': off, 'p': tuple(p), 'shallow': 'tie',
                           'base_s': base_s, 'base_d': base_d, 'd': d,
                           'nxt': None})

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
            elif OPT.get('drop_empty') or e == 0 or not deep_end:
                # 残余なしの縮約は「行 1 ずれ」かつ「残りが分岐列で終わる」ときだけ
                # （NOTES §7 の strip_lift の適用条件と同じ）
                continue
            elif OPT.get('mark_local') and not leaves_mark_local(
                    A, U, dd, d, LA, L, FA, v, s2, e1, e2, st, na, oA, oU,
                    off + len([p] + list(A) + list(U)) - 1):
                continue
            elif OPT.get('mark') and not leaves_mark(
                    A, U, dd, d, LA, L, FA, v, s2, e1, e2, st, na, q, oA, oU):
                # **課題 E1 の新しいガード**。残余なしの縮約は「写しを飲んだ」印が
                # 像に残るときだけ許す。印は `na = NOTLAST` で A / U の末尾の
                # 分岐列が深く綴られること。自然な綴り（次の列 = q）と同じなら
                # 写しは像に 1 ビットも現れないので、写しの無い行列と同じ像に
                # 潰れる（＝単射性の破れ）。
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
            if TRACE is not None:
                TRACE.append({'off': off, 'p': tuple(p), 'e': e,
                              'nU': len(U), 'nA': len(A), 'npre': len(pre),
                              'rest2': len(rest2), 'deep_end': deep_end,
                              'na': tuple(na)})
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
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0,
          'rec': {}}
    return tuple(conv3(list(M), st=st)), st['nc']


def b2d3(M):
    return b2d3n(M)[0]


# ---------------------------------------------------------------- 単射の検査
def inj_pairs(f, lim, verbose=0):
    """単射の破れを**列数をまたいで**集める。

    `gen3(lim)` の M の像 N に逆写像 `inv3.d2b3` を当て、戻り B が M と違い、
    しかも B が BMS 3 行 z<2 標準形で f(B) == N なら、M と B は同じ像に潰れて
    いる（＝単射の破れ）。B は lim 列より長いことが多いので、`gen3(lim)` の
    中だけで比べても見つからない。

    返り値 (破れの対のリスト [(M, B, N)], 本当の失敗のリスト [(M, N, B)])。
    """
    from inv3 import d2b3
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    pairs, hard = [], []
    for i, M in enumerate(A):
        if i % 3000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        N = tuple(f(M))
        try:
            B = d2b3(N)
        except Exception:
            B = None
        if B == tuple(M):
            continue
        if (B and isstd(B, 'BMS') and all(c[2] <= 1 for c in B)
                and tuple(f(list(B))) == N):
            pairs.append((tuple(M), tuple(B), N))
        else:
            hard.append((tuple(M), N, B))
    return pairs, hard


def tail_shape(M, B):
    """双子 B が「もと M ＋ 尾」の形か。共通の接頭辞の長さと尾を返す。"""
    k = 0
    while k < len(M) and k < len(B) and M[k] == B[k]:
        k += 1
    return k, B[k:]


# ---------------------------------------------------------------- 採点台
def score(f=None, sheet=True, gen=6, z0=8, injlim=6, imgc=3, imglim=5,
          cof=6, tag=''):
    """7 つの土俵で採点する。数字は NOTES の v11 の表と比べる。

      1 シート            満点 1354/1358
      2 z=0               gen3 z=0 で rows2.convC と一致（食い違い 0 が満点）
      3 単射              列数をまたぐ衝突（<=6 列 7 組 / <=7 列 166 組）
      4 ImgClosedT        速い道の外れ（<=5 列 A が 28 個）
      5 非標準            <=7 列 3 件
      6 順序              <=7 列 0 件
      7 共終性 C1/C2      <=6 列 121 / 0
    """
    if f is None:
        f = b2d3
    t0 = time.time()
    R = {'tag': tag}
    if sheet:
        import sheet3
        ok, tot = sheet3.score(f=f, show_n=0)
        R['sheet'] = (ok, tot)
    if z0:
        A = gen3('BMS', z0, zcap=0)
        bad = sum(1 for M in A if tuple(f(M)) != pad(convC2(two(M))))
        R['z0'] = (bad, len(A))
        print('  z=0 <=%d列 %d 個: 2 行版と食い違い %d' % (z0, len(A), bad))
    if injlim:
        P, H = inj_pairs(f, injlim)
        R['inj'] = (len(P), len(H))
        print('  単射 <=%d列: 破れ %d 組  本当の失敗 %d 件' % (injlim, len(P), len(H)))
    A = sorted(gen3('BMS', gen, zcap=1), key=key)
    W = [tuple(f(M)) for M in A]
    ns = sum(1 for N in W if not isstd(N, 'DBMS'))
    ordbad = sum(1 for i in range(len(A) - 1) if cmpmat(W[i], W[i + 1]) >= 0)
    R['ns'] = (ns, len(A))
    R['ord'] = ordbad
    print('  非標準 <=%d列 %d 個: %d   順序違反 %d' % (gen, len(A), ns, ordbad))
    if imgc:
        B = sorted(gen3('BMS', imglim, zcap=1), key=key)
        ok, tot, bad = imgclosed_fast(f, B, imgc)
        R['img'] = (ok, tot, len(bad))
        print('  ImgClosedT <=%d列 m<=%d: 逆像あり %d/%d  外れた A %d 個'
              % (imglim, imgc, ok, tot, len(bad)))
    if cof:
        C = sorted(gen3('BMS', cof, zcap=1), key=key)
        c1 = c2 = 0
        for i, M in enumerate(C):
            if len(M) < 2:
                continue
            if i % 2000 == 0:
                core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
            N = f(M)
            E = [tuple(expand(N, m)) for m in range(1, 41)]
            G = [tuple(f(expand(M, np))) for np in range(1, 31)]
            if any(not any(cmpmat(E[m], g) <= 0 for g in G[:24]) for m in range(10)):
                c1 += 1
            if any(not any(cmpmat(g, e) <= 0 for e in E) for g in G[:24]):
                c2 += 1
        R['cof'] = (c1, c2)
        print('  共終性 <=%d列: C1 の破れ %d   C2 の破れ %d' % (cof, c1, c2))
    print('  (%.0fs) %s' % (time.time() - t0, tag))
    return R


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'score'
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    if cmd == 'inj':
        P, H = inj_pairs(b2d3, n)
        print('<=%d列: 単射の破れ %d 組  本当の失敗 %d 件' % (n, len(P), len(H)))
        for M, B, N in P[:20]:
            k, t = tail_shape(M, B)
            print('  もと %-40s' % show(M))
            print('  双子 %-40s 共通 %d 尾 %s' % (show(B), k, show(t)))
            print('  像   %s' % show(N))
    else:
        score(gen=n)


# ---------------------------------------------------------------- 単射（inv3 に頼らない）
def twin(M):
    """双子: `M ++ (1,1,0) ++ M[1:] の写し`（行 0 +1, 行 1 は 0 でなければ +1）。

    単射の破れ 166 組のうち 143 組がちょうどこの形だった（2026-08-27 実測）。
    残り 23 組も「もと ++ アンカー ++ 写し」の変種である。
    """
    return tuple(M) + ((1, 1, 0),) + tuple(
        (a + 1, (b + 1 if b > 0 else 0), c) for a, b, c in M[1:])


def inj_closure(f, lim=6, tlim=6, elim=5, en=6, verbose=3):
    """**逆写像に頼らない**単射の検査。列数をまたぐ相手を自分で作って比べる。

      S1 = gen3(<=lim)                      短いほう
      S2 = {twin(M) : M in gen3(<=tlim)}    長いほう（<=2*tlim 列）
      S3 = {M<n> : M in gen3(<=elim), n<=en} 展開したもの

    S1 ∪ S2 ∪ S3 の像をハッシュに貯めて衝突を数える。
    `inv3.d2b3` は古い conv3 に合わせて作られているので、conv3 を変えると
    往復は当てにならない。この検査は conv3 だけを見る。
    """
    S = set()
    for M in gen3('BMS', lim, zcap=1):
        S.add(tuple(M))
    for M in gen3('BMS', tlim, zcap=1):
        T = twin(M)
        if isstd(T, 'BMS') and all(c[2] <= 1 for c in T):
            S.add(T)
    for M in gen3('BMS', elim, zcap=1):
        for n in range(1, en + 1):
            T = tuple(expand(tuple(M), n))
            if all(c[2] <= 1 for c in T):
                S.add(T)
    core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    seen, col = {}, []
    for i, M in enumerate(sorted(S, key=key)):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        N = tuple(f(list(M)))
        if N in seen:
            col.append((seen[N], M, N))
        else:
            seen[N] = M
    print('  単射（閉包 %d 個）: 衝突 %d 組' % (len(S), len(col)))
    for a, b, N in col[:verbose]:
        print('        %s' % show(a))
        print('        %s' % show(b))
        print('        同じ像 %s' % show(N))
    return len(S), col


# ---------------------------------------------------------------- ImgClosedT（inv3 に頼らない）
def build_dict(f, lim=7, tlim=6, elim=6, en=8):
    """像 -> BMS 標準形 の辞書。`inv3` を使わずに逆像の証人を探すための台。"""
    S = set()
    for M in gen3('BMS', lim, zcap=1):
        S.add(tuple(M))
    for M in gen3('BMS', tlim, zcap=1):
        T = twin(M)
        if isstd(T, 'BMS') and all(c[2] <= 1 for c in T):
            S.add(T)
    for M in gen3('BMS', elim, zcap=1):
        for n in range(1, en + 1):
            T = tuple(expand(tuple(M), n))
            if all(c[2] <= 1 for c in T):
                S.add(T)
    core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    D = {}
    for i, M in enumerate(sorted(S, key=key)):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        D.setdefault(tuple(f(list(M))), M)
    return D


def imgclosed_dict(f, A, D, mmax=3, verbose=0):
    """ImgClosedT を辞書引きで測る（`inv3` に依存しない）。

    `D` は `build_dict` で作った 像 -> BMS 標準形。T = (f A)<m> が `D` に
    あればそれが逆像の**構成的な証拠**。無いのは「この台では見つからない」
    だけなので、破れの**上界**である。v11 と新規則を同じ土俵で比べるための道具。
    """
    ok = tot = 0
    bad = set()
    for i, M in enumerate(A):
        if len(M) < 2:
            continue
        if i % 500 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        N = tuple(f(M))
        for m in range(1, mmax + 1):
            T = tuple(expand(N, m))
            tot += 1
            if T in D:
                ok += 1
            else:
                bad.add(tuple(M))
    print('  ImgClosedT（辞書 %d 個, m<=%d）: 逆像あり %d/%d   外れた A %d 個'
          % (len(D), mmax, ok, tot, len(bad)))
    for M in sorted(bad, key=key)[:verbose]:
        print('        %s -> %s' % (show(M), show(f(M))))
    return ok, tot, bad
