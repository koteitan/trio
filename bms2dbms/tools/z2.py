"""課題 E2: `rule.py` の `depth_rule` の機構を `rows3.conv3` に翻訳する台。

**`newterm` は採用され、`rows3.conv3` に `V12['newterm']` として入った**
（課題 E5, 2026-08-27）。このファイルの `conv3` のコピーは v11 ベースのままで、
`mark`（課題 E1）は入っていない。採点に使うなら `f` に `rows3.b2d3` を渡すこと。

`rule.convert`（旧トランスデューサ）はシート 1622/1622 で、争点 P6 の正しい
綴り `...(6,2,1)(6,2,0)(7,3,1)` も出す。ただし丸ごと使うと z=0 の断片で
2 行版 `rows2.convC` と 35 件食い違う。そこで**分岐列 (a,1,0) の浅い／深いを
決める部分だけ**を `conv3` に持ってきて、1 条項ずつ 7 つの土俵で採点した。

このファイルは `rows3.conv3`（v11）の**コピー**で、`FLAGS` で条項を入れ切り
できる。`install()` で `rows3` 側の名前を差し替えるので、`sheet3` / `inv3` /
`rows3.check` はそのまま自分の版を採点してくれる。`rows3.py` は読むだけ。

    python3 z2.py census [lim] [条項...]   rule の深さビットと突き合わせて分類
    python3 z2.py score  [lim] [条項...]   7 つの土俵で採点（条項名を並べる。
                                          `v11` だけ書くと素の v11）
    python3 z2.py p6                       争点 P6 の像

== 結論（2026-08-27, 測定ずみ）==

**採用したのは `newterm` 1 つだけ**（既定で on）。

    newterm  行 0 が 0 の柱 (0,0,0) は新しい加算項の頭なので、段の状態
             `st['prev']` を持ち越さない（None に戻す）。
             持ち越すと A ++ A の 2 つ目の写しが浅く綴られ、f が和について
             加法的でなくなる。

    | 土俵 | v11 | +newterm |
    |---|---|---|
    | シート 3 行 z<=1 (1358 対) | 1354 | **1354** |
    | z=0 <=9 列 295014 個 vs `rows2.convC` | 0 | **0** |
    | 生成 <=7 列 77282 個で v11 と像が違う | - | **0**（非標準 3・衝突 0 も同じ） |
    | `d2b3` 往復 <=7 列（単射の破れ） | 166 | **166** |
    | 非標準 / 順序違反（<=6 列） | 0 / 0 | 0 / 0 |
    | 共終性 C1 の破れ <=5 / <=6 / <=7 列 | 7 / 121 / 1572 | **5 / 88 / 1167** |
    | 共終性 C2 の破れ <=6 / <=7 列 | 0 / 2 | 0 / 2 |
    | ImgClosedT の破れ A <=5 / <=6 / <=7 列 | 28 / 327 / 3779 | **26 / 294 / 3374** |
    | 生成 <=8 列 781605 個: 像の差 / 非標準 / 像の衝突 | - | **50 / 84 / 0** |

（`FLAGS` を全部切ると `rows3.b2d3` と <=7 列 77282 個で食い違い 0。
コピーは忠実である。<=8 列の非標準 84 は v10/v11 と同数。
ImgClosedT <=5 列は対で 3000/3051（v11 は 2996/3051）。`m_imgclosed` の
梯子つき探索（`LADDER_SCAN`）に降ろしても 26 個のまま。ただし 26 個中 25 個は
打ち切りが付いたので、探索不足の疑いは残る。）

破れ集合は真部分集合（<=6 列で C1 33 個・ImgClosedT 33 個、<=7 列で
それぞれ 405 個が直り、**新しく壊れたものは 0**）。
**生成 <=7 列では像が 1 ビットも変わらない**ので、シート・単射・順序・z=0 は
定義から動かない。v11 を採ったときと同じ形の
「片側にしか動かない」変更である。

**単射の破れ（<=7 列 166 件）はこの課題の道具では動かない。** NOTES は
「分岐列の浅い／深いのビット」が原因としているが、実測では原因は**縮約**である:

    もと (0,0,0)(1,1,1)(2,1,0)(3,2,1)(3,0,0)(2,1,0)                     6 列
    双子 上 ++ (1,1,0)(2,2,1)(3,2,0)(4,3,1)(4,0,0)(3,2,0)             12 列

双子の後半 6 列に分岐列 (a,1,0) は **1 本も無い**（(1,1,0) はアンカー、
(3,2,0) は行 1 が 2）。`b2d3n` の縮約回数は もと 0 / 双子 1 で、双子は
写しをまるごと吸って もと と同じ像になる。`rule.convert` は縮約しないので
双子を 14 列の別の像に写して分離できている。**担当は残余なしの縮約
（rest2 が空・e=1・deep_end）のガードであって、`depth_rule` ではない。**

== 採らなかった条項と、その理由（全部これも測定ずみ）==

  onx       主判定の `closes_unit` を `rule` と同じ「もとの行列の次の列」
            `Mo[off+1]` で見る（いまはブロック分割の `nxt`）。
            **シート 1354 -> 1250。却下。**
  aw_none   `after_w` を `prev is None` でも効かせる（`rule.at_unit_edge`）。
            **<=5 列で C1 7 -> 10、ImgClosedT 28 -> 31。却下。**
  endprev   行列の末尾でも直前の分岐列が深ければ段を落とさない。
            **シート 1354 -> 1221。却下。**
  rule_order / cs_aw / prev_all / anchor
            `<=7` 列で像が 1 ビットも変わらない。`anchor`（= v10 のアンカー
            リセット）は `sibL` と組むと <=5 列で C2 を 1 件壊す。
  anchor_mo アンカー (1,1,0) を「前の分岐列から今まで」もとの行列で探して
            `prev` を 0 に戻す（`rule.depths` の忠実な翻訳。素の
            `p == ANCHOR` では縮約が飛ばしたアンカーを取りこぼす）。
            **単独では <=7 列で像が変わらない**。`sibL` の暴発止めとしてだけ
            意味がある。
  sibL      **争点 P6 が直る条項**。行 1 の影を書いたら、その「深い側」を
            **あとの兄弟**にも渡す（段の表の第 5 要素。分岐列だけが使う）。
            P6 の像が `rule.convert` と一致するようになる。
            <=6 列で C1 121 -> 83（49 直り・11 新しく壊れる）、
            ImgClosedT 327 -> 295（49 直り・17 新しく壊れる）。
            **両側に動くので不採用。**
  sibend / sibdeep
            `sibL` の深い側が生きているときはユニットを閉じる合図でも段を
            落とさない（末尾だけ / 全部）。P6 の 1 列短い接頭辞
            `(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)` も深く綴れるようになるが、
            <=6 列で C1 100（49 直り・28 壊れ）・ImgClosedT 309（49・31）。
            **深い綴りは 1 列短い相手へ次々に伝染し、境目がいつまでも残る。**

== rule の深さビットとの突き合わせ（`census`）==

`rule.depths` は分岐列で `prev` が一度 0 になると 0 に貼りつく（アンカーでも
0 に戻す）ので、**素の規則は浅い側に偏っている**。`rule.R23` はそれを
「像が DBMS 標準形にならなければ 1〜3 箇所ひっくり返す」で後始末している。
だから `rule.depths` は正解表ではない。実測（<=6 列, 分岐列 5130 本、
`R23` のひっくり返しまで入れた最終ビットと比較）:

    v11              一致 4230 / 食い違い 894（全部 rule=0 conv=1）
    anchor_mo など   一致 4877 / 食い違い 247

食い違いは**すべて「conv3 のほうが深い」**。7 つの土俵はどれも conv3 の
深い側を支持した（`onx` / `aw_none` / `endprev` はどれも成績を落とす）。
つまり **`depth_rule` の判定部分を忠実に移植しても良くならない**。
"""
from __future__ import annotations
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import parse, show, isstd, cmpmat, expand, pim, rows
import rows3
from rows3 import (gen3, key, split0, units_split, ok_place, fit, closes_unit,
                   par0, hi_block, is_repeat, is_w_col, closes_hi_unit,
                   Lat, padL, is_branch, dmap_at, NOTLAST, ANCHOR, pad, two)
import rule

# 既定 = 採用した条項だけ on（= v11 ＋ newterm）。`v11` を渡すと全部 off。
FLAGS = dict(onx=False, aw_none=False, rule_order=False, prev_all=False,
             cs_aw=False, anchor=False, anchor_mo=False, sibL=False,
             sibLu=False, newterm=True, endprev=False, sibend=False,
             sibdeep=False)


def reset(*names):
    """条項を全部切ってから `names` だけ入れる。`v11` は「全部切る」の別名。"""
    for k in FLAGS:
        FLAGS[k] = False
    for k in names:
        if k != 'v11':
            setf(**{k: True})

TRACE = None        # None でなければ {もとの列の添字: 深さビット} を貯める


def setf(**kw):
    for k, v in kw.items():
        if k not in FLAGS:
            raise KeyError(k)
        FLAGS[k] = v


def flagstr():
    on = [k for k, v in FLAGS.items() if v]
    return '+'.join(on) if on else 'v11'


ADOPTED = ('newterm',)      # 7 つの土俵で片側にしか動かなかった条項


# ---------------------------------------------------------------- 深さの判定
def decide(p, nxtb, prev, off, Mo, sib=False):
    """分岐列 `p`（もとの添字 `off`）が浅いか。True = 浅い（段 1）。

    `rule.depth_rule` の翻訳。`prev` は直前の分岐列の選択（None / 0 / 1）。
    """
    onx = Mo[off + 1] if off + 1 < len(Mo) else None
    nxt_cu = onx if FLAGS['onx'] else nxtb
    pv = Mo[off - 1] if off >= 1 else None
    pv2 = Mo[off - 2] if off >= 2 else None
    hi = hi_block(Mo, off)
    if prev == 0:
        return True
    # after_w: 直前が「x w」の柱 (k,0,0) でユニットの端なら段は落ちる。
    # W_(w^2) 系（hi）で直前の x w が根から生えていないときだけ段が残る。
    edge = closes_unit(onx) or (prev is None and FLAGS['aw_none'])
    aw = None
    if is_w_col(pv) and edge and (prev == 1 or FLAGS['aw_none']):
        pnt = off > 0 and par0(Mo, off - 1) == 0
        aw = (prev == 1) and hi and not pnt          # True = 深い
    if aw is not None and FLAGS['rule_order']:
        return not aw
    shallow = closes_unit(nxt_cu)
    # sibend / sibdeep: 深い側が「直前の兄弟が書いた行 1 の影」（`sibL` の
    # 第 5 要素）のときは、ユニットを閉じる合図でも段を落とさない。
    # sibend は**行列の末尾だけ**、sibdeep は閉じる合図ぜんぶに効かせる。
    if sib and shallow and (FLAGS['sibdeep']
                            or (FLAGS['sibend'] and nxt_cu is None)):
        shallow = False
    # endprev: 行列の**真の末尾**でも、直前の分岐列が深ければ段は落ちない。
    # ImgClosedT の破れ「目標の末尾 1 列の行 1 が 1 だけ届かない」がこれ。
    if FLAGS['endprev'] and nxt_cu is None and prev == 1:
        shallow = False
    if aw is not None:
        shallow = not aw
    if closes_hi_unit(p, onx, pv, pv2, hi, is_repeat(Mo, off)):
        shallow = True
    return shallow


# ---------------------------------------------------------------- 写しの状態機械
def copy_shift(block, e, ps0, prev0, nxt_after, st=None, off0=None):
    """`rows3.copy_shift` のコピー。`cs_aw` で `decide` を使う。"""
    out, prev = [], prev0
    Mo = st['Mo'] if st is not None else None
    for i, c in enumerate(block):
        nxt = block[i + 1] if i + 1 < len(block) else nxt_after
        if c == ANCHOR and FLAGS['anchor']:
            prev = 0
        if is_branch(c):
            if FLAGS['cs_aw'] and Mo is not None and off0 is not None:
                shallow = decide(c, nxt, prev, off0 + i, Mo)
            else:
                shallow = (prev == 0) or closes_unit(nxt)
            prev = 0 if shallow else 1
            dl = 0 if shallow else (e if c[1] > ps0 else 0)
        else:
            dl = e if c[1] > ps0 else 0
        out.append((c[0] + 1, c[1] + dl, c[2]))
    return out


def contrPre(p, U, A, e, ps0, prev0, nxt_after, st=None, off0=None):
    return copy_shift([p] + list(A) + list(U), e, ps0, prev0, nxt_after,
                      st, off0)


# ---------------------------------------------------------------- conv3 のコピー
def conv3(M, d=0, L=(), F=(), ps=(0, 0), pw=(0, 0), first=True, force=False,
          st=None, nx=None, off=0):
    """`rows3.conv3`（v11）のコピー。判定だけ `decide` に出してある。"""
    if st is None:
        st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0}
    if not M:
        return []
    p, r = M[0], M[1:]
    v, s2 = p[1], p[2]
    A, B = split0(p, r)
    oA, oB = off + 1, off + 1 + len(A)

    if v == 0:
        base_d = base_s = base_sd = 0
        pl2, force1 = 0, False
    else:
        e = Lat(L, v - 1)
        base_d, pl2, force1, base_s = e[0] + 1, e[1], e[2], e[3] + 1
        # 段の表の第 5 要素は「**分岐列だけ**が使える深い側」。無ければ深い側と同じ。
        # `sibL` はここにだけ書き込むので、分岐列でない柱の綴りは変わらない。
        base_sd = (e[4] if len(e) > 4 else e[0]) + 1
    first1 = F[v] if v < len(F) else True

    if p == ANCHOR and FLAGS['anchor']:
        st['prev'] = 0
    # newterm: 行 0 が 0 の柱 (0,0,0) は**新しい加算項**の頭。ユニットが
    # 変わるのだから、直前の分岐列の選択は次の項に持ち越さない。
    # 持ち越すと、A ++ A の 2 つ目の写しで段が浅く綴られる（ImgClosedT の破れ）。
    if FLAGS['newterm'] and p[0] == 0:
        st['prev'] = None
        st['lastbr'] = off
    if is_branch(p) and (base_s != base_sd or FLAGS['prev_all']):
        nxt = M[1] if len(M) > 1 else nx
        prev = st['prev']
        # anchor_mo: `rule.depths` はアンカー (1,1,0) を通るたび prev を 0 に
        # 戻す。`conv3` は縮約でアンカーを**飛ばす**ことがある（写しの頭に
        # なると `p` として訪れない）ので、素の `p == ANCHOR` では取りこぼす。
        # もとの行列 Mo を「前の分岐列から今まで」見て、アンカーがあれば戻す。
        if FLAGS['anchor_mo']:
            lb = st.get('lastbr', -1)
            if any(tuple(st['Mo'][j]) == ANCHOR for j in range(lb + 1, off)):
                prev = 0
        st['lastbr'] = off
        shallow = decide(p, nxt, prev, off, st['Mo'], base_sd != base_d)
        if TRACE is not None:
            TRACE[off] = (0 if shallow else 1, base_s != base_sd)
        base = base_s if shallow else base_sd
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
    st['dmap'] = st['dmap'][:p[0]] + [dd]

    fc = (not lad1) and first1 and s2 == pl2
    f0 = (not lad0) and first and (v, s2) == ps
    if e1 == base + 1 and v >= 1:
        Lb = padL(L, v - 1) + ((base, pl2, False, Lat(L, v - 1)[3]),)
    else:
        Lb = L
    LA = padL(Lb, v) + ((e1, s2, fc, e1),)
    if FLAGS['sibL']:
        # 「兄弟だけの深い側」（第 5 要素）は**子には渡さない**。
        # 渡すとアンカー (1,1,0) を素通りして次のユニットの分岐列まで届く
        # （<=6 列で 67 件が rule と食い違う。うち 1 件も rule 側が正しい）。
        LA = tuple(t[:4] for t in LA)
    FA = F[:v] + (False,)
    # sibL: 行 1 の影を書いたら、**あとの兄弟**にも「深い側」を渡す。
    # いまは Lb（深い側 = 影の値）を子 `A` にしか渡していないので、
    # 兄弟の分岐列は深く綴る選択肢を持てない（争点 P6 がこれ）。
    # 深い側だけ差し替え、浅い側と v 以上の段はそのまま残す。
    if FLAGS['sibL'] and Lb is not L:
        eo = Lat(L, v - 1)
        LS = (padL(L, v - 1) + ((eo[0], eo[1], eo[2], eo[3], base),)
              + tuple(L[v:]))
    else:
        LS = L

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
            for na in (q, NOTLAST):
                pre = contrPre(p, U, A, e, ps[0], st['prev'], na, st, off)
                if list(Aq[:len(pre)]) == pre:
                    break
            else:
                continue
            blk = [p] + list(A) + list(U)
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
            Lr = padL(L, v) + (((base, pl2, fc, base) if e else (e1, s2, fc, e1)),)
            hd = lambda *ls: next((l[0] for l in ls if l), nx)
            cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
                       U[0] if U else na, oA)
            cU = conv3(U, d + 1, LS if FLAGS['sibLu'] else L, FA, (v, s2),
                       (e1, e2), False, False, st, na, oU)
            rd = (d + 1 + e if (not rest2 or rest2[0][0] == p[0] + 1)
                  else dmap_at(st, rest2[0][0] - 1))
            cR = conv_resid(rest2, rd, Lr, (v, s2), (e1, e2), st, hd(Bq), oR)
            cB = conv3(Bq, d, LS if FLAGS['sibLu'] else L, FA, (v, s2),
                       (e1, e2), False, False, st, nx, oBq)
            st['nc'] = st.get('nc', 0) + 1
            return cols + cA + cU + cR + cB

    cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
               B[0] if B else nx, oA)
    cB = conv3(B, d, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)
    return cols + cA + cB


def conv_resid(rest, rd, Lr, ps, pw, st, nx, off):
    """`rows3.conv_resid` のコピー。"""
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
        rd = max(0, rd - (m0 - tail[0][0]))
        off += i
        rest = tail
    return out


def b2d3n(M):
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0}
    return tuple(conv3(list(M), st=st)), st['nc']


def b2d3(M):
    return b2d3n(M)[0]


def bits(M):
    """`b2d3` を回して、分岐列に与えた深さビットを {添字: 0/1} で返す。"""
    global TRACE
    TRACE = {}
    try:
        img = b2d3(M)
        return dict(TRACE), img
    finally:
        TRACE = None


def install():
    """`rows3` 側の名前を自分の版に差し替える（`sheet3` / `inv3` 経由の採点用）。"""
    rows3.conv3 = conv3
    rows3.conv_resid = conv_resid
    rows3.copy_shift = copy_shift
    rows3.contrPre = contrPre


# ---------------------------------------------------------------- rule 側の深さ
def rule_final_depths(m):
    """`rule.R23` が最後に採った深さビット（ひっくり返しの後）。

    `rule.depths` は素の規則で、`R23` は像が DBMS 標準形にならないときだけ
    1〜3 箇所ひっくり返して探し直す。**シート 1622/1622 なのは後者**なので、
    突き合わせの正解表はこちら。返り値 (ビット列, ひっくり返した箇所の数)。
    """
    import itertools as _it
    from rule import (depths, dedup, _stair, _try, convert, is_branching)
    Y = rows(m)
    ds = depths(m)
    Z = dedup(_stair(m, Y, lambda x, c: ds[x]))
    if isstd(Z, 'DBMS'):
        return list(ds), 0
    lo = None
    if len(m) > 1 and isstd(m[:-1], 'BMS'):
        try:
            lo = convert(m[:-1], Y)
        except Exception:
            lo = None

    def okay(W):
        return isstd(W, 'DBMS') and (lo is None or cmpmat(lo, W) < 0)

    br = [x for x, c in enumerate(m) if is_branching(c)]
    for k in (1, 2, 3):
        cands = []
        for f in _it.combinations(br, k):
            W = _try(m, Y, ds, f)
            if W is not None and okay(W):
                cands.append((W, f))
        if cands:
            best = cands[0]
            for W in cands[1:]:
                if cmpmat(W[0], best[0]) < 0:
                    best = W
            e = list(ds)
            for i in best[1]:
                e[i] ^= 1
            return e, k
    return list(ds), -1


def census(lim=6, show_n=4):
    """rule の深さビットと `conv3` のビットを同じ行列で突き合わせて分類する。"""
    t0 = time.time()
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    print('BMS 3 行 z<2 標準形 (<=%d 列): %d   条項 %s' % (lim, len(A), flagstr()))
    from rule import is_branching
    cnt = {}
    ex = {}
    nm = 0
    for i, M in enumerate(A):
        if i % 500 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        T, img = bits(M)
        rd, k = rule_final_depths(list(M))
        raw = rule.depths(list(M))
        for x, c in enumerate(M):
            if not is_branching(c):
                continue
            if x not in T:
                key_ = ('未訪問（縮約で飛ばした）', rd[x])
            else:
                b, ch = T[x]
                if b == rd[x]:
                    key_ = ('一致', b)
                else:
                    key_ = ('食い違い rule=%d conv=%d %s' %
                            (rd[x], b, '選べる' if ch else '選べない'), 0)
            cnt[key_] = cnt.get(key_, 0) + 1
            if key_[0] != '一致':
                ex.setdefault(key_, []).append((M, x, rd[x], raw[x], k))
        nm += 1
    print('  分岐列の総数 %d' % sum(cnt.values()))
    for k_ in sorted(cnt, key=lambda t: -cnt[t]):
        print('    %-46s %d' % ('%s%s' % (k_[0], ' (深さ%d)' % k_[1]
                                          if k_[0] != '一致' else ' =%d' % k_[1]),
                                cnt[k_]))
    for k_ in sorted(ex, key=lambda t: -cnt[t]):
        print('  例 %s' % k_[0])
        for M, x, r, raw_, kk in ex[k_][:show_n]:
            print('    %-40s 列%d %s  rule=%d(素%d,flip%d)'
                  % (show(M), x, show([M[x]]), r, raw_, kk))
    print('  (%.1fs)' % (time.time() - t0))
    return cnt




# ---------------------------------------------------------------- 採点
def score(lim=5, imgc=3, sheet=True, verbose=0):
    """7 つの土俵で採点する。`install()` してから `rows3.check` に渡す。"""
    t0 = time.time()
    install()
    import inv3, sheet3
    print('=== 条項 %s ===' % flagstr())
    if sheet:
        sheet3.score(b2d3, 0)
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    print('BMS 3 行 z<2 標準形 (<=%d 列): %d' % (lim, len(A)))
    n = rows3.check(b2d3, A, verbose=verbose, imgc=imgc)
    print('合計違反 %d  (%.1fs)' % (n, time.time() - t0))
    return n


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'census'
    arg = int(sys.argv[2]) if len(sys.argv) > 2 else None
    if cmd == 'census':
        if sys.argv[3:]:
            reset(*sys.argv[3:])
        setf(prev_all=True)
        census(arg or 6)
    elif cmd == 'score':
        if sys.argv[3:]:
            reset(*sys.argv[3:])
        score(arg or 5)
    elif cmd == 'p6':
        M = parse('(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)', 3)
        P = parse('(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)', 3)
        print('  rule.convert    %s' % show(rule.convert(M)))
        for fl in (('v11',), ADOPTED, ADOPTED + ('anchor_mo', 'sibL'),
                   ADOPTED + ('anchor_mo', 'sibL', 'sibend')):
            reset(*fl)
            print('  %-30s %s' % (flagstr(), show(b2d3(M))))
        print('  1 列短い接頭辞 %s' % show(P))
        for fl in (('v11',), ADOPTED + ('anchor_mo', 'sibL'),
                   ADOPTED + ('anchor_mo', 'sibL', 'sibend')):
            reset(*fl)
            print('  %-30s %s' % (flagstr(), show(b2d3(P))))
        print('  rule.convert                   %s' % show(rule.convert(P)))
