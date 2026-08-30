"""課題 F1: `sibL` の伝染を止める条件を探す台（2026-08-27）。

**採用ずみ**: ここで決めた `sibL` ＋ `sib_anchbefore` は課題 F5 で
`rows3.conv3` に入った（旗 `rows3.V13['sibL'] / ['sib_anchbefore']`）。
このファイルは条項を 1 つずつ入れ切りして比べるための台として残す
（`install()` を呼ぶと `rows3` 側がこのファイルの v12 ベースのコピーに
差し替わるので、`rows3.V13` は効かなくなる）。

`rows3.conv3`（**v12** = mark ＋ newterm）の**コピー**に、`z2.py` の `sibL`
（行 1 の影を立てた柱の「深い側」を子だけでなく**あとの兄弟**にも渡す）を
移植したもの。`FLAGS` で条項を入れ切りできる。

    python3 w1.py base [lim]        旗を v12 にしたコピーが `rows3.b2d3` と一致するか
    python3 w1.py quick 条項...     主指標だけ（ImgClosedT <=5/<=6, z=0 対照, C1 <=6）
    python3 w1.py score [lim] 条項...  `rows3.check` の 7 つの土俵
    python3 w1.py table [lim] 条項...  像が変わる行列と、深い側を使った柱の文脈
    python3 w1.py p6                争点 P6 とその 1 列短い接頭辞 P5

== 分かったこと ==

**1. `z2.py` の `sibL` には門（どの柱が「浅い／深いを選べる」か）のバグがある。**
`z2` は `is_branch(p) and base_s != base_sd` で門を開き、閉じたときは
`base = base_d` を採る。すると `base_s == base_sd != base_d` の柱で
**v12 にはあった深い側の選択肢が消える**。ここでは門を

    深い側の候補 deep = 兄弟から渡ってきた base_sd（使ってよければ）/ さもなくば base_d
    選べる <=> base_s != deep,   選べないなら base = deep

とした（旗を全部切ると v12 に戻り、<=6 列 8387 個で `rows3.b2d3` と食い違い 0）。
この門で測ると、`sibL` が像を変えるのは <=7 列 77282 個のうち **213 個**だけ
（6 列 8 / 7 列 205）。

**2. 伝染の正体は「その柱より前にアンカー (1,1,0) を通ったか」だった。**
争点 P6 の柱と、壊れる柱は**局所の文脈が完全に同じ**（どちらも
`(a,1,1)(a,1,0)` の隣り合う兄弟・prev=None・末尾でない・after_w も
closes_hi_unit も不発）。区別は行列の**前方**にしかない:

    <=7 列で `sibL` が像を変える 213 個を `rule.convert`（シート 1622/1622）と
    突き合わせた表

    | 柱より前のアンカー | rule が支持する側 | 個数 |
    |---|---|---|
    | あり | **v12**（浅い）  |   4 |
    | なし | **sibL**（深い） | 190 |
    | なし | v12（浅い）      |   8 |
    | なし | どちらでもない   |  11 |

「あり」の 4 個は全部 (0,0,0)(1,1,1)**(1,1,0)**(2,0,0)(3,1,1)(3,1,0)X で、
素の `sibL` が新しく作る DBMS 非標準の像 4 個とちょうど同じ。
「なし」で rule が v12 を支持する 8 個は全部
(0,0,0)(1,1,1)(2,0,0)(3,1,1)**(4,0,0)**(3,1,0)X ＝ 影の柱と分岐列の間に
柱が 1 本挟まる（gap=2）ものだった。

**3. 条項 `sib_anchbefore`**（採用候補）

    兄弟から渡ってきた深い側は、**その柱より前にアンカー (1,1,0) が
    1 本も無いとき**にしか使えない。

Lean 向けの読み: アンカーは行 1 の新しい加算ユニットの頭なので、
「行 1 の最初のユニットの中でだけ、影の深さは兄弟に効く」。
`st['Mo']` と `off` はすでに持ち回っているので `∃ j < off, Mo[j] = (1,1,0)`
で書ける（`after_w` / `closes_hi_unit` と同じ形）。

同じ点数になる書き方が 3 つある（`sib_anchsrc` = 影の柱より前、
`sib_anchnone` = 行列のどこにも、`sib_anchbefore` = この柱より前）。
`sib_adj`（gap==1 だけ）を足すと ImgClosedT が 285 -> 286 に**悪化**した。

== 測った点数（すべて conv3 v12 を基準に）==

| 条項 | ImgClosedT <=5 | <=6 | z=0 対照 | 共終性 C1 <=6 | 辞書引き <=6 |
|---|---|---|---|---|---|
| v12（基準） | 26 | 294 | 0 | 88 | 584 |
| +sibL（素） | 46 | 472 | 0 | 68 | 762 |
| +sibL+anchor_mo | 28 | 339 | 0 | 88 | - |
| anchor_mo だけ | 26 | 311 | 0 | 105 | - |
| **+sibL+sib_anchbefore** | **25** | **285** | **0** | **73** | **575** |
| +sibL+sib_anchsrc | 25 | 285 | 0 | 73 | - |
| +sibL+sib_anchnone | 25 | 285 | 0 | 73 | - |
| +sibL+sib_anchbefore+sib_adj | 25 | 286 | 0 | 75 | - |
| +sibL+sib_anchbefore+sib_notail | 25 | 285 | 0 | 73 | - |（`sib_notail` は無効）

辞書引き（`z1.build_dict` の 127182 個。逆写像 `inv3` に依存しない）が
`imgfast` の段 1 と同じ結論を出したので、**この差は `d2b3` の古さではない**。

**`sibend` / `sibdeep` は却下**（`sib_anchbefore` と組んでも）:
    +sibend   img5 26 / img6 300 / C1 91
    +sibdeep  img5 26 / img6 296 / C1 90
どちらも `sib_anchbefore` 単独（25 / 285 / 73）より悪い。

== 残りの土俵（`sib_anchbefore`）==

| 土俵 | v12 | +sibL+sib_anchbefore |
|---|---|---|
| シート 3 行 z<=1（満点 1354） | 1354 | **1354** |
| 生成 <=7 列 77282 個: 非標準 | 3 | **0** |
| 生成 <=7 列: 順序違反 / 像の衝突 / z=0 食い違い | 0 / 0 / 0 | **0 / 0 / 0** |
| 列数をまたいだ単射（閉包 15611 個） | 衝突 0 組 | **衝突 0 組** |
| 共終性 C2 の破れ（<=6 列） | 0 | **0** |

v12 の <=7 列の非標準 3 個は**全部 P6 一族**
(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)X で、`sib_anchbefore` はこれを
0 にする。素の `sibL` は逆に 4 個（アンカー付きの一族）を作る。

`sib_anchbefore` の内訳: ImgClosedT <=6 は直る 16 / 新しく壊れる 7、
C1 <=6 は直る 16 / 壊れる 1。**新しく壊れる 7 個は争点 P6 の一族**
（(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)X）で、外れる目標はどれも同じ 1 本

    T = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,0,0)(5,1,0)(6,2,1)(6,2,0)

＝「1 列短い接頭辞 P5 を深く綴ったもの」。`sibend`（兄弟の深い側が
生きているなら**行列の末尾**でも段を落とさない）を足すと P5 がこれを
綴るようになる（`python3 w1.py p6` で見える）。ただし P5 は
`rule.convert` では浅い側なので、シートと衝突しうる。

**採点は片側だけではない。** シート 1354/1358（v12 と同じ）、
z=0 の対照 0、<=6 列の非標準 / 順序 / 衝突 / z=0 一致はどれも v12 と同じ。
"""
from __future__ import annotations
import sys, os, time, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import parse, show, isstd, cmpmat, expand, rows
import rows3
from rows3 import (gen3, key, split0, units_split, ok_place, fit, closes_unit,
                   par0, hi_block, is_repeat, is_w_col, closes_hi_unit,
                   Lat, padL, is_branch, dmap_at, NOTLAST, ANCHOR, pad, two)

# 既定 = v12（mark ＋ newterm）。`sibL` 系は全部 off。
FLAGS = dict(mark=True, newterm=True,
             sibL=False,          # 深い側を兄弟に渡す
             sibLu=False,         # 縮約の写し `U` / `Bq` にも渡す
             # --- 伝染を止める候補の条件（`sibL` が on のときだけ効く）---
             sib_notail=False,    # 行列の**末尾の柱**では兄弟の深い側を使わない
             sib_sameunit=False,  # 影を書いた柱と同じ加算ユニットの中だけ
             sib_adj=False,       # 影を書いた柱の直後の分岐列だけ
             sib_prev1=False,     # 直前の分岐列が深い (prev==1) ときだけ
             sib_prevn=False,     # 直前の分岐列が無い (prev is None) ときだけ
             sib_nz2=False,       # 影を書いた柱が行 2 を使っていない (s2==0)
             sib_z2=False,        # 影を書いた柱が行 2 を使った (s2>0)
             sib_noanchor=False,  # 影の柱と今の柱の間にアンカー (1,1,0) が無いときだけ
             sib_anchbefore=False,# この柱より前にアンカー (1,1,0) が 1 本も無いときだけ
             sib_anchsrc=False,   # 影を書いた柱より前にアンカーが無いときだけ
             sib_anchnone=False,  # 行列のどこにもアンカーが無いときだけ
             sibend=False,        # 兄弟の深い側が生きているなら**行列の末尾**でも段を落とさない
             sibdeep=False,       # 同上。ユニットを閉じる合図ぜんぶに効かせる
             anchor_mo=False,     # アンカーを通ったら prev を 0 に戻す（z2 の暴発止め）
             )

TRACE = None        # None でなければ {もとの添字: 記録} を貯める


def reset(*names):
    for k in FLAGS:
        FLAGS[k] = False
    for k in names:
        if k == 'v12':
            FLAGS['mark'] = FLAGS['newterm'] = True
        elif k != 'v11':
            setf(**{k: True})


def setf(**kw):
    for k, v in kw.items():
        if k not in FLAGS:
            raise KeyError(k)
        FLAGS[k] = v


def flagstr():
    on = [k for k, v in FLAGS.items() if v]
    return '+'.join(on) if on else 'v11'


def _snap(st):
    return (st['ST'], st['prev'], list(st['dmap']), st.get('nc', 0))


def _restore(st, s):
    st['ST'], st['prev'], st['dmap'], st['nc'] = s[0], s[1], list(s[2]), s[3]


def leaves_mark_local(A, U, dd, d, LA, L, FA, v, s2, e1, e2, st, na, oA, oU,
                      ob):
    """`rows3.leaves_mark_local` のコピー。"""
    s0 = _snap(st)
    rec0 = dict(st['rec'])
    conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
          U[0] if U else na, oA)
    conv3(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na, oU)
    prev_in = st['rec'].get(ob, 'none')
    _restore(st, s0)
    st['rec'] = rec0
    if prev_in == 0 or prev_in == 'tie' or prev_in == 'none':
        return False
    Mo = st['Mo']
    c = Mo[ob]
    pv = Mo[ob - 1] if ob >= 1 else None
    pv2 = Mo[ob - 2] if ob >= 2 else None
    onx = Mo[ob + 1] if ob + 1 < len(Mo) else None
    if prev_in == 1 and is_w_col(pv) and closes_unit(onx):
        return False
    if closes_hi_unit(c, onx, pv, pv2, hi_block(Mo, ob), is_repeat(Mo, ob)):
        return False
    return True


def unit_start(Mo, off):
    """`off` を含む加算ユニットの頭（行 0 が 0 の直近の柱）のもとの添字。"""
    for j in range(off, -1, -1):
        if Mo[j][0] == 0:
            return j
    return 0


def sib_ok(off, src, prev, st, nxt_cu):
    """兄弟から渡された深い側 `base_sd` を**使ってよいか**（伝染止め）。

    `src` は深い側を書いた柱のもとの添字（分からなければ None）。
    """
    Mo = st['Mo']
    if FLAGS['sib_notail'] and off == len(Mo) - 1:
        return False
    if FLAGS['sib_sameunit'] and src is not None:
        if unit_start(Mo, off) != unit_start(Mo, src):
            return False
    if FLAGS['sib_adj'] and src is not None and off != src + 1:
        return False
    if FLAGS['sib_prev1'] and prev != 1:
        return False
    if FLAGS['sib_prevn'] and prev is not None:
        return False
    if FLAGS['sib_nz2'] and src is not None and Mo[src][2] != 0:
        return False
    if FLAGS['sib_z2'] and src is not None and Mo[src][2] == 0:
        return False
    if FLAGS['sib_noanchor'] and src is not None:
        if any(tuple(Mo[j]) == ANCHOR for j in range(src + 1, off + 1)):
            return False
    if FLAGS['sib_anchbefore']:
        if any(tuple(Mo[j]) == ANCHOR for j in range(0, off)):
            return False
    if FLAGS['sib_anchsrc'] and src is not None:
        if any(tuple(Mo[j]) == ANCHOR for j in range(0, src)):
            return False
    if FLAGS['sib_anchnone']:
        if any(tuple(c) == ANCHOR for c in Mo):
            return False
    return True


# ---------------------------------------------------------------- 写しの状態機械
def copy_shift(block, e, ps0, prev0, nxt_after):
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


# ---------------------------------------------------------------- conv3 のコピー
def conv3(M, d=0, L=(), F=(), ps=(0, 0), pw=(0, 0), first=True, force=False,
          st=None, nx=None, off=0):
    """`rows3.conv3`（v12）のコピー ＋ `sibL`。"""
    if st is None:
        st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0,
              'rec': {}}
    if not M:
        return []
    p, r = M[0], M[1:]
    v, s2 = p[1], p[2]
    A, B = split0(p, r)
    oA, oB = off + 1, off + 1 + len(A)

    src = None
    if v == 0:
        base_d = base_s = base_sd = 0
        pl2, force1 = 0, False
    else:
        e = Lat(L, v - 1)
        base_d, pl2, force1, base_s = e[0] + 1, e[1], e[2], e[3] + 1
        # 第 5 要素 = 兄弟だけが使える深い側。無ければ深い側と同じ。
        base_sd = (e[4] if len(e) > 4 else e[0]) + 1
        src = e[5] if len(e) > 5 else None

    first1 = F[v] if v < len(F) else True

    if FLAGS['newterm'] and p[0] == 0:
        st['prev'] = None

    if is_branch(p):
        nxt = M[1] if len(M) > 1 else nx
        prev0 = st['prev']
        # anchor_mo（`z2.py`）: `rule.depths` はアンカー (1,1,0) を通るたび
        # prev を 0 に戻す。`conv3` は縮約でアンカーを飛ばすことがあるので、
        # もとの行列を「前の分岐列から今まで」見て、アンカーがあれば戻す。
        if FLAGS['anchor_mo']:
            lb = st.get('lastbr', -1)
            if any(tuple(st['Mo'][j]) == ANCHOR for j in range(lb + 1, off)):
                prev0 = 0
        st['lastbr'] = off
        # 深い側の候補: 兄弟から渡ってきた側 `base_sd` を使ってよければそれ。
        deep, usesib = base_d, False
        if FLAGS['sibL'] and base_sd != base_d and sib_ok(off, src, prev0, st,
                                                          nxt):
            deep, usesib = base_sd, True
        if base_s != deep:
            st['rec'][off] = prev0
            shallow = (prev0 == 0) or closes_unit(nxt)
            Mo = st['Mo']
            pv = Mo[off - 1] if off >= 1 else None
            pv2 = Mo[off - 2] if off >= 2 else None
            onx = Mo[off + 1] if off + 1 < len(Mo) else None
            hi = hi_block(Mo, off)
            aw = chu = False
            if prev0 == 1 and is_w_col(pv) and closes_unit(onx):
                pnt = off > 0 and par0(Mo, off - 1) == 0
                shallow = not (hi and not pnt)
                aw = True
            if closes_hi_unit(p, onx, pv, pv2, hi, is_repeat(Mo, off)):
                shallow = True
                chu = True
            # sibend / sibdeep: 兄弟から渡ってきた深い側が生きているなら、
            # ユニットを閉じる合図（sibend は**行列の末尾だけ**）でも段を
            # 落とさない。P6 の 1 列短い接頭辞を深く綴れるようにする条項。
            if usesib and shallow and not aw and not chu:
                if FLAGS['sibdeep'] or (FLAGS['sibend'] and nxt is None):
                    shallow = False
            base = base_s if shallow else deep
            st['prev'] = 0 if shallow else 1
            if TRACE is not None:
                TRACE[off] = dict(bit=0 if shallow else 1, prev=prev0,
                                  aw=aw, chu=chu, sib=(base_sd != base_d),
                                  usesib=(usesib and not shallow), src=src,
                                  tail=(off == len(Mo) - 1), nxt=nxt,
                                  base_s=base_s, base_d=base_d,
                                  base_sd=base_sd, d=d, v=v, s2=s2)
        else:
            st['rec'][off] = 'tie'
            base = deep
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
        # 第 5 要素は子には渡さない（アンカーを素通りして次のユニットまで届く）。
        LA = tuple(t[:4] for t in LA)
    FA = F[:v] + (False,)
    # sibL: 行 1 の影を立てたら、あとの兄弟にも「深い側」を渡す。
    if FLAGS['sibL'] and Lb is not L:
        eo = Lat(L, v - 1)
        LS = (padL(L, v - 1) + ((eo[0], eo[1], eo[2], eo[3], base, off),)
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
                pre = contrPre(p, U, A, e, ps[0], st['prev'], na)
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
            elif FLAGS['mark'] and not leaves_mark_local(
                    A, U, dd, d, LA, L, FA, v, s2, e1, e2, st, na, oA, oU,
                    off + len(blk) - 1):
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
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0,
          'rec': {}}
    return tuple(conv3(list(M), st=st)), st['nc']


def b2d3(M):
    return b2d3n(M)[0]


def bits(M):
    """`b2d3` を回して {添字: 記録} と像を返す。"""
    global TRACE
    TRACE = {}
    try:
        img = b2d3(M)
        return dict(TRACE), img
    finally:
        TRACE = None


def install():
    rows3.conv3 = conv3
    rows3.conv_resid = conv_resid
    rows3.copy_shift = copy_shift
    rows3.contrPre = contrPre


def uninstall():
    import importlib
    importlib.reload(rows3)


# ---------------------------------------------------------------- 採点の道具
_GEN = {}


def gen(lim):
    if lim not in _GEN:
        _GEN[lim] = [M for M in sorted(gen3('BMS', lim, zcap=1), key=key)
                     if len(M) > 1]
    return _GEN[lim]


def c1_bad(f, lim=6, mm=10, nn=24):
    """共終性 C1 の破れ（`rows3.check` の (6) と同じ判定）。"""
    bad = set()
    for i, M in enumerate(gen(lim)):
        if i % 2000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear()
            core._flat_memo.clear()
        N = f(list(M))
        E = [tuple(expand(N, m)) for m in range(1, mm + 1)]
        G = [tuple(f(list(expand(tuple(M), n)))) for n in range(1, nn + 1)]
        if any(not any(cmpmat(e, g) <= 0 for g in G) for e in E):
            bad.add(tuple(M))
    return bad


def img_bad(f, lim=5, mmax=3, zcap=1, fallback=False):
    """ImgClosedT の破れた A の集合（`imgfast` の段 1 ＋ `preimage_try`）。"""
    import imgfast, inv3
    from rows3 import preimage_try
    A = [M for M in sorted(gen3('BMS', lim, zcap=zcap), key=key) if len(M) > 1]
    r = imgfast.imgclosed_fast(f, A, mmax,
                               lambda T: preimage_try(f, T, inv3.d2b3),
                               fallback=fallback)
    return r[2], r[1]


def quick(fl, lim6=True, z0=True):
    """主指標だけ手早く。`fl` は条項の並び。"""
    reset(*fl)
    install()
    out = {}
    t0 = time.time()
    out['img5'] = img_bad(b2d3, 5)[0]
    if lim6:
        out['img6'] = img_bad(b2d3, 6)[0]
    if z0:
        out['z0'] = img_bad(b2d3, 6, zcap=0)[0]
    out['c1'] = c1_bad(b2d3, 6)
    print('%-46s img5 %3d  img6 %3d  z0 %d  C1(<=6) %3d   (%.0fs)'
          % (flagstr(), len(out['img5']), len(out.get('img6', ())),
             len(out.get('z0', ())), len(out['c1']), time.time() - t0),
          flush=True)
    return out


def feats(M, fl=('v12', 'sibL')):
    """`M` を `fl` の条項で綴って、**兄弟の深い側を使った柱**の文脈を返す。"""
    reset(*fl)
    T, img = bits(list(M))
    Mo = tuple(M)
    out = []
    for off in sorted(T):
        r = T[off]
        if not r['usesib']:
            continue
        src = r['src']
        out.append(dict(
            off=off, col=Mo[off], src=src, srccol=Mo[src] if src is not None else None,
            gap=(off - src) if src is not None else None,
            prev=r['prev'], tail=r['tail'], aw=r['aw'], chu=r['chu'],
            ncol=len(Mo),
            anchor_between=(src is not None and any(
                tuple(Mo[j]) == ANCHOR for j in range(src + 1, off + 1))),
            sameunit=(src is not None
                      and unit_start(Mo, off) == unit_start(Mo, src)),
            srcs2=Mo[src][2] if src is not None else None,
            nunits=sum(1 for c in Mo if c[0] == 0),
            atend=(off >= len(Mo) - 2),
        ))
    return out, img


def table(Ms, fl=('v12', 'sibL'), tag=''):
    """行列の並びについて、兄弟の深い側を使った柱を 1 行ずつ並べる。"""
    print('--- %s (%d 個) ---' % (tag, len(Ms)))
    for M in sorted(Ms, key=key):
        fs, img = feats(M, fl)
        reset(*[x for x in fl if x != 'sibL'])
        img0 = b2d3(list(M))
        print('  %-40s' % show(M))
        print('      v12  %s' % show(img0))
        print('      sibL %s' % show(img))
        for r in fs:
            print('      柱%d %s <- src%s %s gap=%s prev=%s tail=%s aw=%s chu=%s '
                  'anch=%s unit=%s srcs2=%s'
                  % (r['off'], show([r['col']]), r['src'],
                     show([r['srccol']]) if r['srccol'] else '-', r['gap'],
                     r['prev'], r['tail'], r['aw'], r['chu'],
                     r['anchor_between'], r['sameunit'], r['srcs2']))


def score(fl=('v12', 'sibL', 'sib_anchbefore'), lim=5, imgc=3, sheet=True):
    """7 つの土俵で採点（`rows3.check` にかける）。"""
    t0 = time.time()
    reset(*fl)
    install()
    import sheet3
    print('=== 条項 %s ===' % flagstr())
    if sheet:
        sheet3.score(b2d3, 0)
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    print('BMS 3 行 z<2 標準形 (<=%d 列): %d' % (lim, len(A)))
    n = rows3.check(b2d3, A, verbose=3, imgc=imgc)
    print('合計違反 %d  (%.0fs)' % (n, time.time() - t0))
    return n


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'base'
    if cmd == 'base':
        # 旗を v12 にしたコピーが `rows3.b2d3` と一致するか
        reset('v12')
        A = sorted(gen3('BMS', int(sys.argv[2]) if len(sys.argv) > 2 else 6,
                        zcap=1), key=key)
        bad = sum(1 for M in A
                  if tuple(b2d3(list(M))) != tuple(rows3.b2d3(list(M))))
        print('コピーの食い違い (%d 個中): %d' % (len(A), bad))
    elif cmd == 'quick':
        quick(tuple(sys.argv[2:]) or ('v12',))
    elif cmd == 'score':
        score(tuple(sys.argv[3:]) or ('v12', 'sibL', 'sib_anchbefore'),
              int(sys.argv[2]) if len(sys.argv) > 2 else 5)
    elif cmd == 'table':
        # `sibL` が像を変える行列を全部並べる（<=lim 列）
        lim = int(sys.argv[2]) if len(sys.argv) > 2 else 6
        fl = tuple(sys.argv[3:]) or ('v12', 'sibL')
        reset(*[x for x in fl if not x.startswith('sib')])
        A = [tuple(M) for M in sorted(gen3('BMS', lim, zcap=1), key=key)]
        I0 = {M: tuple(b2d3(list(M))) for M in A}
        reset(*fl)
        ch = [M for M in A if tuple(b2d3(list(M))) != I0[M]]
        table(ch, fl, '像が変わる行列')
    elif cmd == 'p6':
        from core import parse
        import rule
        for spec in ('(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)',
                     '(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)'):
            M = parse(spec, 3)
            print(spec)
            for fl in (('v12',), ('v12', 'sibL'),
                       ('v12', 'sibL', 'sib_anchbefore'),
                       ('v12', 'sibL', 'sib_anchbefore', 'sibend')):
                reset(*fl)
                print('   %-42s %s' % (flagstr(), show(b2d3(list(M)))))
            print('   %-42s %s' % ('rule.convert', show(rule.convert(M))))
    else:
        print(__doc__)
