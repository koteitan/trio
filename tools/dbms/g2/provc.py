"""rows3.conv3 の写し（出どころを PROV に記録する）。mkprov.py が生成。"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from rows3 import (split0, Lat, padL, is_branch, is_w_col, par0,
                   hi_block, is_repeat, closes_unit, closes_hi_unit,
                   wchain_head, sib_ok, ok_place, fit, dmap_at,
                   copy_head, term_top, top_level, closes_top, hi_block2,
                   anch_before, p0deep_ok,
                   units_split, contrPre, leaves_mark,
                   leaves_mark_local, ANCHOR, NOTLAST, copy_src, par0_w,
                   p0_shallow, closes_w, sibnb_ok, _parK,
                   first_of, ps_of,
                   aw_flip,
                   tie_sd, _DMAP_TRACE,
                   V12, V13, V14, V15, V16, V17, V18, V20)
PROV = []
CTX = []


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

    src = None
    why = None
    if v == 0:
        base_d = base_s = base_sd = 0
        pl2, force1 = 0, False
    else:
        e = Lat(L, v - 1)
        base_d, pl2, force1, base_s = e[0] + 1, e[1], e[2], e[3] + 1
        # v13 sibL: 第 5 要素 = 兄弟だけが使える深い側、第 6 要素 = それを
        # 書いた柱のもとの添字。無ければ深い側と同じ（＝ v12 のまま）。
        base_sd = (e[4] if len(e) > 4 else e[0]) + 1
        src = e[5] if len(e) > 5 else None
    first1 = F[v] if v < len(F) else True

    # v12 newterm（課題 E2）: 行 0 が 0 の柱 (0,*,*) は**新しい加算項**の頭。
    # ユニットが変わるのだから、直前の分岐列の選択は次の項に持ち越さない。
    # 持ち越すと A ++ A の 2 つ目の写しで段が浅く綴られ、f が和について
    # 加法的でなくなる（ImgClosedT と共終性 C1 の破れ）。実測（`z2.py`）:
    #   gen<=7 の 77282 個で像の差 0、gen<=8 の 781605 個で 50 個だけ変わる
    #   C1 の破れ <=5/<=6/<=7 列  7/121/1572 -> 5/88/1167（破れ集合は真部分集合）
    #   ImgClosedT の破れ A       28/327/3779 -> 26/294/3374（同）
    #   新しく壊れたものは 0
    if V12['newterm'] and p[0] == 0:
        st['prev'] = None
    # v14 wterm（試作, 既定 off）: 根に直付けの「x w」の柱 (k,0,0) も
    # 新しい加算項の頭なので段の状態を持ち越さない。生成 <=8 列の非標準 3 件
    # （`(0,0,0)(1,1,1)(2,1,0)(1,0,0)(2,1,1)(2,1,0)(3,2,1)X`）を狙う。
    elif (V14['wterm'] and is_w_col(p)
            and (par0_w if V15['wterm_chain'] else par0)(st['Mo'], off) == 0
            and not (V14['wterm_anchbefore']
                     and any(tuple(c) == ANCHOR for c in st['Mo'][:off]))):
        st['prev'] = None

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
    if is_branch(p):
        nxt = M[1] if len(M) > 1 else nx
        # v13 sibL（課題 F1）: 深い側の候補は、兄弟から渡ってきた `base_sd` を
        # 使ってよければそれ。門は「浅い側 != 深い側の候補」で開く。
        # v12 では門が `base_s != base_d` だったので、`base_sd` を入れると
        # 門の判定にも `base_sd` が要る（さもないと選択肢が消える）。
        deep = base_d
        if V13['sibL'] and base_sd != base_d and sib_ok(off, src, st):
            deep = base_sd
        if base_s != deep:
            # v12 mark: 局所版のガードのために「決める直前の段」を残す。
            st['rec'][off] = st['prev']
            shallow = (st['prev'] == 0) or closes_unit(nxt)
            why = ('prev0' if st['prev'] == 0 else
                   ('closes' if closes_unit(nxt) else 'plain'))
            # ここから先はもとの行列 Mo を直接見る。ブロックに切ってしまうと
            # 「直前の柱」が見えなくなるが、段の規則は直前 2 本を見て決まる。
            Mo = st['Mo']
            pv = Mo[off - 1] if off >= 1 else None
            pv2 = Mo[off - 2] if off >= 2 else None
            onx = Mo[off + 1] if off + 1 < len(Mo) else None
            hi = hi_block(Mo, off)
            # v14 h1（課題 H1）: 写しの中で「段が 1 だけ浅い」と綴る病
            # （ImgClosedT の族 α）を直す。どれも `Mo` と `off` と次の柱だけで
            # 決まる（＝写しに同変）。
            _w0 = False       # 位置から読んで深くしたか（P1 `wide0_noprev`）
            if V14['h1']:
                hi = hi_block2(Mo, off)
                cw = closes_top(Mo, off, nxt)
                if V15['closesw'] and closes_w(Mo, off, nxt):
                    cw = True     # P2 `closesw`: 化けたアンカーも閉じる
                if st['prev'] == 0:
                    # 課題 H6: `prev == 0` の枝は `p0_shallow` 1 つで完全に決まる
                    # （教師データ 6480 本で食い違い 0）。`closes_top` /
                    # `closes_unit` / `p0deep_ok` の 3 段重ねを置き換える。
                    _w0 = not p0_shallow(Mo, off)
                    shallow = not _w0
                elif cw:
                    shallow = True
            # after_w（rule.py）: 直前が「x w」の柱 (k,0,0) で、しかもユニットの
            # 端にいるなら、段はふつう 1 に落ちる（浅い）。W_(w^2) 系（hi）で
            # 直前の柱が根に付いていないときだけ、段が残る（深い）。
            _p0 = par0_w if V15['wroot'] else par0
            if st['prev'] == 1 and is_w_col(pv) and closes_unit(onx):
                pnt = off > 0 and _p0(Mo, off - 1) == 0
                shallow = not (hi and not pnt)
                why = 'after_w'
                # v17 awflip（課題 H13）: 発火 27 回（lim=6）の稀な枝だが、
                # 証人が要求する反転の 23/24 がここ。門は `aw_flip`。
                if (V17['awflip'] and aw_flip(Mo, off)
                        and not (V17['awdown'] and shallow)):
                    shallow = not shallow
            # v13 wchain（課題 F2）: `after_w` の窓は**直前 1 本**しかない。
            # 「x w」の柱がもっと後ろにあって、そこから今までがぜんぶその子孫
            # なら、直前が「x w」だったのと同じに扱う（判定式は after_w と同じ、
            # 親を見る柱だけ (k,0,0) 本人にする）。`after_w` が発火するときは
            # そちらが優先（elif）。
            elif V13['wchain'] and st['prev'] == 1 and closes_unit(onx):
                j = wchain_head(Mo, off)
                if j is not None:
                    shallow = not (hi and not (_p0(Mo, j) == 0))
                    why = 'wchain'
            # closes_hi_unit（rule.py）: (a,2,1)(a,2,0)(a,1,0) と積んだ直後が
            # アンカー (1,1,1) なら、段を上げずにユニットを閉じる（浅い）。
            if closes_hi_unit(p, onx, pv, pv2, hi, is_repeat(Mo, off)):
                shallow = True
                why = (why or '?') + '+closes_hi'
            # P3 `cpyspell`: 写しの中の分岐列は、写しのもとの柱と同じに綴る。
            # 縮約が飲んだ写しは決定を残さないので、写しの鎖をさかのぼる。
            if (V15['cpyspell']
                    and not (V15['cpy_notlast'] and closes_unit(nxt))
                    and not (V15['cpy_noend'] and nxt is None)):
                dec = st.setdefault('dec', {})
                j, seen = copy_src(Mo, off), 0
                while j is not None and j not in dec and seen < len(Mo):
                    j, seen = copy_src(Mo, j), seen + 1
                if j is not None and j in dec and not (
                        V15['cpy_noanch']
                        and any(tuple(c) == ANCHOR for c in Mo[j:off])):
                    if not (V15['cpy_endshal'] and nxt is None and not dec[j]):
                        shallow = dec[j]
            if V15['cpyspell']:
                st.setdefault('dec', {})[off] = shallow
            base = base_s if shallow else deep
            why = (why or '?') + ('/shallow' if shallow else '/deep')
            # P1 `wide0_noprev`: 位置から読んで深くしたときは、深さは像に出るが
            # 1 ビットの状態は 0 のまま置く（`prev == 1` は「ユニットがまだ
            # 閉じていないので深く綴った」の意味で、`after_w` / `wchain` は
            # それを見て発火する）。
            if not (V15['wide0_noprev'] and not shallow
                    and st['prev'] == 0 and _w0):
                st['prev'] = 0 if shallow else 1
        else:
            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い
            why = 'tie'
            base = deep
            # v18 tiesd（課題 H14）: `sib_ok` が閉じて `base_sd` が捨てられる
            # 枝。門 `tie_sd` が開くときだけ深い側を使う。
            if (V18['tiesd'] and base_sd != deep
                    and tie_sd(st['Mo'], off)):
                base = base_sd
    else:
        base = base_d
        # v16 sibnb（課題 H11）: 兄弟に渡す「深い側」は分岐列だけのもの
        # ではない。門は `sibnb_ok`（行列から読める 6 条件の連言）。
        if (V16['sibnb'] and v >= 1 and base_sd != base_d
                and sib_ok(off, src, st) and sibnb_ok(st['Mo'], off)):
            base = base_sd

    lad1 = first1 and s2 == pl2 + 1 and (base <= s2 or force1)
    e1 = base + 1 if lad1 else (s2 + 1 if (s2 > 0 and base <= s2) else base)
    e2 = s2
    h1 = base if lad1 else e1
    lad0 = first and v == ps[0] + 1 and (d <= h1 or force)

    ST = st['ST']
    cols = []
    if lad0:
        cols.append((d, pw[0], pw[1]))
        PROV.append(('sh0', off, why, tuple(CTX)))
        ST = ST[:d] + ((pw[0], pw[1]),)
        dd = d + 1
    else:
        dd = fit(ST, d, h1)
        if dd is None:
            dd = max(d, len(ST))
    if lad1:
        cols.append((dd, base, pl2))
        PROV.append(('sh1', off, why, tuple(CTX)))
        ST = ST[:dd] + ((base, pl2),)
        dd += 1
    if not ok_place(ST, dd, e1):
        x = fit(ST, dd, e1)
        if x is not None:
            dd = x
    cols.append((dd, e1, e2))
    PROV.append(('body', off, why, tuple(CTX)))
    ST = ST[:dd] + ((e1, e2),)
    st['ST'] = ST
    if _DMAP_TRACE is not None:               # 課題 R13: (D0') の計器
        _DMAP_TRACE.append((off, p[0], dd, tuple(st['dmap'])))
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
    if V13['sibL']:
        # 第 5/6 要素は**子には渡さない**（渡すとアンカーを素通りして
        # 次の加算ユニットまで深い綴りが届いてしまう）。
        LA = tuple(t[:4] for t in LA)
    FA = F[:v] + (False,)
    # v13 sibL: 行 1 の影を立てたら、そのあとの**兄弟**にも「深い側」を渡す。
    if V13['sibL'] and Lb is not L:
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
            # 写しの終わりの分岐列は、写しが吸収されるぶん深く書かれることがある。
            # 素直な「次の列 = q」と「深い側」の 2 通りを試す。
            for na in (q, NOTLAST):
                # 課題 H5 (3): ここは `st['prev']` を読んでいたが、**読む必要が無い**。
                # `None` / `1` / 行列から読んだ近似 のどれに替えても像は 1 ビットも
                # 変わらない（gen<=7 の 77282 個、<=6 列の展開 33548 個（最長 30 列超）
                # で差 0。lim=5 の 7 土俵も全部不変）。`0` に替えたときだけ 7 個変わり
                # シートが 1354 -> 1112 に落ちるので、「0 でない」ことだけが効いている。
                # 写しに同変でない読みを 1 つ減らすため、定数にする。
                pre = contrPre(p, U, A, e, ps[0], None, na)
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
            elif V12['mark'] and not (
                    leaves_mark(A, U, dd, d, LA, L, FA, v, s2, e1, e2, st,
                                na, q, oA, oU)
                    if V12['mark_global'] else
                    leaves_mark_local(A, U, dd, d, LA, L, FA, v, s2, e1, e2,
                                      st, na, oA, oU, off + len(blk) - 1)):
                # v12 mark（課題 E1）: 残余なしの縮約は「写しを飲んだ印が像に
                # 残る」ときだけ許す。印が残らないと `M` と `M ++ q ++ 写し` が
                # 同じ像に潰れる（単射性の破れ）。実測（`z1.py`）:
                #   gen<=7 の 77282 個で像の差 0（変わるのは長い双子だけ）
                #   双子 3609 個で 24 個の像が変わり、24 個ぜんぶが「潰れて
                #   いたものが分離した」側。閉包 127182 個で衝突 24 -> 0
                #   シート 1354 / z=0 / 非標準 / 順序 / ImgClosedT / 共終性は不変
                continue
            Lr = padL(L, v) + (((base, pl2, fc, base) if e else (e1, s2, fc, e1)),)
            hd = lambda *ls: next((l[0] for l in ls if l), nx)
            # 写しは書かれないので、A から見た「次の列」は写しの後ろ
            # 写しは書かれないので、A から見た「次の列」は写しの後ろ。
            # 何も無くても「レベルが後で綴られている」ので末尾扱いにはしない。
            CTX.append('cA')
            cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,
                       U[0] if U else na, oA)
            CTX.pop()
            CTX.append('cU')
            cU = conv3(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na,
                       oU)
            CTX.pop()
            # 写しの真下（もとの深さ p[0]+1）なら影の位置、さらに深ければ
            # 「もとの深さ -> 像の深さ」の表で決める。
            rd = (d + 1 + e if (not rest2 or rest2[0][0] == p[0] + 1)
                  else dmap_at(st, rest2[0][0] - 1))
            # 残余は 1 本の木ではなく**森**。深さをそろえずに読む（conv_resid）。
            CTX.append('cR')
            cR = conv_resid(rest2, rd, Lr, (v, s2), (e1, e2), st, hd(Bq), oR)
            CTX.pop()
            CTX.append('cB')
            cB = conv3(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                       oBq)
            CTX.pop()
            st['nc'] = st.get('nc', 0) + 1      # 縮約が発火した回数
            return cols + cA + cU + cR + cB

    # ここで「行 1 の影を立てた柱の兄弟を、影の横（深さ d）ではなく本体の横
    # （深さ dd）に付ける」規則（x_spell.py の sibbody2/3）を試したが、
    # **採らなかった**。gen<=7 の非標準を 3->1、gen<=8 を 84->42 に減らす代わりに、
    # 共終性 C1 を 1 件（<=5 列）・11 件（<=6 列）新しく壊す。詳しくは
    # モジュール docstring の「採らなかった規則」。
    cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
               B[0] if B else nx, oA)
    cB = conv3(B, d, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)
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
        # v16（課題 H12）: `first` / `ps` は行列から読める。ここだけ
        # `False` / 親でない `ps` を渡していたので、写しに同変な読みに直す。
        # 実測: gen<=7 の 77282 個・lim=6 の展開 25158 個で**像の差 0**、
        # lim=7 の一致も +0/-0 の完全な no-op。非同変な読みが 2 つ消える。
        Mo_ = st['Mo']
        out += conv3(head, rd, Lr, (False,) * 12, ps_of(Mo_, off), pw,
                     first_of(Mo_, off), False, st, nx2, off)
        if not tail:
            break
        rd = max(0, rd - (m0 - tail[0][0]))   # もとの深さの差だけ浅くする
        off += i
        rest = tail
    return out



def b2d3p(M):
    """(像, PROV) の対。PROV は出力の柱と 1 対 1 で同じ順に並ぶ。"""
    del PROV[:]
    del CTX[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0,
          'rec': {}}
    out = tuple(conv3(list(M), st=st))
    assert len(out) == len(PROV), (len(out), len(PROV))
    return out, list(PROV)
