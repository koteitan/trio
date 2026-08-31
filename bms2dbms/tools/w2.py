"""課題 F2: ImgClosedT の破れ 26 個の「正しい像」を逆算する台。

**採用ずみ**: ここで決めた条項 `wchain` は課題 F5 で `rows3.conv3` に入った
（旗 `rows3.V13['wchain']`）。このファイルは逆算の手順と、条項を入れ切りして
比べるための台として残す（`install()` を呼ぶと `rows3` 側がこのファイルの
v12 ベースのコピーに差し替わるので、`rows3.V13` は効かなくなる）。

規則を当てずっぽうで直すのではなく、**先に正解を知る**。

    step1  <=5 列で ImgClosedT が破れる A（26 個）と (m, T=(conv3 A)<m>) を出す
    step2  A の像を N2 に取り替えると T の逆像が出る、そんな N2 を総当たり
    step3  逆写像 d2b3(T) = D の像 conv3(D) と T の差分を数える（もう一方の向き）
    step4  「深く綴るべき D」を集めてシートと突き合わせる
    step5  陽性（深くすべき）と陰性（シートが浅いと言う）を特徴で分離する
    score / img   条項 `wchain` を入れて 7 つの土俵で採点

== 結論（2026-08-27, 測定ずみ）==

**破れの正体は 1 つ。`after_w` の見る窓が「直前 1 本」しかないこと。**

step2（A の像を動かす向き）: 26 個中 21 個で、同じ長さの N2 は
**「末尾の柱の行 1 が +1」ただ 1 つ**（ヒント通り）。ただしその 12 個は
**シートに載っていて、シートはいまの浅い綴りを正しいと言う**（行 525 など）。
だから **A の像を動かすのは間違い**。

step3（小さいほうの像を動かす向き）: 破れ 51 対のうち **42 対**で
`D = d2b3(T)` は BMS 標準形で、`conv3(D)` は T と**末尾の柱の行 1 が 1 違う
だけ**（差分 (0,+1,0) 1 点）。つまり直すべきは A ではなく **D の綴り**。
D はどれも A<m>（長い展開）で、**1 個もシートに載っていない**ので矛盾しない。

裏取り（`scratchpad/gap2.log`）: A=(0,0,0)(1,1,1)(2,1,0)(2,1,0), m=2 の
目標 T について、順序の窓 (A<2>, A) に入る BMS 標準形を **<=12 列で
203481 個**歩いても、v12 で T に写るものは 1 つも無い。破れは本物である。

step5（分離条件）: 「深く綴るべき D」44 個と「シートが浅いと言う」137 個は

    hi_block（W_(w^2) 系）が真  かつ  「x w」の柱 (k,0,0) が末尾から距離 2〜3

で**ぴったり分かれる**（陽性 44/44 が該当、陰性 137/137 が非該当）。

== 条項 `wchain`（このファイルの conv3 のコピーに入っている）==

    `after_w` は「**直前の柱**が (k,0,0) ならユニットの端で段が落ちる」を見る。
    これを「**この写しの頭**まで」広げる: 後ろに (k,0,0) があって、そこから
    今の柱までがぜんぶその子孫（行 0 > k）なら、直前が (k,0,0) だったのと
    同じに扱う（深いのは `hi and not pnt` のとき。判定式は `after_w` と同一）。

`wchain_head(Mo, off)` がその柱をさがす。距離の上限は要らない
（「ぜんぶ子孫」が効く）。`after_w` が発火する場合はそちらが優先（elif）。

== 成績（conv3 v12 -> v12+wchain, 2026-08-27 実測）==

| 土俵 | v12 | +wchain |
|---|---|---|
| シート 3 行 z<=1（1358 対, 満点 1354） | 1354 | **1354** |
| **ImgClosedT の破れ A（<=5 列）** | 26 | **5** |
| **ImgClosedT の破れ A（<=6 列）** | 294 | **95**（201 直り・2 新規） |
| **ImgClosedT の破れ A（<=7 列）** | 3374 | **1487**（1916 直り・29 新規） |
| ImgClosedT の破れ 対（<=7 列） | 6855 | **2950** |
| z=0 の対照 ImgClosedT（<=6 列 3852 対） | 0 | **0** |
| z=0 <=8 列 44653 個 vs `rows2.convC` | 0 | **0** |
| 生成 <=6 列: 非標準 / 順序 / 単射 | 0 / 0 / 0 | **0 / 0 / 0** |
| 生成 <=6 列: 列数をまたぐ単射（閉包 15611） | 0 組 | **0 組** |
| 生成 <=6 列: `d2b3` 往復の失敗 | 0 | **0** |
| 生成 <=7 列 77282 個: 像が変わった数 | - | **48** |
| 生成 <=7 列: 非標準 / 順序違反 / 像の衝突 | 3 / 0 / 0 | **3 / 0 / 0** |
| 生成 <=8 列 781605 個: 像が変わった数 | - | **807** |
| 生成 <=8 列: 非標準 | 84 | **84** |
| 共終性 C1 の破れ（<=6 列） | 88 | **90**（0 直り・2 新規） |
| 共終性 C2 の破れ（<=6 列） | 0 | **0** |

**動いた土俵は ImgClosedT（大きく良化）と C1（2 だけ悪化）の 2 つだけ。**
ほかは 1 つも動かない（<=7 列で像が変わるのは 77282 個中 48 個）。

== 使い方 ==

    python3 w2.py step1          破れる (A, m, T) を出す（保存も）
    python3 w2.py step2          A の像を動かす向きの逆算（26 個ぜんぶ）
    python3 w2.py step3          d2b3(T)=D 側の差分の分布
    python3 w2.py step4          深くすべき D をシートと突き合わせ
    python3 w2.py step5          陽性／陰性の特徴くらべ（分離条件）
    python3 -c "import w2; w2.same(6)"            コピーの忠実さ
    python3 -c "import w2; w2.score(6, wchain=True)"   7 つの土俵
    python3 -c "import w2; w2.img(6,3,1,0,wchain=True)"  ImgClosedT だけ
    python3 -c "import w2; w2.img(6,3,0,0,wchain=True)"  z=0 の対照

`install()` は `rows3.conv3 / conv_resid / b2d3n / b2d3` をこのファイルの版に
差し替える。**`rows3.py` は書き換えない。**

== 残る 2 個（新しく壊れたもの）==

<=6 列で新しく壊れたのは 2 個だけ:
    (0,0,0)(1,1,1)(2,1,0)(2,0,0)(3,1,1)(4,1,0)
    (0,0,0)(1,1,1)(2,1,0)(3,0,0)(4,1,1)(5,1,0)
どちらも「wchain で深くした当人」で、こんどは**その展開が 1 段足りない**。
向きは逆（目標のほうが 1 だけ**浅い**）なので、`wchain` の伝染ではなく
別種の残余である。<=7 列では 29 個で、**29 個ぜんぶが同じ形**

    ... (k,0,0)(k+1,1,1)(a,1,0)      ＝ wchain が深くした当人

つまり残余は「wchain が深くした行列の**中**にある分岐列（次が (a+1,2,1) で
ユニットを閉じないので v12 が深く綴るもの）を、こんどは浅く綴るべき」である。
直りが 1916 / 新規が 29 なので**割に合う片側**だが、片側だけではない。

`wchain_end`（真の末尾でだけ発火する狭い版）は <=6 列で成績が同じ
（シート 1354・ImgClosedT 95）。この範囲では陽性はぜんぶ行列の末尾にある。
"""
import sys, os, time, json, collections, itertools

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import expand, isstd, show, parse, cmpmat
from rows3 import gen3, key, b2d3, conv3
import rows3

SCR = '/tmp/claude-1000/-home-koteitan-proofs-dbms/ebd5ffaf-97c2-45bc-92a0-5391fe3b1a6d/scratchpad'


def clr():
    core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()


def S(M):
    return show(list(M)) if M else '()'


# ---------------------------------------------------------------- step1
def step1(lim=5, mmax=3, save=True):
    """破れる (A, m, T) を全部出す。fast（段 1 だけ）で十分
    （NOTES: <=6 列までは段 2 の救出 0 なので段 1 の答えが確定値）。"""
    from imgfast import score
    t0 = time.time()
    r = score(b2d3, lim=lim, mmax=mmax, zcap=1, verbose=1, fallback=False)
    bad = sorted(r[2], key=key)
    print('\n破れた A: %d 個 / 破れた対: %d' % (len(bad), len(r.badpairs)))
    byA = collections.defaultdict(list)
    for M, m, T in r.badpairs:
        byA[M].append((m, T))
    out = []
    for i, M in enumerate(bad):
        N = tuple(b2d3(list(M)))
        ms = sorted(byA[M])
        print('%2d. A = %-46s  |A|=%d' % (i + 1, S(M), len(M)))
        print('      conv3 A = %s' % S(N))
        for m, T in ms:
            print('      m=%d  T = %s' % (m, S(T)))
        out.append({'A': list(map(list, M)), 'N': list(map(list, N)),
                    'ms': [[m, list(map(list, T))] for m, T in ms]})
    if save:
        with open(os.path.join(SCR, 'f2_bad%d.json' % lim), 'w') as fp:
            json.dump(out, fp)
        print('\n保存: %s/f2_bad%d.json  (%.0fs)' % (SCR, lim, time.time() - t0))
    return out



# ---------------------------------------------------------------- 像の辞書
_IMG = None
_GEN = None


def img_index(lim=7, verbose=1, cache=True):
    """BMS 3 行 z<2 標準形 <=lim 列の像を全部作って辞書にする。
    返り値 (IMG: 像 -> B, GEN: key 順に並べた B の並び)。"""
    global _IMG, _GEN
    if _IMG is not None and _IMG[0] == lim:
        return _IMG[1], _GEN
    t0 = time.time()
    cf = os.path.join(SCR, 'img%d.pkl' % lim)
    if cache and os.path.exists(cf):
        import pickle
        IMG, G = pickle.load(open(cf, 'rb'))
        if verbose:
            print('像の辞書 <=%d 列（キャッシュ）: BMS %d 個  (%.0fs)'
                  % (lim, len(G), time.time() - t0), flush=True)
        _IMG, _GEN = (lim, IMG), G
        return IMG, G
    G = sorted(gen3('BMS', lim, zcap=1), key=key)
    IMG = {}
    for M in G:
        N = tuple(map(tuple, b2d3(list(M))))
        if N not in IMG:          # 短い（小さい）ほうを優先して残す
            IMG[N] = M
    if verbose:
        print('像の辞書 <=%d 列: BMS %d 個 -> 像 %d 個  (%.0fs)'
              % (lim, len(G), len(IMG), time.time() - t0), flush=True)
    _IMG, _GEN = (lim, IMG), G
    return IMG, G


def near_last(T, IMG):
    """T と「末尾 1 列だけ違う」像を全部拾う（差分つき）。"""
    out, head = [], T[:-1]
    for N, B in IMG.items():
        if len(N) == len(T) and N[:-1] == head and N[-1] != T[-1]:
            out.append((tuple(a - b for a, b in zip(N[-1], T[-1])), N, B))
    out.sort()
    return out


def step2a(lim=7):
    """破れ 51 対それぞれで「T に一番近い像」を調べる（ヒントの確認）。"""
    IMG, G = img_index(lim)
    with open(os.path.join(SCR, 'f2_bad5.json')) as fp:
        bad = json.load(fp)
    cnt = collections.Counter()
    for e in bad:
        A = tuple(map(tuple, e['A']))
        for m, T in e['ms']:
            T = tuple(map(tuple, T))
            nn = near_last(T, IMG)
            if not nn:
                cnt['なし'] += 1
                print('  なし: %s m=%d  T=%s' % (S(A), m, S(T)))
                continue
            d, N, B = min(nn, key=lambda t: sum(map(abs, t[0])))
            cnt[d] += 1
    print('\n末尾 1 列の差分（届く像 - 目標）の分布:')
    for k, v in cnt.most_common():
        print('   %-24s %d' % (str(k), v))



# ---------------------------------------------------------------- 逆像の判定
def has_pre(T, IMG, d2b3=None, deep=False, m=None, A=None):
    """T の逆像（BMS 3 行 z<2 **標準形**）があるか。返り値 B or None。
    (a) 像の辞書 (b) 逆写像 d2b3 ＋ その接頭辞 (c) 望むなら誘導つき DFS。"""
    T = tuple(map(tuple, T))
    B = IMG.get(T)
    if B is not None:
        return B
    if d2b3 is None:
        from inv3 import d2b3 as _d
        d2b3 = _d
    from rows3 import preimage_try
    B = preimage_try(b2d3, T, d2b3)
    if B is not None:
        return B
    if deep and A is not None and m is not None:
        from imgfast import find2, LADDER_DEEP
        _, B, st, nodes, cap = find2(tuple(A), m, f=b2d3, ladder=LADDER_DEEP,
                                     T=T, usefast=False)
        return B
    return None


# ---------------------------------------------------------------- DBMS の候補
def dbms_ext(pre, lo, hi):
    """接頭辞 `pre` を持つ DBMS 3 行標準形を、長さ lo..hi で全部。"""
    out = []
    def rec(S):
        if lo <= len(S) <= hi:
            out.append(S)
        if len(S) >= hi:
            return
        amax = (S[-1][0] + 1) if S else 0
        for a in range(amax + 1):
            for b in range(max(a - 1, 0) + 1):
                for c in range(max(b - 1, 0) + 1):
                    P = S + ((a, b, c),)
                    if isstd(P, 'DBMS'):
                        rec(P)
    if not isstd(tuple(pre), 'DBMS'):
        return []
    rec(tuple(pre))
    return out


def cands(N, back=3, grow=2):
    """`N` と接頭辞を共有し末尾だけ違う DBMS 標準形（`N` 自身は除く）。"""
    seen, out = {tuple(N)}, []
    for k in range(len(N) - 1, max(len(N) - 1 - back, -1), -1):
        for P in dbms_ext(N[:k], max(1, len(N) - 1), len(N) + grow):
            if P not in seen:
                seen.add(P)
                out.append(P)
    return out


def bounds(A, G):
    """順序の窓 (lo, hi)。

    lo = max{ conv3 M : M < A }、hi = min{ conv3 M : M > A かつ A は M の接頭辞でない }。
    **A を接頭辞に持つ M は上界から外す**（A の像を変えればその像も動くので、
    窓を締めてはいけない）。"""
    from core import cmpmat
    A = tuple(A)
    lo = hi = None
    for M in G:
        c = cmpmat(M, A)
        if c < 0:
            f = tuple(map(tuple, b2d3(list(M))))
            if lo is None or cmpmat(f, lo) > 0:
                lo = f
        elif c > 0 and M[:len(A)] != A:
            f = tuple(map(tuple, b2d3(list(M))))
            if hi is None or cmpmat(f, hi) < 0:
                hi = f
    return lo, hi



# ---------------------------------------------------------------- step2
def solve_one(A, IMG, G, back=4, grow=0, mmax=3, lohi=None, verbose=1):
    """A の像を N2 に取り替えると m<=mmax の逆像が全部出る、そんな N2 を全部。

    条件 (a) N2 は DBMS 標準形
         (b) 順序の窓 lo < N2 < hi（`bounds`。A の延長は上界から外す）
         (c) m=1..mmax で N2<m> に BMS 標準形の逆像がある
    返り値 [(N2, [B_1..B_mmax], 差分)]。"""
    A = tuple(map(tuple, A))
    N = tuple(map(tuple, b2d3(list(A))))
    lo, hi = lohi if lohi else bounds(A, G)
    out = []
    for P in cands(N, back=back, grow=grow):
        if len(P) != len(N) and grow == 0:
            continue
        if (lo is not None and cmpmat(P, lo) <= 0) or (hi is not None and cmpmat(P, hi) >= 0):
            continue
        Bs, good = [], True
        for m in range(1, mmax + 1):
            B = has_pre(tuple(expand(P, m)), IMG)
            if B is None:
                good = False
                break
            Bs.append(B)
        if good:
            d = [(k, N[k] if k < len(N) else None, P[k] if k < len(P) else None)
                 for k in range(max(len(N), len(P)))
                 if (N[k] if k < len(N) else None) != (P[k] if k < len(P) else None)]
            out.append((P, Bs, d))
    return N, lo, hi, out


def step2(lim=7, back=4, mmax=3):
    """破れた A 26 個ぜんぶで「正しい像 N2」を逆算する。"""
    from core import cmpmat
    IMG, G = img_index(lim)
    with open(os.path.join(SCR, 'f2_bad5.json')) as fp:
        bad = json.load(fp)
    t0 = time.time()
    res, dcnt = [], collections.Counter()
    for e in bad:
        A = tuple(map(tuple, e['A']))
        N, lo, hi, sols = solve_one(A, IMG, G, back=back, mmax=mmax)
        print('A  = %s' % S(A))
        print('  N  = %s' % S(N))
        if not sols:
            print('  ** 同じ長さの N2 は無し **')
            dcnt['なし'] += 1
        for P, Bs, d in sols:
            taken = IMG.get(P)
            print('  N2 = %-52s 差分 %s%s'
                  % (S(P), ['%d: %s -> %s' % (k, a, b) for k, a, b in d],
                     ('   ※ すでに %s の像' % S(taken)) if taken else ''))
            for m, B in enumerate(Bs, 1):
                print('        m=%d  B = %s' % (m, S(B)))
            if len(d) == 1:
                k, a, b = d[0]
                dcnt[(k - len(N), tuple(x - y for x, y in zip(b, a)))] += 1
            else:
                dcnt['多点 %d' % len(d)] += 1
        res.append({'A': list(map(list, A)), 'N': list(map(list, N)),
                    'sols': [[list(map(list, P))] for P, _, _ in sols]})
    print('\n差分の分布（位置は末尾から, 値は N2 - N）:')
    for k, v in dcnt.most_common():
        print('   %-28s %d' % (str(k), v))
    with open(os.path.join(SCR, 'f2_sol.json'), 'w') as fp:
        json.dump(res, fp)
    print('%.0fs' % (time.time() - t0))



# ---------------------------------------------------------------- step3
def step3(lim=7):
    """もう一方の向き: **目標 T に一番近い像**を持つ小さい行列 D を見て、
    「D の像がどこで 1 だけ足りないか」を数える。

    `inv3.d2b3` は「T の逆像はこれのはず」を返す（`conv3` とは独立に作られた
    読み方）。その D の像と T の差分が 1 種類なら、直すべきは **D の綴り**である。
    """
    from inv3 import d2b3
    IMG, G = img_index(lim)
    with open(os.path.join(SCR, 'f2_bad5.json')) as fp:
        bad = json.load(fp)
    cnt, ex = collections.Counter(), []
    for e in bad:
        A = tuple(map(tuple, e['A']))
        for m, T in e['ms']:
            T = tuple(map(tuple, T))
            try:
                D = tuple(map(tuple, d2b3(list(T))))
            except Exception:
                D = None
            if not D:
                cnt['d2b3 が返さない'] += 1
                continue
            std = isstd(D, 'BMS') and all(c[2] <= 1 for c in D)
            fD = tuple(map(tuple, b2d3(list(D))))
            if not std:
                cnt['D が BMS 非標準'] += 1
                continue
            if fD == T:
                cnt['一致（破れでない）'] += 1
                continue
            if len(fD) == len(T):
                d = [(k - len(T), tuple(x - y for x, y in zip(T[k], fD[k])))
                     for k in range(len(T)) if T[k] != fD[k]]
                cnt[tuple(d)] += 1
                if len(ex) < 6:
                    ex.append((A, m, D, fD, T, d))
            else:
                cnt['長さが違う %+d' % (len(fD) - len(T))] += 1
    print('目標 T と d2b3(T) の像 conv3(D) の差分（位置は末尾から, 値は T - conv3 D）')
    for k, v in cnt.most_common():
        print('   %-40s %d' % (str(k), v))
    print()
    for A, m, D, fD, T, d in ex:
        print('A = %s   m=%d' % (S(A), m))
        print('  T       = %s' % S(T))
        print('  D       = %s' % S(D))
        print('  conv3 D = %s   差分 %s' % (S(fD), d))



# ---------------------------------------------------------------- step4
def deep_wanted(lim=7):
    """「末尾の柱の行 1 が 1 足りない」44 対から、**深く綴るべき行列 D** を集める。"""
    from inv3 import d2b3
    with open(os.path.join(SCR, 'f2_bad5.json')) as fp:
        bad = json.load(fp)
    want = {}
    for e in bad:
        A = tuple(map(tuple, e['A']))
        for m, T in e['ms']:
            T = tuple(map(tuple, T))
            try:
                D = tuple(map(tuple, d2b3(list(T))))
            except Exception:
                continue
            if not (D and isstd(D, 'BMS') and all(c[2] <= 1 for c in D)):
                continue
            fD = tuple(map(tuple, b2d3(list(D))))
            if len(fD) != len(T) or fD == T:
                continue
            d = [k for k in range(len(T)) if T[k] != fD[k]]
            if len(d) == 1 and tuple(x - y for x, y in
                                     zip(T[d[0]], fD[d[0]])) == (0, 1, 0):
                want.setdefault(D, []).append((A, m, d[0], len(T)))
    return want


def step4(lim=7):
    """深く綴るべき D と、シートが「浅いのが正しい」と言う行列を並べて比べる。"""
    import sheet3
    want = deep_wanted(lim)
    ST = {tuple(map(tuple, b)): (row, tuple(map(tuple, dd)))
          for row, b, dd in sheet3.load(1)}
    print('深く綴るべき D: %d 個' % len(want))
    rows_ng = []
    for D, uses in sorted(want.items(), key=lambda t: key(t[0])):
        fD = tuple(map(tuple, b2d3(list(D))))
        k = uses[0][2]
        tag = ''
        if D in ST:
            row, dd = ST[D]
            tag = ('  シート行%d %s' % (row, '一致' if dd == fD else '不一致'))
            if dd == fD:
                rows_ng.append((row, D))
        print('  %-52s 柱 %d/%d %s%s'
              % (S(D), k, len(fD), fD[k], tag))
    print('\n※ シートが「いまの綴りで正しい」と言う D: %d 個' % len(rows_ng))
    for row, D in rows_ng:
        print('    行%-6d %s' % (row, S(D)))


def branch_end(M):
    """末尾の柱の綴りを決めた列の位置と、そのときの `prev`（`rows3.conv3` の記録）。"""
    from rows3 import conv3
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    conv3(list(M), st=st)
    return st['rec']



# ---------------------------------------------------------------- step5
def dec_end(M):
    """`M` の**末尾の列**が分岐列のとき、`rows3.conv3` がそれをどう決めたか。
    返り値 (prev, shallow)。分岐列でなければ None。

    末尾では `nxt is None` なので `closes_unit` はいつも真、
    `closes_hi_unit` はいつも偽。だから
        浅い  <=>  not (prev == 1 かつ 直前が「x w」 かつ hi かつ not pnt)
    """
    from rows3 import is_branch, is_w_col, hi_block, par0, conv3
    M = tuple(map(tuple, M))
    if not is_branch(M[-1]):
        return None
    x = len(M) - 1
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': M, 'nc': 0, 'rec': {}}
    conv3(list(M), st=st)
    prev = st['rec'].get(x, 'なし')
    if prev == 'tie':
        return prev, None
    pv = M[x - 1] if x >= 1 else None
    hi = hi_block(M, x)
    shallow = True
    if prev == 1 and is_w_col(pv):
        pnt = x > 0 and par0(M, x - 1) == 0
        shallow = not (hi and not pnt)
    if prev == 0:
        shallow = True
    return prev, shallow


def endcase(M):
    """`M` の**末尾の列**が「行列の末尾で浅くされた分岐列」かどうか。
    返り値 None か、決める直前の `prev`（0/1/None）。"""
    from rows3 import is_branch, conv3
    M = tuple(map(tuple, M))
    if not is_branch(M[-1]):
        return None
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': M, 'nc': 0, 'rec': {}}
    conv3(list(M), st=st)
    return st['rec'].get(len(M) - 1, 'なし')


def feats(M):
    """末尾の分岐列まわりの特徴（分離条件さがし用）。"""
    from rows3 import (is_branch, is_w_col, hi_block, is_repeat, par0,
                       closes_unit, ANCHOR)
    M = tuple(map(tuple, M))
    x = len(M) - 1
    pv = M[x - 1] if x >= 1 else None
    pv2 = M[x - 2] if x >= 2 else None
    lastanc = max([q for q in range(x) if M[q] == ANCHOR], default=-1)
    lastz = max([q for q in range(x) if M[q][2] > 0], default=-1)
    lastw = max([q for q in range(x) if is_w_col(M[q])], default=-1)
    return dict(n=len(M), col=M[x], pv=pv, pv2=pv2,
                pv_branch=bool(pv and is_branch(pv)),
                pv_w=is_w_col(pv), hi=hi_block(M, x),
                rep=is_repeat(M, x), par0=par0(M, x),
                par0_pv=(par0(M, x - 1) if x >= 1 else None),
                anc=x - lastanc if lastanc >= 0 else None,
                zdist=x - lastz if lastz >= 0 else None,
                wdist=x - lastw if lastw >= 0 else None)


def step5(lim=7):
    """深く綴るべき 44 個（陽性）と、シートが浅いと言う行列（陰性）を並べる。"""
    import sheet3
    from rows3 import is_branch
    want = deep_wanted(lim)
    pos = [D for D in want if endcase(D) == 1]
    other = [D for D in want if endcase(D) != 1]
    neg = []
    for row, b, dd in sheet3.load(1):
        b = tuple(map(tuple, b))
        if not is_branch(b[-1]):
            continue
        if endcase(b) != 1:
            continue
        if tuple(map(tuple, b2d3(list(b)))) == tuple(map(tuple, dd)):
            neg.append((row, b))
    print('陽性（末尾を深くすべき, prev=1）: %d / 44' % len(pos))
    if other:
        print('  ※ prev!=1 のもの: %d  %s' % (len(other), [S(D) for D in other][:4]))
    print('陰性（シートが浅いと言う, prev=1）: %d' % len(neg))
    keys = ['n', 'pv_branch', 'pv_w', 'hi', 'rep', 'par0', 'par0_pv',
            'anc', 'zdist', 'wdist']
    for k in keys:
        pv = collections.Counter(feats(D)[k] for D in pos)
        nv = collections.Counter(feats(b)[k] for _, b in neg)
        sep = set(pv) & set(nv)
        print('  %-9s 陽性 %-38s 陰性 %-38s %s'
              % (k, str(sorted(pv.items(), key=str))[:38],
                 str(sorted(nv.items(), key=str))[:38],
                 '分離' if not sep else ''))
    print('\n--- 陰性の例 ---')
    for row, b in neg[:10]:
        print('  行%-6d %-46s %s' % (row, S(b), feats(b)))
    print('--- 陽性の例 ---')
    for D in pos[:6]:
        print('  %-46s %s' % (S(D), feats(D)))



# ================================================================ conv3 のコピー
# `rows3.conv3`（v12）の**逐語コピー**に、課題 F2 の条項 `wchain` を 1 つ
# 足したもの。`FL` を全部 False にすると `rows3.b2d3` と同じ答えになる
# （`w2.py same` で確かめる）。`rows3.py` は読むだけ。
FL = dict(wchain=False, wchain_end=False)

from rows3 import (split0, units_split, ok_place, fit, closes_unit, par0,
                   hi_block, is_repeat, is_w_col, closes_hi_unit, Lat, padL,
                   is_branch, dmap_at, copy_shift, contrPre, leaves_mark,
                   leaves_mark_local, conv_resid as _unused_cr,
                   NOTLAST, ANCHOR, V12, twin, untwin, terms0)


def wchain_head(Mo, off):
    """`off` から後ろへ「x w」の柱 (k,0,0) をさがす。ただし
    **その柱から `off` までの柱がぜんぶ行 0 > k**（＝その柱の子孫）でなければ
    ならない。見つからなければ None。

    直前 1 本だけを見る `after_w` を、写しの頭まで届くように広げたもの。
    `(k,0,0)(k+1,1,1)...(a,1,0)` のように、「x w」で開いた写しの中で
    分岐列が末尾に来る形を拾う。
    """
    for j in range(off - 1, -1, -1):
        if is_w_col(Mo[j]):
            k = Mo[j][0]
            if all(Mo[t][0] > k for t in range(j + 1, off + 1)):
                return j
            return None
        if Mo[j][0] == 0:
            return None
    return None


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
        # v12 mark: 局所版のガードのために「決める直前の段」を残す。
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
        # ---- 課題 F2 の条項 `wchain`（このファイルだけ） ----------------
        # `after_w` を**直前 1 本**から**この写しの頭まで**に広げる。
        # 「x w」の柱 (k,0,0) が後ろにあり、そこから今までの柱がぜんぶ
        # その子孫（行 0 > k）なら、直前が「x w」だったのと同じに扱う。
        # 逆算（`w2.step2/3/5`）が指す 44 個の陽性はぜんぶこの形で、
        # シートが「浅いのが正しい」と言う 137 個は 1 つも当たらない。
        elif FL['wchain'] and st['prev'] == 1 and closes_unit(onx):
            j = wchain_head(Mo, off)
            if j is not None and (not FL['wchain_end'] or onx is None):
                pnt = par0(Mo, j) == 0
                shallow = not (hi and not pnt)
        # closes_hi_unit（rule.py）: (a,2,1)(a,2,0)(a,1,0) と積んだ直後が
        # アンカー (1,1,1) なら、段を上げずにユニットを閉じる（浅い）。
        if closes_hi_unit(p, onx, pv, pv2, hi, is_repeat(Mo, off)):
            shallow = True
        base = base_s if shallow else base_d
        st['prev'] = 0 if shallow else 1
    else:
        base = base_d
        if is_branch(p):
            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い

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
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0,
          'rec': {}}
    return tuple(conv3(list(M), st=st)), st['nc']


def b2d3(M):
    return b2d3n(M)[0]




def install():
    """`rows3` 側の名前をこのファイルの版に差し替える（`z2.install` と同じ手）。
    `sheet3` / `inv3` / `rows3.check` / `imgfast` がそのままこの版を採点する。"""
    import rows3 as R
    R.conv3, R.conv_resid, R.b2d3n, R.b2d3 = conv3, conv_resid, b2d3n, b2d3
    import inv3, sheet3, imgfast
    for mod in (inv3, sheet3, imgfast):
        if hasattr(mod, 'b2d3'):
            mod.b2d3 = b2d3
    imgfast._F = b2d3
    return b2d3


def same(lim=6):
    """条項を全部切ったとき `rows3.b2d3` と同じ答えか（コピーの忠実さ）。"""
    import rows3 as R
    old = dict(FL)
    for k in FL:
        FL[k] = False
    n = d = 0
    for M in gen3('BMS', lim, zcap=1):
        n += 1
        if tuple(conv3(list(M))) != tuple(R.b2d3(list(M))):
            d += 1
    FL.update(old)
    print('コピーの忠実さ <=%d 列: %d 個中 食い違い %d' % (lim, n, d))
    return d



# ---------------------------------------------------------------- 採点
def score(lim=5, imgc=3, sheet=True, verbose=0, **fl):
    """7 つの土俵で採点する（`z2.score` と同じ手）。"""
    import rows3 as R
    t0 = time.time()
    if fl:
        for k in FL:
            FL[k] = False
        FL.update(fl)
    install()
    import sheet3
    print('=== 条項 %s ===' % ('+'.join(k for k, v in FL.items() if v) or 'v12'))
    if sheet:
        sheet3.score(b2d3, 0)
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    print('BMS 3 行 z<2 標準形 (<=%d 列): %d' % (lim, len(A)))
    n = R.check(b2d3, A, verbose=verbose, imgc=imgc)
    print('合計違反 %d  (%.1fs)' % (n, time.time() - t0))
    return n


def img(lim=5, mmax=3, zcap=1, fallback=0, **fl):
    """ImgClosedT だけを測る（`imgfast.score`）。`zcap=0` で z=0 の対照。"""
    if fl:
        for k in FL:
            FL[k] = False
        FL.update(fl)
    install()
    import imgfast
    r = imgfast.score(b2d3, lim=lim, mmax=mmax, zcap=zcap, verbose=1,
                      fallback=bool(fallback))
    return r


if __name__ == '__main__':
    a = sys.argv[1:] or ['step1']
    cmd, rest = a[0], [int(x) for x in a[1:] if x.lstrip('-').isdigit()]
    globals()[cmd](*rest)
