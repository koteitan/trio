"""BMS -> DBMS の「素朴な構文的推測」ルール。

R1: 先頭に DBMS 対角の長さ Y-1 の接頭辞 (0)(1)(2,1)... を付け、
    もとの各列 (a_0,...,a_{Y-1}) を (a_0+(Y-1), a_1+(Y-2), ..., a_{Y-1}+0) にずらす。
    根拠: BMS の (0^Y)(1^Y) が DBMS の (0)(1)(2,1)...(Y,Y-1,...,1) に対応するため。

R2: R1 を「行 0 が 0 の列で切ったブロック（＝順序数の和の項）」ごとに適用して連結。
    f は和について加法的なので R1 より筋がよい……はずだが、単項ブロックで壊れる。
"""
from __future__ import annotations
from functools import lru_cache
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import Mat, diag, rows, isstd


def R1(m: Mat, Y: int | None = None) -> Mat:
    if Y is None:
        Y = rows(m)
    if not m:
        return ()
    off = tuple(Y - 1 - y for y in range(Y))
    return diag('DBMS', Y - 1, Y) + tuple(
        tuple(c[y] + off[y] for y in range(Y)) for c in m)


def _blocks(m: Mat):
    out, cur = [], []
    for c in m:
        if c[0] == 0 and cur:
            out.append(tuple(cur)); cur = []
        cur.append(c)
    if cur:
        out.append(tuple(cur))
    return out


def R2(m: Mat, Y: int | None = None) -> Mat:
    if Y is None:
        Y = rows(m)
    return tuple(c for b in _blocks(m) for c in R1(b, Y))


# ---------------------------------------------------------------- R7
from core import pim


def R7(m: Mat, Y: int | None = None) -> Mat:
    """「影つき階段」規則（本命の予想）。

    BMS の列 x を DBMS の 1 列 T に写すが、行 y (y>=1) の親になる列は DBMS では
    「行 y-1 で 1 段深い影の列」でなければならない。足りなければ影の列を挿入する
    （これが階段）。影は使い回されるので、同じ親に対する挿入は 1 回だけ。

      shadow(p, 0) = img[p]
      shadow(p, y) = shadow(p, y-1)                     … 行 y-1 の値が 1 以上なら
                   = 新しい列 shadow(p,y-1)+（行 0..y-1 に +1）  … さもなくば挿入
      T[y] = out[shadow(P_y(x), y)][y] + 1   (1 <= y <= t)
      T[0] = max(out[img[P_0(x)]][0], out[shadow(P_t(x), t)][0]) + 1
    """
    if Y is None:
        Y = rows(m)
    if not m:
        return ()
    P = pim(m)
    out: list = []
    img: list = [None] * len(m)
    sh: dict = {}

    def shadow(p: int, y: int) -> int:
        if y == 0:
            return img[p]
        key = (p, y)
        if key in sh:
            return sh[key]
        s = shadow(p, y - 1)
        if out[s][y - 1] >= 1:
            r = s
        else:
            col = [out[s][z] + 1 if z < y else 0 for z in range(Y)]
            out.append(tuple(col))
            r = len(out) - 1
        sh[key] = r
        return r

    for x, c in enumerate(m):
        nz = [y for y in range(Y) if c[y] > 0]
        if not nz:
            out.append(tuple([0] * Y))
            img[x] = len(out) - 1
            continue
        t = nz[-1]
        base = shadow(P[x][t], t) if P[x][t] != -1 else None
        T = [0] * Y
        for y in range(1, t + 1):
            p = P[x][y]
            T[y] = out[shadow(p, y)][y] + 1 if p != -1 else 0
        p0 = P[x][0]
        T[0] = out[img[p0]][0] + 1 if p0 != -1 else 0
        # 敷き直しで捨てられた側に行 0 の親がいるなら、写しのほうを使う
        if (p1 > 0 and (p1, lvl) in relaid and p0 != -1
                and img[p0] < relaid[(p1, lvl)]):
            T[0] = out[base][0] + 1
        if base is not None:
            for y in range(0, t + 1):
                T[y] = max(T[y], out[base][y] + 1)
        out.append(tuple(T))
        img[x] = len(out) - 1
    return tuple(out)


# ---------------------------------------------------------------- R8 = R7 + 余分なコピーの縮約
from core import expand, isstd, pim as _pim


def _badroot(Z):
    X = len(Z); x = X - 1; Y = len(Z[0])
    if all(v == 0 for v in Z[x]):
        return None, None
    t = max(y for y in range(Y) if Z[x][y] > 0)
    r = _pim(Z)[x][t]
    if r == -1:
        return None, None
    return r, x - r


def reduce_once(Z):
    """良い部分の末尾がバッド部のコピー 1 個ぶんなら落とす（順序数は不変）。

    expand(Z, n) = G' ++ B ++ n個 、 expand(Z_red, n+1) = G' ++ (n+1)個 なので
    expand(Z_red, n+1) == expand(Z, n) が全 n で成り立てば sup は等しい。
    """
    r, bp = _badroot(Z)
    if r is None or r < bp:
        return None
    cand = Z[:r - bp] + Z[r:]
    for n in range(4):
        if expand(cand, n + 1) != expand(Z, n):
            return None
    return cand


def normalize(Z, limit=64):
    """接頭辞ごとに「余分なコピー 1 個」を落とす縮約を、標準形になるまで繰り返す。"""
    for _ in range(limit):
        if isstd(Z, 'DBMS'):
            return Z
        done = False
        for L in range(len(Z), 1, -1):
            c = reduce_once(Z[:L])
            if c is not None:
                Z = c + Z[L:]
                done = True
                break
        if not done:
            return Z
    return Z


def R8(m: Mat, Y: int | None = None) -> Mat:
    return normalize(R7(m, Y))


# ---------------------------------------------------------------- R9 = R7 + 一般の重複縮約
from core import cmpmat


def cofinal(Z, W, K=3, K2=6):
    """{Z[n]} と {W[m]} が互いに共終か（＝ sup が等しいか）を有限近似で判定。

    展開結果はどちらも DBMS 側の行列なので cmpmat で直接比較できる。
    reduce_once の `expand(Z_red,n+1)==expand(Z,n)` は delta=0 の場合しか通らないが、
    こちらは基本列の形が違っていても sup の一致を拾える。
    """
    ez = [expand(Z, n) for n in range(1, K2 + 1)]
    ew = [expand(W, m) for m in range(1, K2 + 1)]
    for n in range(K):
        if not any(cmpmat(ez[n], w) <= 0 for w in ew):
            return False
    for m in range(K):
        if not any(cmpmat(ew[m], z) <= 0 for z in ez):
            return False
    return True


def dup_candidates(Z):
    """Z[i-L:i] == Z[i:i+L] な逐語重複を 1 個落とした候補（長い方・右から）。"""
    n = len(Z)
    out = []
    for L in range(n // 2, 0, -1):
        for i in range(n - L, L - 1, -1):
            if Z[i - L:i] == Z[i:i + L]:
                out.append(Z[:i] + Z[i + L:])
    return out


def normalize2(Z, limit=24):
    """非標準形のあいだ、共終性を保つ逐語重複の削除を繰り返す。"""
    for _ in range(limit):
        if isstd(Z, 'DBMS'):
            return Z
        nxt = None
        for c in dup_candidates(Z):
            if cofinal(Z, c):
                nxt = c
                break
        for cand in _absorb_cands(Z):
            if isstd(cand, 'DBMS'):
                return cand          # 吸収は標準形になるときだけ使う
        if nxt is None:
            return Z
        Z = nxt
    return Z


def R9(m: Mat, Y: int | None = None) -> Mat:
    return normalize2(R7(m, Y))


# ---------------------------------------------------------------- R10 = R7 + 縮約（2 つの健全性判定の OR）
def accept(Z, c):
    if cofinal(Z, c):
        return True
    for n in range(4):                      # delta=0 型（添字が 1 ずれるだけ）
        if expand(c, n + 1) != expand(Z, n):
            return False
    return True


def normalize3(Z, limit=24):
    for _ in range(limit):
        if isstd(Z, 'DBMS'):
            return Z
        nxt = None
        for c in dup_candidates(Z):
            if accept(Z, c):
                nxt = c
                break
        for cand in _absorb_cands(Z):
            if isstd(cand, 'DBMS'):
                return cand          # 吸収は標準形になるときだけ使う
        if nxt is None:
            return Z
        Z = nxt
    return Z


def R10(m: Mat, Y: int | None = None) -> Mat:
    return normalize3(R7(m, Y))


# ---------------------------------------------------------------- R12 ブロックごとの一様オフセット
def _topt(c):
    nz = [y for y in range(len(c)) if c[y] > 0]
    return nz[-1] if nz else -1


def R12(m: Mat, Y: int | None = None, tfun=None) -> Mat:
    """行 0 の根で切ったブロックごとに、そのブロックの深さ t だけ「階段」を前置して
    一様オフセット (t, t-1, ..., 0) を足す。

    psi(W_(wk)) 族などはこれで完全に一致する:
      BMS  (0,0,0)(1,1,1)(2,1,0)(3,2,1)
      -> 前置 (0)(1) ＋ 各列に (2,1,0) を足す
      =    (0)(1)(2,1)(3,2,1)(4,2)(5,3,1)   （正解）
    """
    if Y is None:
        Y = rows(m)
    out = []
    for b in _blocks(m):
        t = max((_topt(c) for c in b), default=-1)
        if tfun is not None:
            t = tfun(b, t)
        if t <= 0:
            out.extend(b)
            continue
        off = tuple(max(t - y, 0) for y in range(Y))
        out.extend(diag('DBMS', t, Y))
        out.extend(tuple(c[y] + off[y] for y in range(Y)) for c in b)
    return tuple(out)


# ---------------------------------------------------------------- R13 深さを状態にした階段
def R13(m: Mat, Y: int | None = None, deep=None) -> Mat:
    """R7 の階段に「レベル（影の深さ）」の状態を足したもの。

    観測: 印の無い列 (2,1,0) の像の行 1 値は、その列が行 0 の木で葉なら 1、
    子孫を持つなら 2 になる。つまり使う影の深さが 1 段変わる。
    deep(x) が真なら shadow(P_t(x), t+1) を使う。
    """
    if Y is None:
        Y = rows(m)
    if not m:
        return ()
    P = pim(m)

    def has_desc0(x):
        for z in range(x + 1, len(m)):
            j = z
            while j != -1:
                if j == x:
                    return True
                j = P[j][0]
        return False

    if deep is None:
        deep = has_desc0
    out: list = []
    img: list = [None] * len(m)
    sh: dict = {}

    def shadow(p: int, y: int) -> int:
        if y <= 0:
            return img[p]
        key = (p, y)
        if key in sh:
            return sh[key]
        s = shadow(p, y - 1)
        if out[s][y - 1] >= 1:
            r = s
        else:
            col = [out[s][z] + 1 if z < y else 0 for z in range(Y)]
            out.append(tuple(col))
            r = len(out) - 1
        sh[key] = r
        return r

    for x, c in enumerate(m):
        nz = [y for y in range(Y) if c[y] > 0]
        if not nz:
            out.append(tuple([0] * Y)); img[x] = len(out) - 1; continue
        t = nz[-1]
        lvl = t + 1 if (t < Y - 1 and deep(x)) else t
        base = shadow(P[x][t], lvl) if P[x][t] != -1 else None
        T = [0] * Y
        for y in range(1, t + 1):
            p = P[x][y]
            T[y] = out[shadow(p, y)][y] + 1 if p != -1 else 0
        p0 = P[x][0]
        T[0] = out[img[p0]][0] + 1 if p0 != -1 else 0
        # 敷き直しで捨てられた側に行 0 の親がいるなら、写しのほうを使う
        if (p1 > 0 and (p1, lvl) in relaid and p0 != -1
                and img[p0] < relaid[(p1, lvl)]):
            T[0] = out[base][0] + 1
        if base is not None:
            for y in range(0, t + 1):
                T[y] = max(T[y], out[base][y] + 1)
        out.append(tuple(T)); img[x] = len(out) - 1
        realimg.append((len(out) - 1, x))
        if len(c) > 1 and c[0] == c[1] and c[0] >= 1:
            anchors.add(img[x])
        while absorb_tail():
            pass
    return tuple(out)


# ---------------------------------------------------------------- R15 一様オフセット + 深さ状態
def R15(m: Mat, Y: int | None = None, mode='desc') -> Mat:
    """R12（ブロック単位の一様オフセット）に「行 1 のオフセットは列ごと」を足す。

    行 0 のオフセットはブロックの深さ t で一様、行 1 のオフセットは
    その列が「深い」かどうかで t-1 か 0。深さの判定は mode で切り替える:
      'desc'   行 0 の木で子孫を持つ
      'mark'   自分に行 2 の印がある
      'both'   どちらか
    """
    if Y is None:
        Y = rows(m)
    if not m:
        return ()
    P = pim(m)

    def has_desc0(x):
        for z in range(x + 1, len(m)):
            j = z
            while j != -1:
                if j == x:
                    return True
                j = P[j][0]
        return False

    def deep(x, c):
        d = has_desc0(x)
        mk = any(c[y] > 0 for y in range(2, Y))
        return {'desc': d, 'mark': mk, 'both': d or mk}[mode]

    out = []
    base = 0
    for b in _blocks(m):
        t = max((_topt(c) for c in b), default=-1)
        if t <= 0:
            out.extend(b); base += len(b); continue
        out.extend(diag('DBMS', t, Y))
        for i, c in enumerate(b):
            o1 = (t - 1) if deep(base + i, c) else 0
            col = [c[0] + t] + [c[1] + o1 if Y > 1 else 0] + list(c[2:])
            out.append(tuple(col[:Y]))
        base += len(b)
    return tuple(out)


# ================================================================ R23（現時点の最良）
# 設計:
#   1. 階段（影の列）: 行 y (y>=1) の親になる列は DBMS では「行 y-1 で 1 段深い影」で
#      なければならない。足りなければ影を挿入する（親ごとに 1 回、使い回す）。
#   2. 深さ（レベル）: 影を何段まで使うかは列ごとに変わる。実測すると
#      **分岐するのは (a,1,0) 型の列だけ**で、他は常に t 段（浅い方）。
#      (a,1,0) (a>=2) は「次の列」で決まる（シートで曖昧 0.66%）。
#   3. 縮約: BMS は「コピー 1 個 + 印」で書くところを DBMS は「印」だけで書くので、
#      出力に逐語重複が出る。標準形になるまで重複区間を 1 つずつ落とす。
def _blockctx(m: Mat, x: int):
    """列 x が属する行 0 ブロックの中で、x より前／後の行 1 値の最大。"""
    L = len(m)
    b = 0
    for i in range(x + 1):
        if m[i][0] == 0:
            b = i
    nb = L
    for i in range(x + 1, L):
        if m[i][0] == 0:
            nb = i
            break
    pm = max([m[z][1] for z in range(b, x)], default=0)
    lm = max([m[z][1] for z in range(x + 1, nb)], default=0)
    return pm, lm


def is_anchor(n) -> bool:
    """次の列が「アンカー」（新しい加算ユニットの頭 = 対角上の列）か。"""
    return n is not None and n[0] == n[1] and n != (1, 1, 1)


def is_anchor1(c) -> bool:
    """アンカー列 (1,1,0)（新しい加算ユニットの頭）か。"""
    return c[0] == 1 and len(c) > 1 and c[1] == 1 and (len(c) < 3 or c[2] == 0)


def is_branching(c) -> bool:
    """深さが分岐する列か。実測では (a,1,0) 型 (a>=2) だけが分岐する。"""
    return len(c) > 2 and c[1] == 1 and c[2] == 0 and c[0] >= 2


def hi_block(m, x) -> bool:
    """x の属するブロック（直前のアンカー以降）に行 2 を使う列があるか。
    W_(w^2) 系の regime にいるかどうかの目印。"""
    b = max([q for q in range(x)
             if len(m[q]) > 1 and m[q][0] == m[q][1] and m[q][0] >= 1], default=0)
    return any(len(m[z]) > 2 and m[z][2] > 0 for z in range(b + 1, x))


def is_repeat(m, x) -> bool:
    """m[..x] の末尾が、その直前の同じ長さの区間の逐語コピーか。
    コピーされた区間は、もとの区間と同じ深さで書かれる。"""
    for L in range(1, (x + 1) // 2 + 1):
        if m[x - 2 * L + 1:x - L + 1] == m[x - L + 1:x + 1]:
            return True
    return False


def spent_level(m: Mat, x: int, lv: int) -> bool:
    """直前の分岐列（＝掛け算の区切り）から x までに、段 lv の列（行 2 が 0）を
    すでに 2 本以上使っているか。使い切っていれば足場は残っていない。"""
    b = max([block_base(m, x)]
            + [q for q in range(x) if is_branching(m[q])])
    return sum(1 for z in range(b + 1, x)
               if len(m[z]) > 2 and m[z][1] == lv and m[z][2] == 0) >= 2


def is_w_col(c) -> bool:
    """「×w」の列 (k,0,0), k>=1。段を上げずに項を伸ばす。"""
    return c is not None and len(c) > 1 and c[1] == 0 and c[0] >= 1


def is_lv2_col(c) -> bool:
    """段 2 の列 (k,2,0)。行 2 は使わない。"""
    return c is not None and len(c) > 2 and c[1] == 2 and c[2] == 0


def closes_unit(nxt) -> bool:
    """次の列がこの加算ユニットを閉じるか。

    閉じるのは (a) 次が無い (b) 次がアンカー (1,1,0) (c) 次が根元 (行 0 <= 1) に戻る。
    閉じるなら、この分岐列が名指すのは段 1 の対象なので浅い。
    """
    if nxt is None:
        return True
    if is_anchor1(nxt):
        return True
    return len(nxt) > 2 and nxt[0] <= 1 and nxt[2] == 0


def at_unit_edge(nxt, prev) -> bool:
    """加算ユニットの端か（＝この分岐列の前か後ろにユニットの切れ目がある）。"""
    return prev is None or closes_unit(nxt)


def ladder_spent(c, nxt, pv, spent) -> bool:
    """段 2 の梯子を使い切ったあと、次が段 1 以下の続きの列なら、
    掛けている相手は段 1（w のべき）なので浅い。"""
    return (spent and is_lv2_col(pv) and nxt is not None and len(nxt) > 2
            and nxt[0] <= c[0] + 1 and nxt[1] <= 1 and nxt[2] == 0)


def after_w(nxt, prev, pv, hi):
    """直前が「×w」の列 (k,0,0) で、この分岐列がユニットの端にあるときの段。

    ×w は段を上げないので、ふつうは段が 1 に落ちる（浅い）。
    ただし W_(w^2) 系のブロックで直前の分岐列が深かったなら、×w は段の上に
    乗っているだけなので段は残る（深い）。
    該当しなければ None を返す（この規則は口を出さない）。
    """
    if not (is_w_col(pv) and at_unit_edge(nxt, prev)):
        return None
    return 1 if (hi and prev == 1) else 0


def closes_hi_unit(c, nxt, pv, pv2, hi, rep) -> bool:
    """W_(w^2) 系で (c0,2,1)(c0,2,0) と積んだ直後の (c0,1,0) は、
    次がアンカー (1,1,1) なら段を上げずに閉じる。
    ただしその区間が直前の逐語コピーなら、もとの深さを引き継ぐ。"""
    return (hi and not rep and nxt is not None and len(nxt) > 2
            and nxt[:3] == (1, 1, 1)
            and pv is not None and len(pv) > 2 and pv[:3] == (c[0], 2, 0)
            and pv2 is not None and len(pv2) > 2 and pv2[:3] == (c[0], 2, 1))


def depth_rule(c, nxt, prev, pv=None, hi=False, pv2=None, rep=False,
               spent=False) -> int:
    """分岐列 c が名指す対象の段（0=段 1 / 1=段 2）。

    **深いのが既定**。BMS は段を梯子で綴るので、綴りが続いていれば段 2 を名指している。
    浅くなるのは「段が落ちる／落ちたままである」合図が出たときだけ:

      1. prev == 0        直前の分岐列が浅い（ユニット内では段は戻らない）
      2. after_w          ユニットの端で直前が「×w」なら段は 1 に落ちる
                          （W_(w^2) 系で直前が深いときだけ段が残る）
      3. closes_unit      次の列がこの加算ユニットを閉じる
      4. ladder_spent     段 2 の梯子を使い切っていて、次は段 1 の続き
      5. closes_hi_unit   W_(w^2) 系で段を上げずにユニットを閉じる形

    状態 prev は直前の分岐列で選んだ深さ。アンカー (1,1,0) で 0 に戻る（`depths`）。
    """
    if not is_branching(c):
        return 0
    if prev == 0:
        return 0
    v = after_w(nxt, prev, pv, hi)
    if v is not None:
        return v
    if closes_unit(nxt):
        return 0
    if ladder_spent(c, nxt, pv, spent):
        return 0
    if closes_hi_unit(c, nxt, pv, pv2, hi, rep):
        return 0
    return 1

def block_base(m: Mat, x: int) -> int:
    """x の属する「段の regime」を開いた列の位置。

    行 2 の印を立てて段 2 の梯子を開く列 (a,1,1) 型（行 1 <= 行 2）か、
    行 2 を使わないときの対角列 (k,k,0) のうち、直近のもの。"""
    for q in range(x - 1, 0, -1):
        c = m[q]
        if len(c) > 2 and c[2] >= 1 and c[1] <= c[2]:
            return q
        if len(c) > 1 and c[0] == c[1] and c[0] >= 1:
            return q
    return 0


def relay_site(m: Mat, P, x: int, t: int) -> bool:
    """「梯子の敷き直し」が要るか。

    BMS では ×psi_W(W) を (a,1,0)(a+1,2,0) と綴る。ふつうはその (a,1,0) の像を
    足場にして次の段を書けばよいが、掛けられる側が W^2 のように **同じ段を
    2 本以上使い切っている** ときは足場が残っていない。このとき DBMS は
    梯子を一から敷き直す（前の段の写しを並べ直す）。

    判定は BMS 側だけで済む:
      p1 = 行 1 の親、pc = m[p1] として
      (1) 同じブロックに (pc[0], pc[1]+1, 0) がすでにある   … 足場が使われた
      (2) 同じブロックの行 pc[1]+1 の列（行 2 が 0）が 2 本以上 … 使い切っている
    """
    if t != 1:
        return False
    p1 = P[x][1]
    if p1 <= 0:
        return False
    pc = m[p1]
    if len(pc) < 3 or pc[2] != 0:
        return False
    b = block_base(m, p1)
    tgt = (pc[0], pc[1] + 1, 0)
    if not any(len(m[z]) > 2 and m[z][:3] == tgt for z in range(b, p1)):
        return False
    n = sum(1 for z in range(b, p1)
            if len(m[z]) > 2 and m[z][1] == pc[1] + 1 and m[z][2] == 0)
    if n < 2:
        return False
    # 足場を使い切った列は、そのブロックの一番上になければならない
    if pc[0] < max(m[z][0] for z in range(b, p1)):
        return False
    # かつ、その列自身は regime の根から段 1 を取っている（途中で入れ子に
    # なっていない）ことが要る
    return P[p1][1] <= b


_ABSORB = True     # 実験用。_stair 内の吸収を切って効果を測るためのつまみ


def _stair(m: Mat, Y: int, depth, relay: bool = True) -> Mat:
    """階段を組む。列を 1 本書くたびに末尾の「吸収」を試し、
    消えた列を参照している img/sh を写像し直す（後続の列が縮約後の状態を見る）。"""
    P = pim(m)
    out: list = []
    img: list = [None] * len(m)
    sh: dict = {}
    relaid: dict = {}         # 敷き直した (p1,lvl) -> 写しの開始位置
    anchors: set = set()      # ブロックのアンカー (k,k,...) の像
    realimg: list = []        # 実際の列の像 (out の位置, もとの列 x)

    def remap(f):
        for i in range(len(img)):
            if img[i] is not None:
                img[i] = f(img[i])
        for k in list(sh):
            sh[k] = f(sh[k])
        for i, z in enumerate(realimg):
            realimg[i] = (f(z[0]), z[1])
        for k in list(relaid):
            relaid[k] = f(relaid[k])
        a = set(f(z) for z in anchors)
        anchors.clear(); anchors.update(a)

    def absorb_tail():
        if not _ABSORB:
            return False
        n = len(out)
        if n < 2:
            return False
        j = n - 1
        Q = out[j]
        for i in range(j - 1, -1, -1):
            Pc = out[i]
            if len(Pc) < 2 or len(Q) < 2 or Pc[0] != Q[0] or Q[1] <= Pc[1]:
                continue
            L = j - i - 1
            if L <= 0 or i - L < 0:
                continue
            if out[i - L:i] == out[i + 1:j]:
                keep = out[:]
                del out[i:j]
                if not isstd(tuple(out), 'DBMS'):
                    out[:] = keep      # 縮めると標準形でなくなるならやめる
                    continue

                def g(z, i=i, j=j, L=L):
                    if z < i:
                        return z
                    if z < j:
                        return z - (L + 1) if z > i else i - L
                    return z - (j - i)
                remap(g)
                return True
        return False

    def shadow(p, y):
        if y <= 0:
            return img[p]
        k = (p, y)
        if k in sh:
            return sh[k]
        s = shadow(p, y - 1)
        if out[s][y - 1] >= 1:
            r = s
        else:
            out.append(tuple(out[s][z] + 1 if z < y else 0 for z in range(Y)))
            r = len(out) - 1
        sh[k] = r
        return r

    for x, c in enumerate(m):
        nz = [y for y in range(Y) if c[y] > 0]
        if not nz:
            out.append(tuple([0] * Y)); img[x] = len(out) - 1
            realimg.append((len(out) - 1, x))
            continue
        t = nz[-1]
        lvl = min(Y - 1, t + depth(x, c))
        p1 = P[x][1] if t >= 1 else -1
        if (p1 > 0 and (p1, lvl) not in sh and img[p1] is not None
                and len(out[img[p1]]) > 1 and out[img[p1]][1] >= 1
                and relay and relay_site(m, P, x, t)):
            s0 = img[p1]; L = out[s0][1]
            bb = block_base(m, p1)
            tg = [oi for oi, xx in realimg
                  if oi < s0 and xx > bb and out[oi][1] == L]
            if tg:
                j = tg[0]
                chain = []; k = j; st = len(out)
                while k > 0:
                    pk = max([q for q in range(k) if out[q][0] < out[k][0]],
                             default=None)
                    if pk is None:
                        break
                    if (out[pk][1] < out[j][1]
                            and all(out[q][0] > out[pk][0]
                                    for q in range(pk + 1, len(out)))):
                        break
                    chain.append(pk); k = pk
                for q in reversed(chain):
                    out.append(out[q])
                out.append(out[j]); base = len(out) - 1
                sh[(p1, lvl)] = base
                relaid[(p1, lvl)] = st
                out.append(tuple(out[base][y] + 1 if y <= t else 0
                                 for y in range(Y)))
                img[x] = len(out) - 1
                realimg.append((len(out) - 1, x))
                if len(c) > 1 and c[0] == c[1] and c[0] >= 1:
                    anchors.add(img[x])
                while absorb_tail():
                    pass
                continue
        base = shadow(P[x][t], lvl) if P[x][t] != -1 else None
        T = [0] * Y
        for y in range(1, t + 1):
            p = P[x][y]
            T[y] = out[shadow(p, y)][y] + 1 if p != -1 else 0
        p0 = P[x][0]
        T[0] = out[img[p0]][0] + 1 if p0 != -1 else 0
        # 敷き直しで捨てられた側に行 0 の親がいるなら、写しのほうを使う
        if (p1 > 0 and (p1, lvl) in relaid and p0 != -1
                and img[p0] < relaid[(p1, lvl)]):
            T[0] = out[base][0] + 1
        if base is not None:
            for y in range(0, t + 1):
                T[y] = max(T[y], out[base][y] + 1)
        out.append(tuple(T)); img[x] = len(out) - 1
        realimg.append((len(out) - 1, x))
        if len(c) > 1 and c[0] == c[1] and c[0] >= 1:
            anchors.add(img[x])
        while absorb_tail():
            pass
    return tuple(out)


def _absorb_cands(Z: Mat):
    """吸収: Z = A ++ [P] ++ B ++ [Q] で B が A の接尾辞のコピー、
    Q が P を上書きする（行 0 が同じで行 1 が大きい）なら A ++ [Q] に縮む。

    BMS は「レベル 1 の印を書いてから、レベルを上げ直して書き直す」が、
    DBMS は最初から上のレベルで書くので、この形の重複が出る。
    """
    n = len(Z)
    for j in range(n - 1, 0, -1):
        Q = Z[j]
        for i in range(j - 1, -1, -1):
            P = Z[i]
            if P[0] != Q[0] or Q[1] <= P[1]:
                continue
            L = j - i - 1
            if L <= 0 or i - L < 0:
                continue
            if Z[i - L:i] == Z[i + 1:j]:
                yield Z[:i] + Z[j:]


def dedup(Z: Mat, limit: int = 40) -> Mat:
    """標準形になるまで縮約する。逐語重複の削除 → 吸収 の順に試す。"""
    for _ in range(limit):
        if isstd(Z, 'DBMS'):
            return Z
        nxt = None
        n = len(Z)
        for L in range(n // 2, 0, -1):
            for i in range(n - L, L - 1, -1):
                if Z[i - L:i] == Z[i:i + L]:
                    cand = Z[:i] + Z[i + L:]
                    if isstd(cand, 'DBMS'):
                        return cand
                    if nxt is None:
                        nxt = cand
        for cand in _absorb_cands(Z):
            if isstd(cand, 'DBMS'):
                return cand          # 吸収は標準形になるときだけ使う
        if nxt is None:
            return Z
        Z = nxt
    return Z


@lru_cache(maxsize=200000)
def convert(m: Mat, Y: int | None = None) -> Mat:
    """BMS(BM4) 標準形 -> DBMS 標準形。

    BM4-Analysis シートの 3 行以下の全 1621 行に一致（Y=1 28、Y=2 236、Y=3 1357）。
    """
    if Y is None:
        Y = rows(m)
    return R23(m, Y)

def depths(m: Mat):
    """各列の深さ（0=浅い / 1=深い）を規則で決める。"""
    prev = [None]
    out = []
    for x, c in enumerate(m):
        if is_anchor1(c):
            prev[0] = 0            # アンカーを通ると加算ユニットが変わるのでリセット
        if not is_branching(c):
            out.append(0); continue
        v = depth_rule(c, m[x + 1] if x + 1 < len(m) else None, prev[0],
                       m[x - 1] if x > 0 else None, hi_block(m, x),
                       m[x - 2] if x > 1 else None, is_repeat(m, x),
                       spent_level(m, x, c[1] + 1))
        prev[0] = v
        out.append(v)
    return out


def R23(m: Mat, Y: int | None = None) -> Mat:
    """規則で深さを決めて階段を組む。出力が DBMS 標準形にならないときだけ、
    深さを 1 箇所ずつ（足りなければ 2 箇所）ひっくり返して探し直す。
    標準形であることは順序数側から来る要請なので、これは規則の後始末にあたる。"""
    if Y is None:
        Y = rows(m)
    if not m:
        return ()
    ds = depths(m)
    Z = dedup(_stair(m, Y, lambda x, c: ds[x]))
    if isstd(Z, 'DBMS'):
        return Z
    # 1 列短い行列の像より大きくなければならない（真の接頭辞は小さいので）
    lo = None
    if len(m) > 1 and isstd(m[:-1], 'BMS'):
        try:
            lo = convert(m[:-1], Y)
        except Exception:
            lo = None

    def okay(W):
        return isstd(W, 'DBMS') and (lo is None or cmpmat(lo, W) < 0)

    br = [x for x, c in enumerate(m) if is_branching(c)]
    for k in (1, 2):
        cands = []
        flips = ([(i,) for i in br] if k == 1
                 else [(i, j) for i in br for j in br if j > i])
        for f in flips:
            e = list(ds)
            for i in f:
                e[i] ^= 1
            try:
                W = dedup(_stair(m, Y, lambda x, c, e=e: e[x]))
            except Exception:
                continue
            if okay(W):
                cands.append(W)
        if cands:
            # 条件を満たすもののうち最小を取る（規則は上に振れやすい）
            best = cands[0]
            for W in cands[1:]:
                if cmpmat(W, best) < 0:
                    best = W
            return best
    return Z


def _R23_old(m: Mat, Y: int | None = None) -> Mat:
    if Y is None:
        Y = rows(m)
    if not m:
        return ()
    prev = [None]

    def dep(x, c):
        if is_anchor1(c):
            prev[0] = 0            # アンカーを通ると加算ユニットが変わるのでリセット
        if not is_branching(c):
            return 0
        v = depth_rule(c, m[x + 1] if x + 1 < len(m) else None, prev[0],
                       m[x - 1] if x > 0 else None, hi_block(m, x),
                       m[x - 2] if x > 1 else None, is_repeat(m, x),
                       spent_level(m, x, c[1] + 1))
        prev[0] = v
        return v
    return dedup(_stair(m, Y, dep))
