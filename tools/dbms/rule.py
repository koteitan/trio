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


# ---------------------------------------------------------------- R7
from core import pim


# ---------------------------------------------------------------- R8 = R7 + 余分なコピーの縮約
from core import expand, isstd, pim as _pim


# ---------------------------------------------------------------- R9 = R7 + 一般の重複縮約
from core import cmpmat


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
    """**廃止**。かつては「段 2 の梯子を使い切ったら浅い」としていたが、
    共終検査で誤りと判明した。正しくは格上げ自体は起き、梯子を敷き直す。
    外すと共終検査の不合格が 291 -> 212 に減る（シートは 1621/1621 のまま）。"""
    return False


def after_w(nxt, prev, pv, hi, pv_new_term=False):
    """直前が「×w」の列 (k,0,0) で、この分岐列がユニットの端にあるときの段。

    ×w は段を上げないので、ふつうは段が 1 に落ちる（浅い）。
    ただし W_(w^2) 系のブロックで直前の分岐列が深く、かつその ×w が
    **いまの項の続き**なら、×w は段の上に乗っているだけなので段は残る（深い）。
    ×w が根から生えて新しい加算項を始めているなら段は残らない。
    該当しなければ None を返す（この規則は口を出さない）。
    """
    if not (is_w_col(pv) and at_unit_edge(nxt, prev)):
        return None
    return 1 if (hi and prev == 1 and not pv_new_term) else 0


def closes_hi_unit(c, nxt, pv, pv2, hi, rep) -> bool:
    """W_(w^2) 系で (c0,2,1)(c0,2,0) と積んだ直後の (c0,1,0) は、
    次がアンカー (1,1,1) なら段を上げずに閉じる。
    ただしその区間が直前の逐語コピーなら、もとの深さを引き継ぐ。"""
    return (hi and not rep and nxt is not None and len(nxt) > 2
            and nxt[:3] == (1, 1, 1)
            and pv is not None and len(pv) > 2 and pv[:3] == (c[0], 2, 0)
            and pv2 is not None and len(pv2) > 2 and pv2[:3] == (c[0], 2, 1))


def depth_rule(c, nxt, prev, pv=None, hi=False, pv2=None, rep=False,
               spent=False, pv_new_term=False) -> int:
    """分岐列 c が名指す対象の段（0=段 1 / 1=段 2）。

    **深いのが既定**。BMS は段を梯子で綴るので、綴りが続いていれば段 2 を名指している。
    浅くなるのは「段が落ちる／落ちたままである」合図が出たときだけ:

      1. prev == 0        直前の分岐列が浅い（ユニット内では段は戻らない）
      2. after_w          ユニットの端で直前が「×w」なら段は 1 に落ちる
                          （W_(w^2) 系で直前が深いときだけ段が残る）
      3. closes_unit      次の列がこの加算ユニットを閉じる
      5. closes_hi_unit   W_(w^2) 系で段を上げずにユニットを閉じる形

    状態 prev は直前の分岐列で選んだ深さ。アンカー (1,1,0) で 0 に戻る（`depths`）。
    """
    if not is_branching(c):
        return 0
    if prev == 0:
        return 0
    v = after_w(nxt, prev, pv, hi, pv_new_term)
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


class _Staircase:
    """BMS の列を 1 本ずつ DBMS の列に写していく組み立て器。

    持ち物:
      out      いままでに書いた DBMS の列
      img[x]   BMS の列 x の像の位置
      sh       影の列のキャッシュ (親, 段) -> 位置
      relaid   敷き直した (親, 段) -> 写しの開始位置
      anchors  ブロックのアンカー (k,k,..) の像の位置
      realimg  実際の列の像 (位置, もとの列 x)。影の列は含まない
    """

    def __init__(self, m: Mat, Y: int, depth, relay: bool = True):
        self.m, self.Y, self.depth, self.relay = m, Y, depth, relay
        self.P = pim(m)
        self.out: list = []
        self.img: list = [None] * len(m)
        self.sh: dict = {}
        self.relaid: dict = {}
        self.anchors: set = set()
        self.realimg: list = []

    # ------------------------------------------------------------ 組み立て
    def run(self) -> Mat:
        for x, c in enumerate(self.m):
            nz = [y for y in range(self.Y) if c[y] > 0]
            if not nz:
                self._emit(tuple([0] * self.Y), x, c)
            else:
                t = nz[-1]
                lvl = min(self.Y - 1, t + self.depth(x, c))
                p1 = self.P[x][1] if t >= 1 else -1
                if not self._relay(x, c, t, lvl, p1):
                    self._normal(x, c, t, lvl, p1)
            while self._absorb_tail():
                pass
        return tuple(self.out)

    def _emit(self, col, x, c):
        """列を 1 本書いて、それを BMS の列 x の像として記録する。"""
        self.out.append(col)
        self.img[x] = len(self.out) - 1
        self.realimg.append((len(self.out) - 1, x))
        if len(c) > 1 and c[0] == c[1] and c[0] >= 1:
            self.anchors.add(self.img[x])

    # ------------------------------------------------------------ 影の列
    def _shadow(self, p, y):
        """列 p の像を、段 y まで届く足場に持ち上げる。足りなければ影の列を挿す。"""
        if y <= 0:
            return self.img[p]
        k = (p, y)
        if k in self.sh:
            return self.sh[k]
        s = self._shadow(p, y - 1)
        if self.out[s][y - 1] >= 1:
            r = s
        else:
            self.out.append(tuple(self.out[s][z] + 1 if z < y else 0
                                  for z in range(self.Y)))
            r = len(self.out) - 1
        self.sh[k] = r
        return r

    # ------------------------------------------------------------ ふつうの列
    def _normal(self, x, c, t, lvl, p1):
        out, P = self.out, self.P
        base = self._shadow(P[x][t], lvl) if P[x][t] != -1 else None
        T = [0] * self.Y
        for y in range(1, t + 1):
            p = P[x][y]
            T[y] = out[self._shadow(p, y)][y] + 1 if p != -1 else 0
        p0 = P[x][0]
        T[0] = out[self.img[p0]][0] + 1 if p0 != -1 else 0
        # 敷き直しで捨てられた側に行 0 の親がいるなら、写しのほうを使う
        if (p1 > 0 and (p1, lvl) in self.relaid and p0 != -1
                and self.img[p0] < self.relaid[(p1, lvl)]):
            T[0] = out[base][0] + 1
        if base is not None:
            for y in range(0, t + 1):
                T[y] = max(T[y], out[base][y] + 1)
        self._emit(tuple(T), x, c)

    # ------------------------------------------------------------ 敷き直し
    def _relay(self, x, c, t, lvl, p1) -> bool:
        """梯子を使い切っているなら、前の段の写しを並べ直してから書く。
        書いたら True。"""
        out = self.out
        if not (self.relay and p1 > 0 and (p1, lvl) not in self.sh
                and self.img[p1] is not None
                and len(out[self.img[p1]]) > 1 and out[self.img[p1]][1] >= 1
                and relay_site(self.m, self.P, x, t)):
            return False
        s0 = self.img[p1]
        L = out[s0][1]
        bb = block_base(self.m, p1)
        tg = [oi for oi, xx in self.realimg
              if oi < s0 and xx > bb and out[oi][1] == L]
        if not tg:
            return False
        j = tg[0]
        chain = self._ancestor_chain(j)
        st = len(out)
        for q in reversed(chain):
            out.append(out[q])
        out.append(out[j])
        base = len(out) - 1
        self.sh[(p1, lvl)] = base
        self.relaid[(p1, lvl)] = st
        self._emit(tuple(out[base][y] + 1 if y <= t else 0
                         for y in range(self.Y)), x, c)
        return True

    def _ancestor_chain(self, j):
        """写し元 j を書くのに要る、行 0 の祖先鎖。まだ生きている段で止める。"""
        out = self.out
        chain = []
        k = j
        while k > 0:
            pk = max([q for q in range(k) if out[q][0] < out[k][0]], default=None)
            if pk is None:
                break
            if (out[pk][1] < out[j][1]
                    and all(out[q][0] > out[pk][0]
                            for q in range(pk + 1, len(out)))):
                break
            chain.append(pk)
            k = pk
        return chain

    # ------------------------------------------------------------ 吸収
    def _absorb_tail(self) -> bool:
        """末尾が A ++ [P] ++ B ++ [Q]（B は A の接尾辞の写し、Q は P を上書き）の形なら、
        A ++ [Q] に縮める。縮めたら True。"""
        if not _ABSORB:
            return False
        out = self.out
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
            if out[i - L:i] != out[i + 1:j]:
                continue
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
            self._remap(g)
            return True
        return False

    def _remap(self, f):
        """列が消えたので、位置を指しているもの全部を写し直す。"""
        for i in range(len(self.img)):
            if self.img[i] is not None:
                self.img[i] = f(self.img[i])
        for k in list(self.sh):
            self.sh[k] = f(self.sh[k])
        for i, z in enumerate(self.realimg):
            self.realimg[i] = (f(z[0]), z[1])
        for k in list(self.relaid):
            self.relaid[k] = f(self.relaid[k])
        a = set(f(z) for z in self.anchors)
        self.anchors.clear()
        self.anchors.update(a)


def _stair(m: Mat, Y: int, depth, relay: bool = True) -> Mat:
    return _Staircase(m, Y, depth, relay).run()

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
    P = pim(m)
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
                       spent_level(m, x, c[1] + 1),
                       x > 0 and P[x - 1][0] == 0)
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
    import itertools as _it
    for k in (1, 2, 3):
        cands = [W for W in
                 (_try(m, Y, ds, f) for f in _it.combinations(br, k))
                 if W is not None and okay(W)]
        if cands:
            # 条件を満たすもののうち最小を取る（規則は上に振れやすい）
            best = cands[0]
            for W in cands[1:]:
                if cmpmat(W, best) < 0:
                    best = W
            return best
    return Z


def _try(m, Y, ds, flips):
    e = list(ds)
    for i in flips:
        e[i] ^= 1
    try:
        return dedup(_stair(m, Y, lambda x, c, e=e: e[x]))
    except Exception:
        return None
