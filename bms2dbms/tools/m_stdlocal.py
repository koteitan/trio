"""3 行 DBMS 標準形の**局所判定**を探す（2026-08-27）。

いまの `core.isstd(m,'DBMS')` は対角から `reach()` で降りる**大域**判定。
Lean に載せるには「列の近傍だけを見る条件の連言」で書きたい。

用語
----
colOK(c, prev) : 列 c=(a,b,z) が  a <= prev の行0 +1（先頭なら a=0）,
                 b <= max(a-1,0),  z <= max(b-1,0)  を満たす。gen3 の枝刈りと同じ。
                 **標準形の必要条件**（`colok` コマンドで <=6 列を全数確認）。
正例 : DBMS 標準形。
負例 : colOK を全部満たし、真の接頭辞はすべて標準形、しかし自身は非標準。
       ＝「ちょうど 1 列足しただけで標準形から外れた」行列。
       標準形の接頭辞は標準形なので、非標準な colOK 行列は必ずどこかの接頭辞が負例。
       よって「負例を全部弾く局所条件」は標準形性の特徴づけになる。

見つかった条件（どれも <=8 列の正例 37453 個で**違反 0**）
--------------------------------------------------------
DEPTH  : 各行 y で「値 = その行の木での入れ子の深さ」
         ＝ 行 y の親の値がちょうど 1 小さい（親が無ければ値 0）。
SIB0   : 行 0 の木で、連続する兄弟のブロックが辞書式に弱く減少する。
PARLAB : 行 0 の親の段 (W,Z) に対し自分の段 (w,z) は
         w<=W+1、w==W なら z<=Z、w==W+1 なら z<=Z+1。
RED    : 末尾列の悪い部分ブロックが「1 つ手前のブロックの delta ずらし写し」に
         なっていない（なっていれば M[n] = M'[n+1] となる短い M' があるので非標準）。
PREZ   : 行 2 を z>=1 にできるのは、対角の位置にいるか、同じ根ブロックの前の列に
         行2 >= z があるとき。
COPY   : 長さ 2 以上の隣り合う写しブロックの直後の列は「3 つ目の写しの頭」以下。

成績（すべて正例で違反 0）
  列数 | 正例     | 負例     | 弾けなかった負例 | 捕捉
  <=6  |    555   |    432   |      1  | 99.77%
  <=7  |   4045   |   3704   |     26  | 99.30%
  <=8  |  37453   |  37222   |    355  | 99.05%
  <=9  | 422582   | 433609   |   4334  | 99.00%

つまり「必要条件」としては <=9 列で完全（正例 422582 個で違反 0）、
「十分条件」としては 1% 足りない。残りは 88% が 行2>=1 を含む形
（<=8 列の残り 355 件のうち 313 件が (3,2,1) を含む）。

効かなかったもの（記録）
  noAdj3   : BMS 2 行の禁止形。DBMS の対角自身が違反する。
  PRE(行1) : 「段を上げるには先例が要る」。反例
             (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,2,0)(5,3,0) は標準形だが 行1=3 の先例が無い。
  SIBT_1/2 : 行 1・行 2 の木でも兄弟が減少する、は成り立たない。
  k 列窓の禁止形の表: 窓の値は行列が伸びるといくらでも大きくなるので有限にならない。
             <7 列の正例から作った 3 列窓の表は、7 列の正例 3490 個のうち 2531 個を誤って弾く。

使い方
------
  python3 m_stdlocal.py colok [lim]    colOK が標準形の必要条件かの全数確認
  python3 m_stdlocal.py count [lim]    正例・負例の件数
  python3 m_stdlocal.py win   [lim] k  「k 列窓の禁止形」表がどこまで効くか（＝効かない）
  python3 m_stdlocal.py check [lim]    4 条件の採点（正例の違反数・負例の捕捉率）
  python3 m_stdlocal.py rest  [lim] n  取り逃した負例を n 個表示
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse, show, isstd, pim, expand

VER = 'DBMS'


# ================================================================ 生成
def colok_cols(prev):
    """prev の次に置ける列（colOK を満たすもの）を全部。prev=None は先頭。"""
    amax = (prev[0] + 1) if prev is not None else 0
    out = []
    for a in range(amax + 1):
        for b in range(max(a - 1, 0) + 1):
            for z in range(max(b - 1, 0) + 1):
                out.append((a, b, z))
    return out


def check_colok(m):
    for x, c in enumerate(m):
        a = c[0]
        if x == 0:
            if a != 0:
                return False
        elif a > m[x - 1][0] + 1:
            return False
        if c[1] > max(a - 1, 0) or c[2] > max(c[1] - 1, 0):
            return False
    return True


def gen_pos_neg(lim):
    """<=lim 列の正例と負例を全部。"""
    cur = [()]
    pos, neg = [], []
    for _ in range(lim):
        nxt = []
        for S in cur:
            prev = S[-1] if S else None
            for c in colok_cols(prev):
                T = S + (c,)
                if isstd(T, VER):
                    nxt.append(T)
                else:
                    neg.append(T)
        cur = nxt
        pos.extend(nxt)
    return pos, neg


def gen_free(lim):
    """colOK を課さずに <=lim 列の標準形を全部（colOK の必要性の確認用）。
       対角の上界 b[x][y] <= max(x-y,0) だけを使う。"""
    cur = [()]
    out = []
    for x in range(lim):
        nxt = []
        for S in cur:
            for a in range(x + 1):
                for b in range(max(x - 1, 0) + 1):
                    for z in range(max(x - 2, 0) + 1):
                        T = S + ((a, b, z),)
                        if isstd(T, VER):
                            nxt.append(T)
        cur = nxt
        out.extend(nxt)
    return out


# ================================================================ 条件 1: DEPTH
def depth_ok(m):
    """各行 y で「値 = その行の木での入れ子の深さ」。
       行 y の親 P[x][y] の値がちょうど 1 小さい（親が無いなら値 0）。"""
    if not m:
        return True
    P = pim(m)
    Y = len(m[0])
    for x in range(len(m)):
        for y in range(Y):
            p = P[x][y]
            want = 0 if p < 0 else m[p][y] + 1
            if m[x][y] != want:
                return False
    return True


# ================================================================ 条件 2: SIB0
def lexcmp(a, b):
    """列を平らに並べた辞書式（core.cmpmat と同じ規約。接頭辞なら長い方が大）。"""
    fa = [v for c in a for v in c]
    fb = [v for c in b for v in c]
    for u, v in zip(fa, fb):
        if u != v:
            return 1 if u > v else -1
    if len(fa) != len(fb):
        return 1 if len(fa) > len(fb) else -1
    return 0


def sib0_pairs(m):
    """行 0 の木の連続する兄弟の対 (a, b, ea, eb)。
       行 0 の値は深さなので、部分木は連続した区間になる:
       x の部分木の終わり = x より後ろで最初に 行0 <= m[x][0] になる位置。"""
    n = len(m)
    end = [n] * n
    for x in range(n):
        for i in range(x + 1, n):
            if m[i][0] <= m[x][0]:
                end[x] = i
                break
    out = []
    for x in range(n):
        j = end[x]
        if j < n and m[j][0] == m[x][0]:
            out.append((x, j, j, end[j]))
    return out


def sib0_ok(m, report=False):
    """SIB0: 連続する兄弟のブロックが辞書式に弱く減少する。"""
    for a, b, _, eb in sib0_pairs(m):
        if lexcmp(m[a:b], m[b:eb]) < 0:
            return (a, b) if report else False
    return None if report else True


# ================================================================ 条件 3: PARLAB
def parlab_ok(m):
    """行 0 の親の段 (W,Z) に対し自分の段 (w,z) は
       w<=W+1、 w==W なら z<=Z、 w==W+1 なら z<=Z+1。親が無ければ段は (0,0)。"""
    if not m:
        return True
    P = pim(m)
    for x in range(len(m)):
        w, z = m[x][1], m[x][2]
        p = P[x][0]
        if p < 0:
            if (w, z) != (0, 0):
                return False
            continue
        W, Z = m[p][1], m[p][2]
        if w > W + 1:
            return False
        if w == W and z > Z:
            return False
        if w == W + 1 and z > Z + 1:
            return False
    return True


# ================================================================ 条件 4: RED
def red_at(m):
    """末尾列の悪い部分ブロック B が、その 1 つ手前のブロック B' の
       「delta ずらし写し」になっているか。なっていれば
       M' = M[:r] ++ [末尾列 - delta] が M[n] = M'[n+1] を満たすので M は非標準。
       返り値: 縮められるなら M'、無理なら None。"""
    if not m:
        return None
    x = len(m) - 1
    Y = len(m[0])
    c = m[x]
    if all(v == 0 for v in c):
        return None
    t = max(y for y in range(Y) if c[y] > 0)
    P = pim(m)
    r = P[x][t]
    if r < 0:
        return None
    bp = x - r
    if r - bp < 0:
        return None
    delta = [(c[y] - m[r][y]) if y < t else 0 for y in range(Y)]
    for i in range(bp):
        a, b = m[r - bp + i], m[r + i]
        for y in range(Y):
            if b[y] != a[y] + delta[y]:
                return None
    cc = tuple(c[y] - delta[y] for y in range(Y))
    if any(v < 0 for v in cc):
        return None
    out = tuple(list(m[:r]) + [cc])
    if not check_colok(out):
        return None          # 縮めた先が列の形を満たさないなら縮められない
    return out


def red_ok(m):
    """どの接頭辞でも RED が起きない。"""
    for k in range(1, len(m) + 1):
        if red_at(m[:k]) is not None:
            return False
    return True


# ================================================================ 条件 5: PREZ
def rootblock(m, x):
    """x が属する「行 0 の根ブロック」の先頭（＝x 以下で最後に 行0==0 になる位置）。"""
    for i in range(x, -1, -1):
        if m[i][0] == 0:
            return i
    return 0


def prez_ok(m):
    """PREZ: 行 2 を z>=1 にできるのは
         (a) その列が対角の位置にいる（行0 == 行1+1 かつ 行2 == 行1-1）か、
         (b) 同じ根ブロックの中の前の列に 行2 >= z があるとき。
       行 1 についての同じ主張（PREW）は**成り立たない**（下の pre_ok を参照）。"""
    for x in range(len(m)):
        d, w, z = m[x][0], m[x][1], m[x][2]
        if z < 1:
            continue
        if d == w + 1 and z == w - 1:
            continue
        j = rootblock(m, x)
        if not any(m[y][2] >= z for y in range(j, x)):
            return False
    return True


# ================================================================ 条件 6: COPY
def copy_ok(m):
    """COPY（写しの上限）: 長さ bp>=2 の隣り合うブロック B = m[i:j], B2 = m[j:k] が
       B2 = B + delta（列ごとに同じ delta、delta[0]>=1、delta の各成分 >= 0）という
       「写し」になっているとき、写しの直後の列 m[k] は
         m[j] + delta   （＝ 3 つ目の写しの頭）
       以下でなければならない（列は (行0,行1,行2) の辞書式で比べる）。

       意味: 展開が作る写しは、もとのブロックの続き方をなぞる。もとで閉じていた柱を
       写しでは開けない。

       注（実測した境界）:
       * bp=1 まで許すと DBMS の対角 (0,0,0)(1,0,0)(2,1,0) 自身が違反する
         （<=8 列の正例 37453 個中 36968 個が違反）。bp>=2 が要る。
       * delta の成分に負を許すと正例違反が出る（<=7 列で 11 個、すべて delta[1]=-1）。"""
    n = len(m)
    for k in range(2, n):
        for bp in range(2, k // 2 + 1):
            i, j = k - 2 * bp, k - bp
            d = (m[j][0] - m[i][0], m[j][1] - m[i][1], m[j][2] - m[i][2])
            if d[0] < 1 or d[1] < 0 or d[2] < 0:
                continue
            ok = True
            for t in range(bp):
                a, b = m[i + t], m[j + t]
                if b[0] != a[0] + d[0] or b[1] != a[1] + d[1] or b[2] != a[2] + d[2]:
                    ok = False
                    break
            if not ok:
                continue
            if m[k] > (m[j][0] + d[0], m[j][1] + d[1], m[j][2] + d[2]):
                return False
    return True


CONDS = [('DEPTH', depth_ok), ('SIB0', sib0_ok), ('PARLAB', parlab_ok),
         ('RED', red_ok), ('PREZ', prez_ok), ('COPY', copy_ok)]


def local_std(m):
    """局所条件だけによる標準形判定（十分性は未証明。<=8 列で負例の 99.05% を弾く）。"""
    return check_colok(m) and all(f(m) for _, f in CONDS)


# ================================================================ 効かなかった条件（記録）
def noadj3(m, y):
    """Lean の `adj3`（BMS 2 行の禁止形）を行 y に一般化したもの。
       **DBMS には使えない**: DBMS の対角 (0,0,0)(1,0,0)(2,1,0) 自身が違反する
       （2 行 DBMS の <=8 列の標準形 9486 個のうち 9001 個が違反）。"""
    for i in range(len(m) - 2):
        a, b, c = m[i], m[i + 1], m[i + 2]
        if a[0] < b[0] < c[0] and b[y] == a[y] and c[y] == b[y] + 1:
            return False
    return True


def vis(m, x):
    """x から左に見える列（＝スタックに載っている祖先＋各段の弟たち）。
       y in vis(x) ⟺ y<x かつ (y,x] のどの列も 行0 が m[y][0] 以上。"""
    out = []
    lo = m[x][0]
    for y in range(x - 1, -1, -1):
        if m[y][0] <= lo:
            out.append(y)
            lo = m[y][0]
    return out


def pre_ok(m):
    """PRE: 段を上げるには「見える範囲に先例があるか、対角の位置にいるか」。
       **強すぎる**（<=8 列の正例 37453 個のうち 1163 個を誤って弾く）。反例:
       (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,2,0)(5,3,0) は標準形だが 行1=3 の先例が無い。"""
    for x in range(len(m)):
        d, w, z = m[x][0], m[x][1], m[x][2]
        if w >= 1 or z >= 1:
            V = vis(m, x)
            if w >= 1 and d != w + 1 and not any(m[y][1] >= w for y in V):
                return False
            if z >= 1 and not (d == w + 1 and z == w - 1) \
                    and not any(m[y][2] >= z for y in V):
                return False
    return True


def kids(m, y):
    P = pim(m)
    ks = {}
    for x in range(len(m)):
        ks.setdefault(P[x][y], []).append(x)
    return ks


def term_y(m, ks, y, x):
    Y = len(m[0])
    lab = m[x][y + 1] if y + 1 < Y else 0
    return (lab, tuple(term_y(m, ks, y, c) for c in ks.get(x, [])))


def cmp_term(a, b):
    if a[0] != b[0]:
        return 1 if a[0] > b[0] else -1
    for u, v in zip(a[1], b[1]):
        c = cmp_term(u, v)
        if c:
            return c
    if len(a[1]) != len(b[1]):
        return 1 if len(a[1]) > len(b[1]) else -1
    return 0


def sibterm_ok(m, y, with_roots=None):
    """行 y の木でも「兄弟の部分項が弱く減少」を課したもの。
       **y>=1 では成り立たない**（行 1 の兄弟は 行 0 の深さが増える向きに並びうる）。
       <=7 列で y=1 は正例 50 個を誤って弾く。反例:
       (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,2,0)(3,2,1)。"""
    if not m:
        return True
    if with_roots is None:
        with_roots = (y == 0)
    ks = kids(m, y)
    for p, cs in ks.items():
        if p < 0 and not with_roots:
            continue
        for a, b in zip(cs, cs[1:]):
            if cmp_term(term_y(m, ks, y, a), term_y(m, ks, y, b)) < 0:
                return False
    return True


# ================================================================ コマンド
def cmd_colok(lim):
    t = time.time()
    g = gen_free(lim)
    bad = [m for m in g if not check_colok(m)]
    print("colOK: <=%d 列の DBMS 標準形 %d 個, colOK 違反 %d 個 (%.1fs)"
          % (lim, len(g), len(bad), time.time() - t))
    for m in bad[:10]:
        print("  ", show(m))


def cmd_count(lim):
    t = time.time()
    pos, neg = gen_pos_neg(lim)
    print("<=%d 列: 正例 %d, 負例 %d  (%.1fs)" % (lim, len(pos), len(neg), time.time() - t))
    from collections import Counter
    cp = Counter(len(m) for m in pos)
    cn = Counter(len(m) for m in neg)
    print("  列数(正/負):", " ".join("%d:%d/%d" % (i, cp.get(i, 0), cn.get(i, 0))
                                     for i in sorted(set(cp) | set(cn))))


def cmd_win(lim, k):
    """k 列窓の「禁止形の表」でどこまで行けるか。
       窓の値は行列が伸びるといくらでも大きくなるので、表は有限にならない。"""
    pos, neg = gen_pos_neg(lim)
    posS = [m for m in pos if len(m) < lim]
    P = set()
    for m in posS:
        for i in range(len(m) - k + 1):
            P.add(m[i:i + k])
    caught = short = 0
    forb = set()
    for m in neg:
        if len(m) < k:
            short += 1
            continue
        w = m[len(m) - k:]
        if w not in P:
            caught += 1
            forb.add(w)
    # 1 列長い正例が、この表で誤って弾かれないか
    newpos = 0
    neww = set()
    for m in [x for x in pos if len(x) == lim]:
        f = False
        for i in range(len(m) - k + 1):
            if m[i:i + k] not in P:
                f = True
                neww.add(m[i:i + k])
        if f:
            newpos += 1
    print("k=%d: <%d 列の正例から作った窓 %d 種、禁止窓 %d 種" % (k, lim, len(P), len(forb)))
    print("   負例の捕捉 %d/%d (%.1f%%)、短すぎ %d" %
          (caught, len(neg), 100.0 * caught / max(len(neg), 1), short))
    print("   しかし %d 列の正例 %d 個中 %d 個をこの表は誤って弾く（新しい窓 %d 種）"
          % (lim, sum(1 for x in pos if len(x) == lim), newpos, len(neww)))


def cmd_check(lim):
    t = time.time()
    pos, neg = gen_pos_neg(lim)
    print("<=%d 列: 正例 %d / 負例 %d" % (lim, len(pos), len(neg)))
    for name, f in CONDS:
        vp = sum(1 for m in pos if not f(m))
        cn = sum(1 for m in neg if not f(m))
        print("  %-7s 正例で違反 %d   負例を捕捉 %d/%d (%.1f%%)"
              % (name, vp, cn, len(neg), 100.0 * cn / max(len(neg), 1)))
    rem = [m for m in neg if all(f(m) for _, f in CONDS)]
    print("  連言: 正例で違反 %d、負例の残り %d/%d → 捕捉 %.2f%%  (%.0fs)"
          % (sum(1 for m in pos if not local_std(m)), len(rem), len(neg),
             100.0 * (1 - len(rem) / max(len(neg), 1)), time.time() - t))
    return rem


def cmd_rest(lim, n):
    rem = cmd_check(lim)
    print("  --- 取り逃した負例 %d 個 ---" % min(n, len(rem)))
    for m in rem[:n]:
        print("   ", show(m))


def main():
    a = sys.argv[1:] or ["check", "7"]
    cmd = a[0]
    n = lambda i, d: int(a[i]) if len(a) > i else d
    if cmd == "colok":
        cmd_colok(n(1, 6))
    elif cmd == "count":
        cmd_count(n(1, 7))
    elif cmd == "win":
        cmd_win(n(1, 7), n(2, 3))
    elif cmd == "check":
        cmd_check(n(1, 7))
    elif cmd == "rest":
        cmd_rest(n(1, 7), n(2, 30))
    else:
        print(__doc__)


if __name__ == "__main__":
    main()


# ================================================================ Lean に書くときの形
LEAN_SKETCH = r"""
列は `Col := ℕ × ℕ × ℕ`、行列は `Mat := List Col`。すべて決定可能な述語。

-- 行 0 の親（直前の列から左に向かって最初に浅くなる列）。スタックで 1 回走査すれば
-- 全部の親が取れるので、Lean では `par0 : Mat → List (Option ℕ)` を左からの再帰で書く。
def par0 (M : Mat) (x : ℕ) : Option ℕ :=
  (List.range x).reverse.find? (fun y => (M.get y).1 < (M.get x).1)
def parY (M : Mat) (y x : ℕ) : Option ℕ :=          -- 行 y の親は行 y-1 の親をたどる
  match y with
  | 0     => par0 M x
  | y'+1  => let rec go (p : Option ℕ) := match p with
               | none   => none
               | some q => if (M.get q).(y'+1) < (M.get x).(y'+1) then some q
                           else go (parY M y' q)
             go (parY M y' x)

-- (0) colOK : 隣り合う 2 列だけ
def colOK (M : Mat) : Prop := ∀ x < M.length,
  (x = 0 → (M.get x).1 = 0) ∧ (0 < x → (M.get x).1 ≤ (M.get (x-1)).1 + 1) ∧
  (M.get x).2 ≤ max ((M.get x).1 - 1) 0 ∧ (M.get x).3 ≤ max ((M.get x).2 - 1) 0

-- (1) DEPTH : 値 = その行の入れ子の深さ（親の値 +1）
def DEPTH (M : Mat) : Prop := ∀ x < M.length, ∀ y < 3,
  match parY M y x with
  | none   => (M.get x).(y) = 0
  | some p => (M.get x).(y) = (M.get p).(y) + 1

-- (2) SIB0 : 行 0 の連続する兄弟ブロックが辞書式に弱く減少
--     x の弟 j = x より後ろで最初に 行0 ≤ 行0(x) になる位置。j の行0 = x の行0 なら兄弟。
def SIB0 (M : Mat) : Prop := ∀ x j k, sibs0 M x j k →
  lexLE (M.slice j k) (M.slice x j)          -- lexLE は List Col の辞書式（接頭辞なら短い方が小）

-- (3) PARLAB : 行 0 の親の段との比較（列 2 本だけ）
def PARLAB (M : Mat) : Prop := ∀ x < M.length,
  match par0 M x with
  | none   => (M.get x).2 = 0 ∧ (M.get x).3 = 0
  | some p => let (_,W,Z) := M.get p; let (_,w,z) := M.get x
              w ≤ W+1 ∧ (w = W → z ≤ Z) ∧ (w = W+1 → z ≤ Z+1)

-- (4) RED : 末尾ブロックが手前のブロックの delta ずらし写しでない
--     t = 末尾列の最大の非零行、r = 行 t の親、bp = x - r、delta[y] = c[y] - M[r][y] (y<t)
def RED (M : Mat) : Prop := ∀ k ≤ M.length, ¬ reducible (M.take k)
  where reducible N :=
    ∃ r bp delta, badroot N = some (r, bp, delta) ∧ bp ≤ r ∧
      (∀ i < bp, N.get (r+i) = N.get (r-bp+i) + delta) ∧
      colOK (N.take r ++ [N.last - delta])

-- (5) PREZ : 行 2 を上げるには根ブロック内の先例か、対角の位置
def PREZ (M : Mat) : Prop := ∀ x < M.length, 1 ≤ (M.get x).3 →
  ((M.get x).1 = (M.get x).2 + 1 ∧ (M.get x).3 = (M.get x).2 - 1) ∨
  (∃ y, rootblock M x ≤ y ∧ y < x ∧ (M.get x).3 ≤ (M.get y).3)

-- (6) COPY : 長さ 2 以上の写しの直後は「3 つ目の写しの頭」以下
def COPY (M : Mat) : Prop := ∀ i j k, 2 ≤ j - i → j - i = k - j → k < M.length →
  ∀ delta, 1 ≤ delta.1 → 0 ≤ delta.2 → 0 ≤ delta.3 →
  (∀ t < j-i, M.get (j+t) = M.get (i+t) + delta) →
  M.get k ≤ M.get j + delta                              -- ≤ は列の辞書式

-- 局所判定
def ST_D_local (M : Mat) : Prop :=
  colOK M ∧ DEPTH M ∧ SIB0 M ∧ PARLAB M ∧ RED M ∧ PREZ M ∧ COPY M

-- 実測: ST_D M → ST_D_local M は <=8 列（正例 37453 個）で違反 0。
-- 逆（ST_D_local M → ST_D M）は未達: <=8 列の負例 37222 個のうち 355 個 (0.95%) が
-- ST_D_local を満たしてしまう。
"""
