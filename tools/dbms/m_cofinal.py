"""R（完全一致）の代わりになる**弱い共終条件** C1/C2/C3/C4 を、シートの正解だけで測る。

記号: f = 正解の変換（BMS 標準形 -> 同じ順序数の DBMS 標準形）、<k> = expand(_,k)（1 始まり）。
      M は 3 行 z<2 の BMS 標準形、|M|>1。

  (C1) 上からの共終: 任意の m に ある n で  f(M)<m> <= f(M<n>)
  (C2) 下からの共終: 任意の n に ある m で  f(M<n>) <= f(M)<m>
  (C3) C1 かつ C2
  (C4) ある定数 D で  f(M)<m> <= f(M<m+D>)  かつ  f(M<n>) <= f(M)<n+D>
       ＝ 各 n で  C1@D: f(M)<n-D> <= f(M<n>)  と  C2@D: f(M<n>) <= f(M)<n+D>

**土台**（すべて実測で確かめてから使う）:

  (i) シートの使える 1622 対を 3 行に 0 で詰めると、両側とも標準形のまま
      （実測: 1622/1622）。ord は展開規則だけで決まり、行 2 が全 0 の列は
      展開に関与しないので ord(pad(X)) = ord(X)。よって f(pad(b)) = pad(d)。
      これで 3 行 z=0（＝2 行を詰めたもの）の空白が埋まる。
  (ii) その 1621 対は BMS 昇順に並べると DBMS も狭義増加（実測: 違反 0）。
       つまりシート上で f は順序同型。

**挟み撃ち**: (ii) より、M<n> がシートに無くても

      A(n) = M<n> 以下で最大のシート行、 B(n) = M<n> 以上で最小のシート行
      f(A(n)) <= f(M<n>) <= f(B(n))

  が厳密に言える。これで各 (M,n) を 成立 / 反例 / 未確認 に振り分ける:

      C1@D 成立: f(M)<n-D> <= f(A(n))     反例: f(M)<n-D> >  f(B(n))
      C2@D 成立: f(B(n))   <= f(M)<n+D>   反例: f(A(n))   >  f(M)<n+D>

  M<n> がシートにあれば A=B=f(M<n>) で、判定は必ず決まる。

**加法性による密度上げ（--add）**: 行 0 が 0 の列で切ったブロックごとに
f(P ++ Q) = f(P) ++ f(Q)（NOTES (d), シート 1622 対と矛盾なし）。これを使うと
M<n> がシートに無くても厳密な f 値が出ることがある。**仮定なので既定は off**。

**2 行版による密度上げ（--rows2）**: z=0（＝2 行を詰めたもの）では
`rows2.convC` を f として使う。シートの 3 行 z=0 対 263 件すべてで convC は
正解に一致する（実測）。**やはり仮定なので既定は off**。

cmpmat は DBMS 標準形どうしにしか使えない。非標準形が出た件は「比較不能」に数える。

    python3 m_cofinal.py [MCAP] [NCAP] [Mの件数上限] [--add] [--rows2]

================================ 結果（2026-08-27）================================

M = 1620 個（3 行 z<=1、|M|>1、うち後続型 16）、n=1..24、m の窓 1..28、
(M,n) = 38880 対。比較不能（非標準形が出た）は**全モードで 0 件**。

| モード | f(M<n>) が厳密 | C1@0 反例 | C1@1 反例 | C2@0 反例 | C2@1 反例 |
|---|---|---|---|---|---|
| シートのみ            | 2186 | 389 | **0** | 131 | **0** |
| +加法性               | 2839 | 418 | **0** | 131 | **0** |
| +2 行版               | 7812 | 830 | **0** | 222 | **0** |
| +両方                 | 7972 | 844 | **0** | 222 | **0** |

厳密に分かる対での必要なずれ（+両方、7972 対、後続型 384 対は窓張り付きで除外）:

    n - g(n) : -1 が 108、0 が 6646、1 が 834     （2 以上は 0）
    h(n) - n : -1 以下が 541+、0 が 6893、1 が 186 （2 以上は 0）

* **R（f(M)<n> = f(M<n>)）は 6568/7972 = 82% でしか成り立たない。**
  添字をどうずらしても一致しない対が 387/7972 = 4.9% 残る
  （f(M<n>) が f(M)<m> と f(M)<m+1> の**あいだ**に落ちる）。
* **C1@1 と C2@1 は 38880 対すべてで反例 0。** つまり
  `f(M)<n-1> <= f(M<n>) <= f(M)<n+1>` が測れた範囲で常に成り立つ。
* M ごとの「反例が出ない最小の D」は 0 が 1225 個、1 が 395 個。**2 以上は 0 個。**
  C1 のずれが要る M（271 個）と C2 のずれが要る M（124 個）は**互いに素**。
  破れはほぼ n=1（C1: n=1 が 235・n=2 が 36、C2: n=1 が 124）。
* 未確認が多い（C1@1 で 29575/38880）のは挟み撃ちの粗さで、n>=3 で急に効かなくなる。
  n=2 では 1279+341、n=8 以降はほぼ決まらない。**反例が無いことだけが確定事実。**
"""
import sys, os, time, bisect, collections, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import expand, isstd, cmpmat, show, flat, parse, rows
import sheet3
from rows2 import convC as _convC2
from rows3 import pad as _pad2, two as _two3

MCAP = 28       # m の窓
NCAP = 24       # n の窓
DMAX = 4        # 試すずれ D の上限
ADD = False     # 加法性を使うか
R2 = False      # z=0 の断片で 2 行版 rows2.convC を使うか


# ---------------------------------------------------------------- 土台
def build():
    """3 行に詰めたシート T（挟み撃ちの土台）と、測る対象 DOM を返す。"""
    T = {}
    npad = collections.Counter()
    drop = 0
    for r in json.load(open(sheet3.DATA)):
        if not (r.get('bms') and r.get('dbms')):
            continue
        r = sheet3.fix(r)
        try:
            yb, yd = rows(parse(r['bms'])), rows(parse(r['dbms']))
            if yb > 3 or yd > 3:
                continue
            b, d = parse(r['bms'], 3), parse(r['dbms'], 3)
        except Exception:
            continue
        if not b:
            continue
        if not isstd(b, 'BMS') or not isstd(d, 'DBMS'):
            drop += 1
            continue
        npad[yb] += 1
        T[b] = d
    T[()] = ()                    # 空行列（f(空)=空）。挟み撃ちの下端。
    keys = sorted(T, key=lambda b: tuple(flat(b)))
    FK = [tuple(flat(b)) for b in keys]
    DOM = [b for b in keys if len(b) > 1 and all(c[2] <= 1 for c in b)]
    return T, keys, FK, DOM, npad, drop


def check_iso(T, keys):
    return sum(1 for a, b in zip(keys, keys[1:]) if cmpmat(T[a], T[b]) >= 0)


def is_succ(m):
    return (not m) or expand(m, 1) == expand(m, 2)


def blocks(X):
    """行 0 が 0 の列で切る（＝順序数の和の項）。"""
    out, cur = [], []
    for c in X:
        if c[0] == 0 and cur:
            out.append(tuple(cur)); cur = [c]
        else:
            cur.append(c)
    if cur:
        out.append(tuple(cur))
    return out


def frows2(X):
    """z=0（＝2 行を詰めたもの）なら 2 行版 convC で f(X) を出す。
    シートの 3 行 z=0 対 263 件すべてで convC は正解に一致する（実測）。"""
    if not X or any(c[2] for c in X):
        return None
    d = _pad2(tuple(_convC2(_two3(X))))
    return d if isstd(d, 'DBMS') else None


def fadd(T, X):
    """加法性で f(X) を出す（できなければ None）。"""
    bs = blocks(X)
    if len(bs) <= 1:
        return None
    out = []
    for b in bs:
        if b not in T:
            return None
        out.extend(T[b])
    r = tuple(out)
    return r if isstd(r, 'DBMS') else None


def bracket(T, keys, FK, X):
    """(L, U, exact) : f(X) の下限・上限。exact なら L=U=f(X)。"""
    xf = tuple(flat(X))
    i = bisect.bisect_left(FK, xf)
    if i < len(FK) and FK[i] == xf:
        d = T[keys[i]]
        return d, d, True
    if R2:
        d = frows2(X)
        if d is not None:
            return d, d, True
    if ADD:
        d = fadd(T, X)
        if d is not None:
            return d, d, True
    L = T[keys[i - 1]] if i > 0 else None
    U = T[keys[i]] if i < len(FK) else None
    return L, U, False


# ---------------------------------------------------------------- 測定
def measure(T, keys, FK, DOM, mcap, ncap, limit=None):
    order = sorted(DOM, key=lambda b: (len(b), tuple(flat(b))))
    if limit:
        order = order[:limit]
    R, bad = [], []
    t0 = time.time()
    for i, M in enumerate(order):
        fM = T[M]
        if not isstd(fM, 'DBMS'):
            bad.append((M, 0, 'f(M) が非標準')); continue
        E, ns = [], None
        for m in range(1, mcap + 1):
            e = expand(fM, m)
            if e and not isstd(e, 'DBMS'):
                ns = m; break
            E.append(e)
        if ns is not None:
            bad.append((M, 0, 'f(M)<%d> が非標準' % ns))
        info = []
        for n in range(1, ncap + 1):
            X = expand(M, n)
            L, U, ex = bracket(T, keys, FK, X)
            if L is not None and not isstd(L, 'DBMS'):
                bad.append((M, n, 'f(A) が非標準')); L = None
            if U is not None and not isstd(U, 'DBMS'):
                bad.append((M, n, 'f(B) が非標準')); U = None
            info.append((n, ex, L, U))
        R.append((M, is_succ(M), is_succ(fM), E, info))
        if i % 150 == 0:
            core._exp_memo.clear(); core._flat_memo.clear()
            if i and i % 600 == 0:
                print('  %d/%d %.0fs' % (i, len(order), time.time() - t0),
                      file=sys.stderr)
    return R, bad, time.time() - t0


def c1_at(E, L, U, n, D):
    """C1@D : f(M)<n-D> <= f(M<n>) を 1/0/-1/2 = 成立/未確認/反例/空虚 で。"""
    m = n - D
    if m < 1:
        return 2                       # 主張が空（f(M)<0> は無い）
    if m > len(E):
        return 0                       # m の窓の外
    e = E[m - 1]
    if L is not None and cmpmat(e, L) <= 0:
        return 1
    if U is not None and cmpmat(e, U) > 0:
        return -1
    return 0


def c2_at(E, L, U, n, D):
    """C2@D : f(M<n>) <= f(M)<n+D>。"""
    m = n + D
    if m > len(E):
        return 0
    e = E[m - 1]
    if U is not None and cmpmat(U, e) <= 0:
        return 1
    if L is not None and cmpmat(L, e) > 0:
        return -1
    return 0


# ---------------------------------------------------------------- 報告
def report(T, R, bad, mcap, ncap, iso_bad, npad, drop):
    print('=' * 76)
    print('■ 土台')
    print('  3 行に詰めたシート: %d 対（もとの行数の内訳 %s、標準形でなく捨てた %d）'
          % (len(T), dict(sorted(npad.items())), drop))
    print('  BMS 昇順に並べて DBMS が狭義増加でない箇所: %d' % iso_bad)
    print('  測った M: %d 個（3 行 z<=1、|M|>1）  n=1..%d  m の窓=1..%d  加法性=%s'
          % (len(R), ncap, mcap,
             ('on' if ADD else 'off') + ' / 2行版=' + ('on' if R2 else 'off')))
    tot = sum(len(r[4]) for r in R)
    ex = sum(1 for r in R for it in r[4] if it[1])
    noL = sum(1 for r in R for it in r[4] if it[2] is None)
    noU = sum(1 for r in R for it in r[4] if it[3] is None)
    print('  (M,n) 対: %d   f(M<n>) が厳密に分かる: %d   挟み撃ちのみ: %d'
          % (tot, ex, tot - ex))
    print('  下限 A が無い: %d   上限 B が無い: %d' % (noL, noU))
    print('  比較不能（非標準形が出た）: %d 件' % len(bad))
    for b in bad[:6]:
        print('      %s  n=%d  %s' % (show(b[0]), b[1], b[2]))
    print('  後続型/極限型が f で食い違う M: %d'
          % sum(1 for r in R if r[1] != r[2]))
    print()

    # ---- (1) 厳密に分かる (M,n) での g, h ----
    G, H = collections.Counter(), collections.Counter()
    Req1, Reqany = [0], [0]
    gcap = hcap = 0
    Req = Rtot = 0
    for M, sM, sF, E, info in R:
        for n, exq, L, U in info:
            if not exq:
                continue
            Rtot += 1
            g = 0
            for m in range(1, len(E) + 1):
                if cmpmat(E[m - 1], L) <= 0:
                    g = m
                else:
                    break
            h = None
            for m in range(1, len(E) + 1):
                if cmpmat(L, E[m - 1]) <= 0:
                    h = m; break
            if g >= len(E):
                gcap += 1            # 窓に張り付き（真の g は不明）
            else:
                G[n - g] += 1
            if h is None:
                hcap += 1
            else:
                H[h - n] += 1
            if g >= 1 and g == n and cmpmat(E[g - 1], L) == 0:
                Req += 1
            if g >= 1 and g == n - 1 and cmpmat(E[g - 1], L) == 0:
                Req1[0] += 1
            if g >= 1 and cmpmat(E[g - 1], L) == 0:
                Reqany[0] += 1
    print('■ (1) f(M<n>) が厳密に分かる %d 対  [g(n)=max{m: f(M)<m> <= f(M<n>)},'
          ' h(n)=min{m: f(M<n>) <= f(M)<m>}]' % Rtot)
    print('  n - g(n) の分布: %s     （窓 m<=%d に張り付き %d 件は除外）'
          % (sorted(G.items()), mcap, gcap))
    print('  h(n) - n の分布: %s     （窓内に見つからず %d 件は除外）'
          % (sorted(H.items()), hcap))
    print('  R  （f(M)<n>   がちょうど f(M<n>)）: %d / %d' % (Req, Rtot))
    print('  R+1（f(M)<n-1> がちょうど f(M<n>)）: %d / %d' % (Req1[0], Rtot))
    print('  どれかの m で ちょうど一致          : %d / %d' % (Reqany[0], Rtot))
    print()

    # ---- (2) C1@D / C2@D ----
    print('■ (2) 全 %d 対での C1@D / C2@D（挟み撃ちこみ）' % tot)
    print('  %-5s %8s %7s %9s %7s   %8s %7s %9s'
          % ('D', 'C1成立', 'C1反例', 'C1未確認', 'C1空虚',
             'C2成立', 'C2反例', 'C2未確認'))
    tab = {}
    for D in range(0, DMAX + 1):
        a, b = collections.Counter(), collections.Counter()
        for M, sM, sF, E, info in R:
            for n, exq, L, U in info:
                a[c1_at(E, L, U, n, D)] += 1
                b[c2_at(E, L, U, n, D)] += 1
        tab[D] = (a, b)
        print('  D=%-3d %8d %7d %9d %7d   %8d %7d %9d'
              % (D, a[1], a[-1], a[0], a[2], b[1], b[-1], b[0]))
    print('  ※「空虚」= n-D < 1 で主張そのものが無い対（D>0 のとき n<=D で起きる）。')
    print()
    # n ごとの決まり方（D=1）
    print('  n ごとの内訳（D=1）:')
    print('   %-4s %8s %7s %9s   %8s %7s %9s'
          % ('n', 'C1成立', 'C1反例', 'C1未確認', 'C2成立', 'C2反例', 'C2未確認'))
    for n0 in list(range(1, 9)) + [12, 16, 20, 24]:
        a, b = collections.Counter(), collections.Counter()
        for M, sM, sF, E, info in R:
            for n, exq, L, U in info:
                if n != n0:
                    continue
                a[c1_at(E, L, U, n, 1)] += 1
                b[c2_at(E, L, U, n, 1)] += 1
        if not (a or b):
            continue
        print('   %-4d %8d %7d %9d   %8d %7d %9d'
              % (n0, a[1], a[-1], a[0], b[1], b[-1], b[0]))
    print()

    # ---- (3) 素の C1 / C2 ----
    c1y = c1n = 0
    for M, sM, sF, E, info in R:
        for m in range(1, len(E) + 1):
            hit = any(L is not None and cmpmat(E[m - 1], L) <= 0
                      for n, q, L, U in info)
            if hit: c1y += 1
            else: c1n += 1
    c2y = c2n = 0
    for M, sM, sF, E, info in R:
        for n, q, L, U in info:
            hit = U is not None and any(cmpmat(U, e) <= 0 for e in E)
            if hit: c2y += 1
            else: c2n += 1
    print('■ (3) 素の C1 / C2（窓 n<=%d, m<=%d）' % (ncap, mcap))
    print('  C1「任意の m に ある n」: (M,m) %d 対  成立 %d  未確認 %d'
          % (c1y + c1n, c1y, c1n))
    print('  C2「任意の n に ある m」: (M,n) %d 対  成立 %d  未確認 %d'
          % (c2y + c2n, c2y, c2n))
    print('  ※ 窓が有限なので「反例」は素の形では確定できない。'
          '確定するのは C1@D / C2@D の反例だけ。')
    print()

    # ---- (4) M ごとの最小 D ----
    Dm, full = {}, {}
    for M, sM, sF, E, info in R:
        d0 = None
        for D in range(0, DMAX + 1):
            v1 = [c1_at(E, L, U, n, D) for n, q, L, U in info]
            v2 = [c2_at(E, L, U, n, D) for n, q, L, U in info]
            if -1 not in v1 and -1 not in v2:
                d0 = D; break
        Dm[M] = d0
        if d0 is not None:
            v1 = [c1_at(E, L, U, n, d0) for n, q, L, U in info]
            v2 = [c2_at(E, L, U, n, d0) for n, q, L, U in info]
            full[M] = (all(x in (1, 2) for x in v1), all(x in (1, 2) for x in v2))
    # 反例が出る M の集合と、反例が初めて出る n
    s1 = {}; s2 = {}
    for M, sM, sF, E, info in R:
        for n, q, L, U in info:
            if M not in s1 and c1_at(E, L, U, n, 0) == -1:
                s1[M] = n
            if M not in s2 and c2_at(E, L, U, n, 0) == -1:
                s2[M] = n
    print('■ (4) M ごとの「反例が出ない最小の D」')
    print('  C1@0 が破れる M: %d 個   C2@0 が破れる M: %d 個   両方破れる M: %d 個'
          % (len(s1), len(s2), len(set(s1) & set(s2))))
    print('  C1@0 が初めて破れる n の分布:', sorted(collections.Counter(s1.values()).items()))
    print('  C2@0 が初めて破れる n の分布:', sorted(collections.Counter(s2.values()).items()))
    print('  分布:', sorted(collections.Counter(
        (-1 if v is None else v) for v in Dm.values()).items()),
        '  （-1 = D<=%d では反例が消えない）' % DMAX)
    fc1 = sum(1 for v in full.values() if v[0])
    fc2 = sum(1 for v in full.values() if v[1])
    print('  その D で窓内の n が**全部成立**まで確認できた M: C1 %d / %d、C2 %d / %d'
          % (fc1, len(R), fc2, len(R)))
    return tab, Dm


# ---------------------------------------------------------------- 例
def examples(T, R, k=3):
    print()
    print('=' * 76)
    for which, D, lab in ((1, 0, 'C1@0  f(M)<n> <= f(M<n>)'),
                          (1, 1, 'C1@1  f(M)<n-1> <= f(M<n>)'),
                          (2, 0, 'C2@0  f(M<n>) <= f(M)<n>'),
                          (2, 1, 'C2@1  f(M<n>) <= f(M)<n+1>')):
        hits = []
        for M, sM, sF, E, info in R:
            for n, q, L, U in info:
                v = (c1_at if which == 1 else c2_at)(E, L, U, n, D)
                if v == -1:
                    hits.append((len(M), tuple(flat(M)), M, n, q, L, U, E))
                    break
        hits.sort()
        print('■ %s の反例: %d 個の M（最小 %d 件）' % (lab, len(hits), min(k, len(hits))))
        for _, _, M, n, q, L, U, E in hits[:k]:
            m = n - D if which == 1 else n + D
            print('   M        = %s' % show(M))
            print('   f(M)     = %s' % show(T[M]))
            print('   M<%-2d>    = %s' % (n, show(expand(M, n))))
            if q:
                print('   f(M<%d>)  = %s' % (n, show(L)))
            else:
                print('   f(M<%d>) は %s 以上 %s 以下' % (n, show(L) if L else '-',
                                                     show(U) if U else '-'))
            print('   f(M)<%-2d> = %s' % (m, show(E[m - 1]) if 1 <= m <= len(E) else '-'))
            print()
        print()


if __name__ == '__main__':
    av = [a for a in sys.argv[1:] if not a.startswith('--')]
    ADD = '--add' in sys.argv
    R2 = '--rows2' in sys.argv
    MCAP = int(av[0]) if len(av) > 0 else MCAP
    NCAP = int(av[1]) if len(av) > 1 else NCAP
    lim = int(av[2]) if len(av) > 2 and av[2] not in ('', '0') else None
    T, keys, FK, DOM, npad, drop = build()
    iso_bad = check_iso(T, keys)
    R, bad, dt = measure(T, keys, FK, DOM, MCAP, NCAP, lim)
    print('測定 %.1fs' % dt, file=sys.stderr)
    tab, Dm = report(T, R, bad, MCAP, NCAP, iso_bad, npad, drop)
    examples(T, R)
