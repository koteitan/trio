"""ImgClosedT を測る。RD1（3 行版 ReindexD）の唯一の新しい要。

    ImgClosedT: 任意の BMS 3 行 z<2 標準形 A（|A|>1）と m>=1 に対し
                ある BMS 3 行 z<2 標準形 B があって (conv3 A)<m> = conv3 B

**性質 R は目標ではない**（NOTES §性質 R で偽と確定）。`ST_D_descend` が要求するのは
相手が A<n> であることではなく、この ImgClosedT ＋ Sandwich 2 つ（既に反例 0）。

============================ 測ったこと（2026-08-27） ============================

## 1. 全数走査（`scan`）

| 対象 | 対の数 | 逆像あり | 逆像なし | うち打ち切り |
|---|---|---|---|---|
| z=0, 2..6 列, m<=3   | 3852 | **3852** | **0** | 0 |
| z<2, 2..4 列, m<=3   |  429 |   425 |  4 | 4 |
| z<2, 2..5 列, m<=3   | 3051 |  2996 | **55** | 51 |

* **z=0（＝Lean で証明済みの 2 行の断片）はちょうど 0 破れ**（9 秒、全部 d2b3 の
  速い道で当たる）。だから破れは 3 行への拡張がほんとうに持っている欠陥。
* 破れは 55 対 = **相異なる A が 28 個**。**m=1 の破れは 0**（1017/1017 成功）、
  破れはすべて m=2 と m=3。
* 逆像の長さの比 |B|/|T| は 0.50〜1.67 に散る（<=5 列, 2996 件）。
  **|B|>|T| が 327 件（11%）、最大 |B|=|T|+8。**
  だから列数をそろえて探すと必ず取り逃がす。

## 2. 破れた A 28 個の形

全部 **接頭辞 (0,0,0)(1,1,1) を持ち、z=1 の列を含む**（z=0 は 1 つも無い）。
24/28 は **末尾の列が (x,1,0)**。像の末尾も (y,1,0) で、目標 T の末尾が (y,2,0)
＝ **行 1 が 1 だけ足りない**。NOTES §性質 R の反例と同じ病気（末尾 1 列・差 (0,-1,0)）。
3 列目以降の (行1,行2) の並びで数えると

    (1,0)(1,0)(1,0)  6 / (1,1)(1,0)(1,0)  5 / (2,0)(1,0)(1,0)  5
    (2,1)(1,0)(1,0)  5 / (0,0)(1,1)(1,1)  2 / (1,0)(1,0)       2
    (1,0)(1,0)(0,0)  2 / (1,0)(2,1)(1,0)  1

## 3. 共終性 C1 との関係（決定的）

<=5 列 1017 個で C1 の破れ 7・C2 の破れ 0（NOTES の値と一致）。

    ImgClosedT NG 28 個 ⊇ C1 破れ 7 個   （C1 だけ = **0**、NG だけ = 21）

**ImgClosedT は C1 より真に細かい指標**で、C1 が見逃す 21 個を捕まえる。
だから今後の主指標はこれでよい。

## 4. 「探索不足」か「本当に像の外」か

RD1 が要求する窓は [A<m>, A)（translate (A<m>) <=o translate B <o translate A）。
その窓の中を **枝刈りを一切使わず**歩いた（`scan_window` / `rd1`）:

    A                                    m |T|  歩き切った列数    窓の大きさ  逆像
    (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,1,0)  3  10  15 (=1.50|T|)★        770  なし
    (0,0,0)(1,1,1)(2,1,0)(2,1,0)         2   9  13 (=1.44|T|)    1412823  なし
    (0,0,0)(1,1,1)(2,1,0)(3,1,0)         2   9  12 (=1.33|T|)     509408  なし
    (0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,1)  2   9  12 (=1.33|T|)     320574  なし
    (0,0,0)(1,1,1)(2,1,0)(2,1,0)         3  13  15 (=1.15|T|)     610779  なし
    (0,0,0)(1,1,1)(2,1,0)(3,1,0)         3  13  13 (=1.00|T|)      25933  なし

  ★ 1.5 倍の列数まで枝刈りなしで歩き切ったので、この 1 件は**確定**。
    ほかも、実際の逆像の伸び（<=5 列 2996 件で最大 |B|=|T|+8、9 割は |B|<=|T|）を
    大きく超えたところまで空。**「探索が足りない」ではなく「本当に像の外」**。

窓を外した ImgClosedT そのものは、誘導つき探索（下記）で
    (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,1,0) m=3 : SL<=8 で節点 450699 を歩き切って なし
    (0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,1) m=2 : SL<=6 で節点 477669 を歩き切って なし
    (0,0,0)(1,1,1)(2,1,0)(2,1,0)        m=2 : SL<=3 窓なしで 27183 を歩き切って なし
と、どれも「見つからない」。**探索不足ではなく本当に像の外**に寄る証拠。
（★の 1 件は 1.5 倍の列数まで枝刈りなしで歩き切ったので、その範囲では確定。）

## 5. 像が DBMS 非標準になる 3 件（<=7 列）とは**別物**

    (0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)(4,0,0) / (4,1,0) / (4,2,0)

の 3 つは像が DBMS 非標準だが、**m=1,2,3 のどれでも逆像は d2b3 が即座に出す**。
つまり ImgClosedT の破れと「像が非標準」は独立な 2 つの欠陥。
再現は `python3 m_imgclosed.py ns`。

============================ 逆像の探し方 ============================

1. **速い道** `fast`: 逆写像 `inv3.d2b3` を当てる。縮約が起きていなければ当たる。
   （d2b3 は 2026-08-27 に改良されたので当たり率は動く。ここでは 3051 対中 2996。）
2. **誘導つき DFS** `search`: 1 列ずつ伸ばして `isstd` で篩い、`b2d3` の値が
   目標 T の接頭辞から離れたら切る。conv3 はほぼ接頭辞単調（P が B の接頭辞なら
   b2d3(P) はほぼ b2d3(B) の接頭辞）で、ずれ
       slack = |b2d3(P)| - lcp(b2d3(P), b2d3(B))
   は縮約のときだけ出る。実測: 縮約なしの逆像 2592 件・15239 接頭辞で **slack<=1**、
   縮約のある既知の例（下の B_2）で **slack=4**。だから SL を上げながら探す。
   **SL の枝刈りは健全ではない**ので、なしと出たら SL と節点上限を上げること。
3. **枝刈りなしの全数** `scan_window` / `preimages`: 窓と列数だけで枝刈りする。
   「打ち切りなしで なし」ならその範囲での完全な否定になる。重い。

窓（lex の上下限）
------------------
* RD1 が要求するのは **A<m> <= B < A**（`scan_window`, `cmd_rd1` はこれ）。
* Sandwich から出るのは **A<m-1> <= B <= A<m+1>**（`search` の既定は下限
  A<max(m-1,1)>・上限 A）。m=1 は下限が無い（A<0> が無い）。
  実測（縮約なしの逆像 2592 件）: 下限 A<max(m-1,1)> は 2587/2592 で成立、
  破れる 5 件は**全部 m=1**。上限 B < A と B <= A<m+1> は 2592/2592。
  だから梯子の最後に **下限なし**の段を置いてある。

**逆像は像より長いことがある。** 実例（NOTES §性質 R の反例）:
    M = (0,0,0)(1,1,1)(2,1,0)(3,0,0),  f(M)<2> は 6 列
    B_2 = (0,0,0)(1,1,1)(2,1,0)(2,1,0)(1,1,0)(2,2,1)(3,2,0)(3,2,0) は 8 列
列数の上限は既定で ceil(1.5*|T|)。

答え合わせ
----------
`valid` は誘導つき探索と枝刈りなしの全数を突き合わせる。
<=3 列 x m<=2 の |T|<=5 の 39 対で**食い違い 0**（56 秒）。

使い方
------
    python3 m_imgclosed.py one  "(0,0,0)(1,1,1)(2,1,0)(3,0,0)" 2   1 件を詳しく
    python3 m_imgclosed.py scan 5 3            <=5 列 x m<=3（安い梯子）
    python3 m_imgclosed.py scan 6 3 0          z=0 の対照（破れ 0 になるはず）
    python3 m_imgclosed.py scan 5 3 1 0 8      8 分割の 0 番（IMGC_OUT=... で pickle）
    python3 m_imgclosed.py deep "(...)" 2      1 件を梯子を伸ばして
    python3 m_imgclosed.py rd1  "(...)" 2      RD1 の窓を枝刈りなしで全数
    python3 m_imgclosed.py ns                  像が非標準の 3 件
    python3 m_imgclosed.py valid 3 2 5         誘導つき vs 全数

`rows3.check` に足すには `imgclosed(f, A, mmax)` を呼ぶ（本体には入れていない）。
"""
import sys, os, time, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import parse, show, expand, isstd, cmpmat
from rows3 import gen3, key, b2d3


def flat(m):
    return [v for c in m for v in c]


def lcp(a, b):
    i, n = 0, min(len(a), len(b))
    while i < n and a[i] == b[i]:
        i += 1
    return i


# ---------------------------------------------------------------- 窓の枝刈り
def lo_state(fp, fl):
    """接頭辞 fp（の任意の延長）が下限 fl 以上になれるか。
    -1 = 望みなし / 0 = まだ決まらない / 1 = どの延長でも下限を満たす。"""
    if fl is None:
        return 1
    for i in range(min(len(fp), len(fl))):
        if fp[i] != fl[i]:
            return 1 if fp[i] > fl[i] else -1
    return 1 if len(fp) >= len(fl) else 0


def hi_state(fp, fu):
    """接頭辞 fp が上限 fu より**真に小さく**なれるか。
    -1 = 望みなし / 0 = まだ決まらない / 1 = どの延長でも真に小さい。"""
    if fu is None:
        return 1
    for i in range(min(len(fp), len(fu))):
        if fp[i] != fu[i]:
            return 1 if fp[i] < fu[i] else -1
    return -1 if len(fp) >= len(fu) else 0


# ---------------------------------------------------------------- 全数（検証用）
def window(lo, hi, Lmax, zcap=1, cap=None):
    """lo <= B < hi かつ |B| <= Lmax の BMS 3 行標準形を**全部**（lo/hi は None 可）。
    像の枝刈りを一切使わないので、`search` の答え合わせ用。重い。"""
    flo = flat(lo) if lo is not None else None
    fhi = flat(hi) if hi is not None else None
    out, trunc = [], [False]

    def rec(S, fs, lst, hst):
        if cap is not None and len(out) >= cap:
            trunc[0] = True
            return
        if S and lst == 1 and hst >= 0:
            out.append(S)
        if len(S) >= Lmax:
            return
        amax = (S[-1][0] + 1) if S else 0
        for a in range(amax + 1):
            for b in range(a + 1):
                for c in range(min(b, zcap) + 1):
                    T = S + ((a, b, c),)
                    ft = fs + [a, b, c]
                    l2 = lo_state(ft, flo)
                    if l2 < 0:
                        continue
                    h2 = hi_state(ft, fhi)
                    if h2 < 0:
                        continue
                    if not isstd(T, 'BMS'):
                        continue
                    rec(T, ft, l2, h2)
                    if cap is not None and len(out) >= cap:
                        trunc[0] = True
                        return

    rec((), [], lo_state([], flo), hi_state([], fhi))
    return out, trunc[0]


def preimages(A, m, Lmax=None, f=b2d3, lo=None, hi='A', cap=300000):
    """全数版の逆像（枝刈りは窓と列数だけ）。返り値 (T, Bs, trunc, 窓の大きさ)。"""
    T = tuple(expand(f(A), m))
    if Lmax is None:
        Lmax = (3 * len(T) + 1) // 2
    if lo is None:
        lo = tuple(expand(A, max(m - 1, 1)))
    elif lo is False:
        lo = None
    U = tuple(A) if hi == 'A' else hi
    W, trunc = window(lo, U, Lmax, cap=cap)
    Bs = [B for B in W if f(B) == T]
    return T, Bs, trunc, len(W)


# ---------------------------------------------------------------- 誘導つき探索
def search(A, m, f=b2d3, Lmax=None, SL=4, lo=None, hi='A', nodecap=300000,
           allb=False, T=None):
    """像で誘導した DFS。返り値 (T, Bs, ('ok'|'cap', 訪れた節点数))。

    枝刈り: |b2d3(P)| <= |T|+SL  かつ  lcp(b2d3(P), T) >= |b2d3(P)|-SL。
    lo=False で下限なし、hi=None で上限なし。"""
    if T is None:
        T = tuple(expand(f(A), m))
    if Lmax is None:
        Lmax = (3 * len(T) + 1) // 2
    if lo is None:
        lo = tuple(expand(A, max(m - 1, 1)))
    elif lo is False:
        lo = None
    U = tuple(A) if hi == 'A' else (None if hi is None else hi)
    flo = flat(lo) if lo is not None else None
    fhi = flat(U) if U is not None else None
    LT = len(T)
    out, cnt, hitcap, done = [], [0], [False], [False]

    def rec(S, fs, lst, hst):
        if done[0]:
            return
        if cnt[0] >= nodecap:
            hitcap[0] = True
            return
        if len(S) >= Lmax:
            return
        amax = (S[-1][0] + 1) if S else 0
        for a in range(amax + 1):
            for b in range(a + 1):
                for c in range(min(b, 1) + 1):
                    P = S + ((a, b, c),)
                    fp = fs + [a, b, c]
                    l2 = lo_state(fp, flo)
                    if l2 < 0:
                        continue
                    h2 = hi_state(fp, fhi)
                    if h2 < 0:
                        continue
                    if not isstd(P, 'BMS'):
                        continue
                    cnt[0] += 1
                    if cnt[0] >= nodecap:
                        hitcap[0] = True
                        return
                    Q = f(P)
                    if Q == T:
                        out.append(P)
                        if not allb:
                            done[0] = True
                            return
                        continue
                    if len(Q) > LT + SL:
                        continue
                    if lcp(Q, T) < len(Q) - SL:
                        continue
                    rec(P, fp, l2, h2)
                    if done[0]:
                        return
                    if cnt[0] >= nodecap:
                        hitcap[0] = True
                        return

    rec((), [], lo_state([], flo), hi_state([], fhi))
    return T, out, ('cap' if (hitcap[0] and not out) else 'ok', cnt[0])


def fast(A, m, f=b2d3):
    """逆写像 d2b3 を当てるだけの速い道。当たれば B、外れれば None。"""
    try:
        from inv3 import d2b3
    except Exception:
        return None
    T = tuple(expand(f(A), m))
    try:
        B = d2b3(T)
    except Exception:
        return None
    if B and isstd(B, 'BMS') and all(c[2] <= 1 for c in B) and f(B) == T:
        return tuple(B)
    return None


# 梯子: (SL, 節点上限, 下限を使うか, |T| に足す列数)
LADDER = ((2, 20000, True, None), (4, 120000, True, None),
          (6, 400000, True, None), (3, 80000, False, 3))

# 全数走査用の安い梯子。当たるときは節点 1 万も要らない（実測）ので、
# 見つからなかったものだけ `deep` で確かめる、という二段構えにする。
LADDER_SCAN = ((2, 5000, True, None), (4, 25000, True, None),
               (6, 25000, True, None), (3, 15000, False, 3))


def find(A, m, f=b2d3, ladder=LADDER, T=None):
    """(conv3 A)<m> の逆像を 1 つ。返り値 (T, B or None, 段の名前, 節点数, 打ち切り)。"""
    if T is None:
        T = tuple(expand(f(A), m))
    B = fast(A, m, f)
    if B is not None:
        return T, B, 'd2b3', 0, False
    tot, capped = 0, False
    for SL, cap, uselo, extra in ladder:
        Lmax = (len(T) + extra) if extra is not None else None
        _, Bs, st = search(A, m, f=f, SL=SL, Lmax=Lmax,
                           lo=(None if uselo else False), nodecap=cap, T=T)
        tot += st[1]
        if st[1] > 20000:      # メモが RSS を食うので段ごとに捨てる
            core._isstd_memo.clear(); core._flat_memo.clear()
        if st[0] == 'cap':
            capped = True
        if Bs:
            return T, Bs[0], 'SL%d%s' % (SL, '' if uselo else '/nolo'), tot, False
    return T, None, 'none', tot, capped


def imgclosed(f, A, mmax=3, verbose=0):
    """`rows3.check` に足せる形。A は BMS 3 行 z<2 標準形の**リスト**。
    返り値 (bad, capped, ratios)。
      bad     : 逆像が見つからなかった (M, m, T) の並び
      capped  : そのうち探索を打ち切った (M, m) の並び（＝「探索不足」の疑い）
      ratios  : 見つかった B について (|B|, |T|) の並び"""
    bad, capped, ratios = [], [], []
    for M in A:
        if len(M) < 2:
            continue
        for m in range(1, mmax + 1):
            T, B, stage, nodes, cap = find(M, m, f=f)
            if B is not None:
                ratios.append((len(B), len(T)))
            else:
                bad.append((tuple(M), m, T))
                if cap:
                    capped.append((tuple(M), m))
    if verbose:
        print('  ImgClosedT: 逆像なし %d / 打ち切り %d' % (len(bad), len(capped)))
        for M, m, T in bad[:verbose]:
            print('        %-34s m=%d  T=%s' % (show(M), m, show(T)))
    return bad, capped, ratios


# ---------------------------------------------------------------- CLI
def cmd_one(s, m, SL=None):
    A = parse(s, 3)
    N = b2d3(A)
    print('A      %s   (%d 列)' % (show(A), len(A)))
    print('conv3A %s   (%d 列)' % (show(N), len(N)))
    t0 = time.time()
    T, B, stage, nodes, cap = find(A, m)
    print('T=<%d>  %s   (%d 列, DBMS 標準形 %s)' % (m, show(T), len(T), isstd(T, 'DBMS')))
    print('逆像   %s' % (show(B) if B else 'なし'))
    print('  段 %s  節点 %d  打ち切り %s  %.1fs'
          % (stage, nodes, cap, time.time() - t0))
    if B:
        print('  |B|=%d |T|=%d 比 %.2f   窓: A<%d><=B %s, B<A %s, B<=A<%d> %s'
              % (len(B), len(T), len(B) / len(T), max(m - 1, 1),
                 cmpmat(B, tuple(expand(A, max(m - 1, 1)))) >= 0,
                 cmpmat(B, tuple(A)) < 0, m + 1,
                 cmpmat(B, tuple(expand(A, m + 1))) <= 0))
    if SL is not None:
        t0 = time.time()
        T, Bs, st = search(A, m, SL=SL, nodecap=5000000, allb=True)
        print('  SL=%d で全部: %d 個 %s %.1fs' % (SL, len(Bs), st, time.time() - t0))
        for b in Bs:
            print('     %s' % show(b))


def cmd_scan(lim, mmax, zcap=1, part=0, nparts=1, verbose=12):
    t0 = time.time()
    A = [M for M in sorted(gen3('BMS', lim, zcap=zcap), key=key) if len(M) > 1]
    if nparts > 1:
        A = A[part::nparts]
    print('BMS 3 行 z<=%d 標準形 (2..%d 列): %d 個 [%d/%d] x m=1..%d = %d 対'
          % (zcap, lim, len(A), part, nparts, mmax, len(A) * mmax), flush=True)
    stg = collections.Counter()
    bad, capped, ratios = [], [], []
    for i, M in enumerate(A):
        for m in range(1, mmax + 1):
            T, B, stage, nodes, cap = find(M, m, ladder=LADDER_SCAN)
            stg[stage] += 1
            if B is not None:
                ratios.append((len(B), len(T), len(M), m))
            else:
                bad.append((tuple(M), m, T, cap))
                if cap:
                    capped.append((tuple(M), m))
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        if (i + 1) % 25 == 0:
            print('  %d/%d  なし %d  (%.0fs)'
                  % (i + 1, len(A), len(bad), time.time() - t0), flush=True)
    print('--- <=%d 列 / m<=%d ---' % (lim, mmax))
    print('  対 %d: 逆像あり %d / なし %d（うち打ち切り %d）'
          % (len(A) * mmax, len(ratios), len(bad), len(capped)))
    print('  当たった段: %s' % sorted(stg.items()))
    rc = collections.Counter('%.2f' % (a / b) for a, b, _, _ in ratios)
    print('  |B|/|T| の分布: %s' % sorted(rc.items(), key=lambda kv: float(kv[0])))
    lc = collections.Counter(a - b for a, b, _, _ in ratios)
    print('  |B|-|T| の分布: %s' % sorted(lc.items()))
    print('  |B|/|T| の最大 %.2f' % max(a / b for a, b, _, _ in ratios))
    print('  (%.0fs)' % (time.time() - t0))
    out = os.environ.get('IMGC_OUT')
    if out:
        import pickle
        pickle.dump({'ratios': ratios, 'bad': bad, 'capped': capped,
                     'stg': dict(stg)}, open(out, 'wb'))
    if bad:
        print('  --- 逆像が見つからなかったもの ---')
        bc = collections.Counter((len(M), m, tr) for M, m, _, tr in bad)
        print('  (|A|, m, 打ち切り) 別: %s' % sorted(bc.items()))
        for M, m, T, tr in bad[:verbose]:
            print('    NG %-34s m=%d  T=%-40s std=%s%s'
                  % (show(M), m, show(T), isstd(T, 'DBMS'),
                     '  [打ち切り]' if tr else ''))
    return bad


DEEP = ((6, 800000, True, None), (8, 800000, True, None),
        (10, 800000, True, None), (12, 800000, True, None),
        (6, 400000, False, 4), (10, 400000, False, 6))


def cmd_deep(spec, m, ladder=DEEP):
    """見つからなかった 1 件を、梯子を伸ばして確かめる。
    ここでも見つからなければ「探索不足」ではなく「本当に像の外」に寄る。"""
    M = parse(spec, 3)
    T = tuple(expand(b2d3(M), m))
    print('A %s  m=%d  |T|=%d  T=%s  T std=%s'
          % (show(M), m, len(T), show(T), isstd(T, 'DBMS')))
    for SL, cap, uselo, extra in ladder:
        Lmax = (len(T) + extra) if extra is not None else None
        t0 = time.time()
        _, Bs, st = search(M, m, SL=SL, Lmax=Lmax,
                           lo=(None if uselo else False), nodecap=cap, T=T)
        print('  SL=%-2d 下限%s Lmax=%s -> %s  %s 節点 %d  %.0fs'
              % (SL, 'あり' if uselo else 'なし',
                 Lmax if Lmax else 'ceil(1.5|T|)',
                 show(Bs[0]) if Bs else 'なし', st[0], st[1], time.time() - t0),
              flush=True)
        core._isstd_memo.clear(); core._flat_memo.clear(); core._exp_memo.clear()
        if Bs:
            return Bs[0]
    return None


def scan_window(lo, hi, Lmax, f=b2d3, T=None, zcap=1, nodecap=None):
    """lo <= B < hi かつ |B|<=Lmax の BMS 標準形を**貯めずに**歩き、f(B)==T を探す。
    枝刈りは窓と列数だけ（像の枝刈りは一切しない）ので、
    「打ち切りなしで なし」なら**その範囲での完全な否定**になる。
    返り値 (B or None, 訪れた個数, 打ち切りしたか)。"""
    flo = flat(lo) if lo is not None else None
    fhi = flat(hi) if hi is not None else None
    st = {'n': 0, 'hit': None, 'cap': False}

    def rec(S, fs, lst, hst):
        if st['hit'] is not None or st['cap']:
            return
        if len(S) >= Lmax:
            return
        amax = (S[-1][0] + 1) if S else 0
        for a in range(amax + 1):
            for b in range(a + 1):
                for c in range(min(b, zcap) + 1):
                    P = S + ((a, b, c),)
                    fp = fs + [a, b, c]
                    l2 = lo_state(fp, flo)
                    if l2 < 0:
                        continue
                    h2 = hi_state(fp, fhi)
                    if h2 < 0:
                        continue
                    if not isstd(P, 'BMS'):
                        continue
                    st['n'] += 1
                    if nodecap and st['n'] >= nodecap:
                        st['cap'] = True
                        return
                    if st['n'] % 100000 == 0:
                        core._isstd_memo.clear(); core._flat_memo.clear()
                        core._exp_memo.clear()
                    if l2 == 1 and f(P) == T:
                        st['hit'] = P
                        return
                    rec(P, fp, l2, h2)
                    if st['hit'] is not None or st['cap']:
                        return

    rec((), [], lo_state([], flo), hi_state([], fhi))
    return st['hit'], st['n'], st['cap']


def cmd_rd1(spec, m, Lmax=None, cap=3000000):
    """RD1 が要求する窓 [A<m>, A) の中を**枝刈りなしで全数**歩く。
    「全数」で「なし」なら、その列数の範囲で RD1 はその (A,m) で偽。"""
    A = parse(spec, 3)
    T = tuple(expand(b2d3(A), m))
    lo = tuple(expand(A, m))
    if Lmax is None:
        Lmax = (3 * len(T) + 1) // 2
    for L in range(len(T), Lmax + 1):
        t0 = time.time()
        B, n, tr = scan_window(lo, tuple(A), L, T=T, nodecap=cap)
        print('  Lmax=%2d 窓 %8d 個 %s -> %s  (%.0fs)'
              % (L, n, '打ち切り' if tr else '全数',
                 show(B) if B else 'なし', time.time() - t0), flush=True)
        core._isstd_memo.clear(); core._flat_memo.clear(); core._exp_memo.clear()
        if B or tr:
            return B
    return None


def cmd_ns(mmax=3):
    """像が DBMS 非標準になる 3 件（<=7 列）で ImgClosedT がどうなるか。"""
    S = ['(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)(4,0,0)',
         '(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)(4,1,0)',
         '(0,0,0)(1,1,1)(2,0,0)(3,1,1)(3,1,0)(4,2,1)(4,2,0)']
    for s in S:
        M = parse(s, 3)
        N = b2d3(M)
        print('%s' % show(M))
        print('   像 %s' % show(N))
        print('   像は DBMS 標準形? %s' % isstd(N, 'DBMS'))
        for m in range(1, mmax + 1):
            t0 = time.time()
            T, B, stage, nodes, cap = find(M, m)
            print('   m=%d |T|=%d T std=%s -> 逆像 %s  [%s, 節点 %d, 打ち切り %s, %.0fs]'
                  % (m, len(T), isstd(T, 'DBMS'), show(B) if B else 'なし',
                     stage, nodes, cap, time.time() - t0), flush=True)


def cmd_valid(lim, mmax, tcap=6):
    """`search`（像の枝刈りあり）と `preimages`（全数）の答え合わせ。
    全数は重いので |T|<=tcap の対だけ見る。"""
    A = [M for M in sorted(gen3('BMS', lim, zcap=1), key=key) if len(M) > 1]
    t0 = time.time()
    ng = n = 0
    for M in A:
        for m in range(1, mmax + 1):
            if len(tuple(expand(b2d3(M), m))) > tcap:
                continue
            n += 1
            T, Bs, tr, w = preimages(M, m)
            T2, B2, stage, nodes, cap = find(M, m)
            a = bool(Bs)
            b = B2 is not None
            if a != b or (a and b and b2d3(B2) != T):
                ng += 1
                print('  食い違い %s m=%d 全数 %s / 誘導 %s (打ち切り %s)'
                      % (show(M), m, show(Bs[0]) if Bs else '-',
                         show(B2) if B2 else '-', tr))
    print('答え合わせ <=%d 列 x m<=%d, |T|<=%d の %d 対: 食い違い %d  (%.0fs)'
          % (lim, mmax, tcap, n, ng, time.time() - t0))


if __name__ == '__main__':
    a = sys.argv[1:]
    if not a:
        cmd_scan(4, 3)
    elif a[0] == 'one':
        cmd_one(a[1], int(a[2]), int(a[3]) if len(a) > 3 else None)
    elif a[0] == 'scan':
        cmd_scan(int(a[1]), int(a[2]) if len(a) > 2 else 3,
                 int(a[3]) if len(a) > 3 else 1,
                 int(a[4]) if len(a) > 4 else 0,
                 int(a[5]) if len(a) > 5 else 1)
    elif a[0] == 'rd1':
        A = parse(a[1], 3)
        print('A %s  m=%s  conv3A %s' % (show(A), a[2], show(b2d3(A))))
        cmd_rd1(a[1], int(a[2]),
                int(a[3]) if len(a) > 3 else None)
    elif a[0] == 'deep':
        cmd_deep(a[1], int(a[2]))
    elif a[0] == 'ns':
        cmd_ns(int(a[1]) if len(a) > 1 else 3)
    elif a[0] == 'valid':
        cmd_valid(int(a[1]), int(a[2]) if len(a) > 2 else 2,
                  int(a[3]) if len(a) > 3 else 6)
    else:
        print(__doc__)
