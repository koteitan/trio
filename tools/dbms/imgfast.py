"""ImgClosedT の**速い**採点器（課題 E4）。規則を試すたびに主指標を測るための道具。

    ImgClosedT: 任意の BMS 3 行 z<2 標準形 A（|A|>1）と m>=1 に対し
                ある BMS 3 行 z<2 標準形 B があって (conv3 A)<m> = conv3 B

これは RD1（= ReindexT1 の新しい要）のただ 1 つの未証明部分である
（NOTES §Lean の器 / §ImgClosedT の測定）。

速くする筋は 3 つ。`m_imgclosed.py` の答えは変えない（下の「答え合わせ」参照）。

  (1) **逆写像 `inv3.d2b3` を 1 発当てる**（`m_imgclosed.fast` と同じ）。
      当たれば逆像 B を手に持っているので**存在の構成的な証明**。
      <=5 列 x m<=3 の 3051 対で 2996 対がこれで当たる。1 対 2.6ms（<=5 列）〜
      13.7ms（<=7 列。列が伸びると `conv3` も `isstd` も高くなる）。
  (2) 外れた対だけ**誘導つき DFS**（`search2`）に落とす。`m_imgclosed.search` と
      同じ木を歩くが、**像の枝刈りを `isstd` より先に**当てる。
      `isstd`（＝対角からの降下）が全体の 92% を食っていた（cProfile 実測）ので、
      これだけで 1 件 4.2s -> 1.2s になり、しかも節点上限に当たらなくなる
      （例: (0,0,0)(1,1,1)(2,1,0)(2,1,0) m=2 は `search` が 25000 節点で
      打ち切りだったのが、`search2` は 16114 節点で**木を歩き切る**）。
  (3) 段 1 も段 2 も **fork した子プロセスに配る**（既定は CPU 数、上限 28）。
      段 2 は 1 対が 10〜30s かかるので、時間はほぼ**外れの対の数**で決まる。

健全性（下の「答え合わせ」）
---------------------------
* 接頭辞が標準形でない行列からは標準形は伸びない（`gen3` と同じ前提）ので、
  「先に像で切る」ことは答えを変えない。像の枝刈り `SL` 自体は
  **健全ではない**（`m_imgclosed` と同じ）ので、「なし」は破れの**上界**である。
* `d2b3` が当たった対は上界ではなく**確定**（B を持っている）。
* `valid` で `m_imgclosed.find`（遅い版）と結論を突き合わせ、`vwin` で
  `m_imgclosed.preimages`（**枝刈りなしの全数**）と突き合わせる。実測は下記。

使い方
------
    python3 imgfast.py scan 5            <=5 列 x m<=3 を採点
    python3 imgfast.py scan 6 3 1 28     <=6 列 / m<=3 / z<=1 / 28 並列
    python3 imgfast.py scan 6 3 0        z=0 の対照（破れ 0 になるはず）
    python3 imgfast.py valid 4 3         `m_imgclosed` の遅い版と結論を突き合わせ
    python3 imgfast.py valid 4 3 1 28 full   同上（既定の重い梯子。とても遅い）
    python3 imgfast.py vwin 3 2 5        枝刈りなしの全数と突き合わせ（探索の検算）
                                         （|T|<=6 にすると窓が爆発する。5 まで）
    python3 imgfast.py one "(0,0,0)(1,1,1)(2,1,0)(2,1,0)" 2
    python3 imgfast.py fast 7            段 1 だけ（探索に落とさない＝甘い上界）
    python3 imgfast.py est 7             走らせる前の見積もり（標本を実測して外挿）

`rows3.check` に足すには（`rows3.imgclosed_fast` と**同じ 3 つ組**を返すので
差し替えるだけでよい）:

    from imgfast import imgclosed_fast          # rows3 の同名関数を隠す
    icok, ictot, icbad = imgclosed_fast(f, A, imgc, d2b3)

rows3 のものは `d2b3` が外れたら即あきらめる（＝破れの上界が甘い）が、
こちらは外れだけ探索に落とすので**上界がきつくなる**。返り値には
`.capped` / `.rescued` / `.secs` / `.badpairs` が属性として付いている。
探索を切りたいときは `imgclosed_fast(f, A, mmax, fallback=False)`
（rows3 のものと完全に同じ答え。並列なぶんだけ速い）。
`gen3` から回すなら `score(f, lim, mmax, fallback=...)` の 1 行でよい。
梯子は `ladder=` で差し替えられる（`LADDER_FAST` 既定 / `LADDER_FULL` 念入り /
`LADDER_DEEP` 1 件を深追い）。

測ったこと（2026-08-27, conv3 v11, 28 コア）
-------------------------------------------
| 対象 | 対 | d2b3 で当たり | 探索で救出 | 破れ 対 (A) | 壁の秒 |
|---|---|---|---|---|---|
| <=4 列 z<2 m<=3 |   429 |   425 | 0 |   4 (2)   |  12 |
| <=5 列 z<2 m<=3 |  3051 |  2996 | 0 |  55 (28)  |  44 |
| <=6 列 z<2 m<=3 | 25158 | 24505 | 0 | 653 (327) | 561（段 1 だけなら 21） |
| <=6 列 **z=0** m<=3 |  3852 |  3852 | - |   0 (0)   |   1 |

**z=0（Lean で答えが確定している断片）の対照は破れ 0**（`m_imgclosed` の
9 秒に対し 1 秒）。ここが 0 でなくなったら採点器の側を疑うこと。

* **<=5 列の 55 対 / A 28 個は `m_imgclosed.py` の既知の値とちょうど同じ**
  （NOTES §ImgClosedT の測定）。`m_imgclosed.py scan 5 3` は同じ結論に 10 分かかる。
* <=6 列の A 327 個も `rows3` の速い道の値と一致（列数別 4 列 2 / 5 列 26 / 6 列 299）。
* **段 2 は 1 対も救出しなかった**（<=6 列まで）。つまりこの範囲では
  「`d2b3` が外れる」＝「本当に像の外」で、段 1 だけの点数が既に正しい。
  段 2 は**その確認**に効く（<=5 列 3s -> 44s、<=6 列 21s -> 561s）。
  規則をいじりながら回すときは `fast`（段 1 だけ）、区切りで `scan`。
* <=7 列（231843 対）は `est 7` の実測外挿で **28 並列 35 分**
  （段 1 だけなら 2 分）。外れは既知で 7665 対（3.3%）なので実際は 45 分くらい。
  「規則を試すたび」に回すなら <=6 列の `fast`（21s）か `scan`（9 分）が現実的。

答え合わせ（健全性）
--------------------
1. `valid 4 3` : <=4 列 x m<=3 の **429 対全部**で `m_imgclosed.find`
   （`LADDER_SCAN`、像の枝刈りが `isstd` の後）と**結論の食い違い 0**（65s）。
   `valid 5 3` : <=5 列 x m<=3 の 3051 対でも**食い違い 0**。
2. `vwin 3 2 5` : `m_imgclosed.preimages`（**枝刈りなしの全数**）と 39 対で突き合わせ。
   「全数は逆像を持つのに梯子が取り逃がした」0 対、「梯子の B が全数の集合に無い」
   0 対、打ち切り 0。
3. `fallback=False` にすると `rows3.imgclosed_fast` と**破れの集合がぴったり同じ**
   （<=5 列で確認）。
4. 既定の重い梯子（`m_imgclosed.LADDER`）との突き合わせは**やっていない**。
   <=4 列でも 1 対に 30 分以上かかる対があり（節点 62 万 x |T|=16 で 1 節点 4.5ms）、
   1 時間走らせて 429 対中 240 対までしか進まなかったので打ち切った。
"""
import sys, os, time, collections
import multiprocessing as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import expand, isstd, show, parse
from rows3 import gen3, key, b2d3
from m_imgclosed import flat, lcp, lo_state, hi_state


# ---------------------------------------------------------------- 誘導つき DFS
def search2(A, m, f=b2d3, Lmax=None, SL=4, lo=None, hi='A', nodecap=300000,
            allb=False, T=None):
    """`m_imgclosed.search` と同じ木を、像の枝刈りを **`isstd` より先に**当てて歩く。

    返り値 (T, Bs, ('ok'|'cap', 節点数))。'ok' は「その SL の枝刈りの下では
    歩き切った」。節点は `m_imgclosed.search` と数え方が違う（像の枝刈りを
    通ったものだけ数える）ので、同じ `nodecap` でも**ずっと広く**歩く。

    順を入れ替えてよい理由: 標準形の接頭辞は標準形なので、標準形でない P の
    先に標準形は無い。だから P を捨てる順序は答えに効かない。像 f(P) が
    目標 T に一致した枝だけは、`isstd(P)` を最後に確かめてから拾う。"""
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
                    try:
                        Q = f(P)
                    except Exception:
                        Q = None          # 像が取れないときは像で切らない
                    if Q == T:
                        if isstd(P, 'BMS'):
                            out.append(P)
                            if not allb:
                                done[0] = True
                                return
                        continue          # 一致した枝の先には伸ばさない
                    if Q is not None:
                        if len(Q) > LT + SL:
                            continue
                        if lcp(Q, T) < len(Q) - SL:
                            continue
                    if not isstd(P, 'BMS'):
                        continue
                    cnt[0] += 1
                    if cnt[0] >= nodecap:
                        hitcap[0] = True
                        return
                    rec(P, fp, l2, h2)
                    if done[0] or hitcap[0]:
                        return

    rec((), [], lo_state([], flo), hi_state([], fhi))
    return T, out, ('cap' if (hitcap[0] and not out) else 'ok', cnt[0])


# 梯子: (SL, 節点上限, 下限を使うか, |T| に足す列数)
# `m_imgclosed.LADDER_SCAN` から SL=2 の段を落としたもの（SL=4 の段が同じ木の
# 上位集合を歩くので、`search2` の速さなら要らない）。
#
# **節点上限の目盛りは `m_imgclosed` と違う。** `search2` は像の枝刈りを通った
# ものだけ数えるので、同じ数字がずっと広い木にあたる。既知の一番きつい救出
#   A=(0,0,0)(1,1,1)(2,1,0)(3,0,0) m=2, T 6 列, B 8 列（slack 4 の縮約）
# は SL=4 の段の **2059 節点目**で出た（1.0s）。だから採点用は 4000 で足りる。
LADDER_FAST = ((4, 4000, True, None), (6, 4000, True, None),
               (3, 3000, False, 3))
# 念入り（節点数は `m_imgclosed.LADDER_SCAN` と同じ数字。`search2` は同じ数字で
# ずっと広く歩くので、これは「上の 6 倍かける」段位に当たる）。
# `score(..., ladder=LADDER_FULL)` / `imgclosed_fast(..., ladder=LADDER_FULL)`。
LADDER_FULL = ((4, 25000, True, None), (6, 25000, True, None),
               (3, 15000, False, 3))
# 深追い用（1 件を確かめるとき）。
LADDER_DEEP = ((6, 200000, True, None), (8, 200000, True, None),
               (10, 200000, True, None), (6, 100000, False, 4))


def capfor(cap, T, scale=8):
    """節点上限を |T| で割り引く（下限は cap/4）。

    1 節点の値段は |T| とともに速く増える（実測: |T|=9 で 0.9ms、|T|=16 で
    4.5ms。木が深くなるうえ `conv3` 自体が列数に比例する）。割り引かないと
    走査の時間が長い目標だけで決まってしまう。**節点で切るので、同じ変換器
    なら答えはいつも同じ**（時間で切ると機械の混み具合で答えが揺れる）。"""
    return max(cap // 4, cap * scale // max(scale, len(T)))


def find2(A, m, f=b2d3, ladder=LADDER_FAST, T=None, usefast=True, d2b3=None,
          scale=8):
    """1 対の逆像を 1 つ。返り値 (T, B or None, 段, 節点数, 打ち切りか)。"""
    if d2b3 is None:
        from inv3 import d2b3
    if T is None:
        T = tuple(expand(f(A), m))
    if usefast:
        try:
            B = d2b3(T)
        except Exception:
            B = None
        if (B and isstd(B, 'BMS') and all(c[2] <= 1 for c in B)
                and tuple(f(list(B))) == T):
            return T, tuple(B), 'd2b3', 0, False
    tot, capped = 0, False
    for SL, cap, uselo, extra in ladder:
        Lmax = (len(T) + extra) if extra is not None else None
        # m=1 は下限 A<m-1> が無い（実測でも下限を破る逆像は全部 m=1）。
        lo = None if (uselo and m > 1) else False
        _, Bs, st = search2(A, m, f=f, SL=SL, Lmax=Lmax,
                            lo=lo, nodecap=capfor(cap, T, scale), T=T)
        tot += st[1]
        if st[0] == 'cap':
            capped = True
        if Bs:
            return T, Bs[0], 'SL%d%s' % (SL, '' if uselo else '/nolo'), tot, False
    return T, None, 'none', tot, capped


# ---------------------------------------------------------------- 返り値
class Res(tuple):
    """`(ok, tot, bad)` の 3 つ組として振る舞う（`rows3.imgclosed_fast` と同じ形）。
    詳しい中身は属性で持つ:
      badpairs 逆像が見つからなかった (A, m, T) / capped そのうち打ち切ったもの
      rescued  d2b3 が外れたが探索が救出した (A, m, B) / hits d2b3 が当たった数
      times    段 2 の 1 対ごとの (秒, 節点, |T|, A, m)（重い順）
      secs     秒 / stages 段ごとの件数"""
    def __new__(cls, ok, tot, bad, **kw):
        r = tuple.__new__(cls, (ok, tot, bad))
        for k, v in kw.items():
            setattr(r, k, v)
        return r

    def line(self):
        return ('ImgClosedT m<=%d: 逆像あり %d / %d 対   破れた A %d 個'
                '（対 %d, うち打ち切り %d）  d2b3 %d / 救出 %d  %.0fs'
                % (self.mmax, self[0], self[1], len(self[2]),
                   len(self.badpairs), len(self.capped),
                   self.hits, len(self.rescued), self.secs))


# ---------------------------------------------------------------- 並列の中身
_F = b2d3          # fork で子に渡す（pickle しない）
_MMAX = 3
_LADDER = LADDER_FAST
_D = None          # 逆写像（既定は inv3.d2b3）


def _clear():
    core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()


def _w_fast(chunk):
    """段 1: `d2b3` を当てるだけ。返り値 (当たり数, 外れた (A,m,T) の並び)。"""
    d2b3 = _D
    if d2b3 is None:
        from inv3 import d2b3
    ok, miss = 0, []
    for j, M in enumerate(chunk):
        if j % 500 == 0:
            _clear()
        N = _F(list(M))
        for m in range(1, _MMAX + 1):
            T = tuple(expand(N, m))
            try:
                B = d2b3(T)
            except Exception:
                B = None
            if (B and isstd(B, 'BMS') and all(c[2] <= 1 for c in B)
                    and tuple(_F(list(B))) == T):
                ok += 1
            else:
                miss.append((M, m, T))
    _clear()
    return ok, miss


def _w_slow(task):
    """段 2: 外れた 1 対を誘導つき探索に落とす。"""
    M, m, T = task
    t0 = time.time()
    _, B, stage, nodes, cap = find2(M, m, f=_F, ladder=_LADDER, T=T,
                                    usefast=False)
    _clear()
    return M, m, T, B, stage, nodes, cap, time.time() - t0


def _chunks(xs, n):
    return [xs[i::n] for i in range(n)]


# ---------------------------------------------------------------- 本体
def imgclosed_fast(f, A, mmax=3, d2b3=None, jobs=None, ladder=LADDER_FAST,
                   fallback=True, verbose=0):
    """ImgClosedT を測る。`A` は BMS 3 行 z<2 標準形の並び（|A|<=1 は飛ばす）。

    `jobs=None` で CPU 数、`jobs=1` で逐次。`fallback=False` なら `d2b3` を
    当てるだけ（`rows3.imgclosed_fast` と完全に同じ答え・同じ速さ）。
    `d2b3` は逆写像（既定は `inv3.d2b3`。`rows3.check` からそのまま渡せる）。
    返り値は `Res`（`(ok, tot, bad)` の 3 つ組 ＋ 属性）。"""
    global _F, _MMAX, _LADDER, _D
    t0 = time.time()
    A = [tuple(M) for M in A if len(M) > 1]
    _F, _MMAX, _LADDER, _D = f, mmax, ladder, d2b3
    if jobs is None:
        jobs = min(os.cpu_count() or 1, 28)
    if mp.current_process().daemon:
        jobs = 1          # 子プロセスの中から呼ばれたら fork しない
    jobs = max(1, min(jobs, max(1, len(A))))
    _clear()
    # ---- 段 1
    if jobs == 1:
        res1 = [_w_fast(A)]
    else:
        ctx = mp.get_context('fork')
        with ctx.Pool(jobs) as pool:
            res1 = pool.map(_w_fast, _chunks(A, jobs * 2))
    hits = sum(r[0] for r in res1)
    miss = [x for r in res1 for x in r[1]]
    tot = len(A) * mmax
    ok = hits
    bad, badpairs, capped, rescued, times = set(), [], [], [], []
    stages = collections.Counter({'d2b3': hits})
    # ---- 段 2
    if fallback and miss:
        miss.sort(key=lambda t: (len(t[2]), key(t[0]), t[1]), reverse=True)
        if jobs == 1:
            it = (_w_slow(t) for t in miss)
        else:
            ctx = mp.get_context('fork')
            pool = ctx.Pool(jobs)
            it = pool.imap_unordered(_w_slow, miss, chunksize=1)
        done = 0
        for M, m, T, B, stage, nodes, cap, sec in it:
            done += 1
            stages[stage] += 1
            times.append((sec, nodes, len(T), M, m))
            if B is not None:
                ok += 1
                rescued.append((M, m, tuple(B)))
            else:
                bad.add(M)
                badpairs.append((M, m, T))
                if cap:
                    capped.append((M, m))
            if verbose and (done % 25 == 0 or done == len(miss)):
                print('    段 2: %d/%d  破れ %d  (%.0fs)'
                      % (done, len(miss), len(badpairs), time.time() - t0),
                      flush=True)
        if jobs > 1:
            pool.close(); pool.join()
    elif miss:
        for M, m, T in miss:
            bad.add(M)
            badpairs.append((M, m, T))
            capped.append((M, m))
        stages['あきらめ'] = len(miss)
    times.sort(reverse=True)
    return Res(ok, tot, bad, badpairs=badpairs, capped=capped,
               rescued=rescued, hits=hits, mmax=mmax, stages=stages,
               times=times, secs=time.time() - t0, njobs=jobs)


def score(f=b2d3, lim=5, mmax=3, zcap=1, jobs=None, verbose=1,
          ladder=LADDER_FAST, fallback=True):
    """`gen3` を回してから採点。返り値は `Res`。
    `fallback=False` なら段 1（`d2b3` を当てるだけ）で止める＝破れの甘い上界。"""
    t0 = time.time()
    A = [M for M in sorted(gen3('BMS', lim, zcap=zcap), key=key) if len(M) > 1]
    if verbose:
        print('BMS 3 行 z<=%d 標準形 (2..%d 列): %d 個 x m=1..%d = %d 対  (%.1fs)'
              % (zcap, lim, len(A), mmax, len(A) * mmax, time.time() - t0),
              flush=True)
    r = imgclosed_fast(f, A, mmax, jobs=jobs, verbose=verbose, ladder=ladder,
                       fallback=fallback)
    if verbose:
        print('  ' + r.line())
        print('  段: %s   並列 %d' % (sorted(r.stages.items()), r.njobs))
        if r.rescued:
            print('  --- d2b3 が外れて探索が救出した %d 対 ---' % len(r.rescued))
            for M, m, B in r.rescued[:8]:
                print('    %-34s m=%d  B=%s' % (show(M), m, show(B)))
        if r.times:
            tt = [t[0] for t in r.times]
            print('  段 2 の 1 対の秒: 合計 %.0f / 最大 %.1f / 中央 %.1f  '
                  '(%d 対, %d 並列)'
                  % (sum(tt), tt[0], tt[len(tt) // 2], len(tt), r.njobs))
            for sec, nodes, lt, M, m in r.times[:5]:
                print('    %5.1fs 節点 %6d |T|=%2d  %-34s m=%d'
                      % (sec, nodes, lt, show(M), m))
        if r[2]:
            bl = collections.Counter(len(M) for M in r[2])
            print('  破れた A の列数別: %s' % sorted(bl.items()))
            for M in sorted(r[2], key=key)[:8]:
                print('    NG %-34s -> %s' % (show(M), show(f(list(M)))))
    return r


# ---------------------------------------------------------------- 答え合わせ
def _w_mi(task):
    """`m_imgclosed` の遅い版で 1 対。"""
    M, m, T, which = task
    import m_imgclosed as mi
    ladder = mi.LADDER if which == 'full' else mi.LADDER_SCAN
    t0 = time.time()
    _, B, stage, nodes, cap = mi.find(M, m, f=_F, ladder=ladder, T=T)
    _clear()
    return M, m, (B is not None), stage, nodes, cap, time.time() - t0


def cmd_valid(lim=4, mmax=3, zcap=1, jobs=None, which='scan'):
    """`m_imgclosed.find`（**遅い版**）と結論（逆像あり / なし）を全対で
    突き合わせる。食い違えば速い版が誤り。

    `which='scan'` は `m_imgclosed.LADDER_SCAN`（`m_imgclosed.py scan` が使う
    梯子＝NOTES の表を出したもの）、`which='full'` は既定の `LADDER`
    （1 件 62 万節点。<=4 列でも 1 対に 30 分以上かかる対があるので注意）。
    どちらも `m_imgclosed.search`（像の枝刈りが `isstd` の**後**）で歩く。"""
    global _F, _LADDER
    _F, _LADDER = b2d3, LADDER_FAST
    A = [tuple(M) for M in sorted(gen3('BMS', lim, zcap=zcap), key=key)
         if len(M) > 1]
    print('突き合わせ: <=%d 列 z<=%d %d 個 x m<=%d = %d 対  遅い梯子 %s'
          % (lim, zcap, len(A), mmax, len(A) * mmax, which), flush=True)
    r = imgclosed_fast(b2d3, A, mmax, jobs=jobs, verbose=1)
    print('  速い版: %s' % r.line(), flush=True)
    ng = set((M, m) for M, m, _ in r.badpairs)
    tasks = []
    for M in A:
        N = b2d3(list(M))
        for m in range(1, mmax + 1):
            tasks.append((M, m, tuple(expand(N, m)), which))
    if jobs is None:
        jobs = min(os.cpu_count() or 1, 28)
    t0 = time.time()
    ctx = mp.get_context('fork')
    dis, done = [], 0
    with ctx.Pool(min(jobs, len(tasks))) as pool:
        for M, m, slow, stage, nodes, cap, sec in pool.imap_unordered(
                _w_mi, tasks, chunksize=1):
            done += 1
            fst = (M, m) not in ng
            if slow != fst:
                dis.append((M, m, slow, fst, stage))
                print('    食い違い %-34s m=%d 遅い=%s 速い=%s (%s)'
                      % (show(M), m, slow, fst, stage), flush=True)
            if done % 500 == 0:
                print('    遅い版 %d/%d  (%.0fs)'
                      % (done, len(tasks), time.time() - t0), flush=True)
    print('--- 結論の食い違い %d / %d 対  (遅い版 %.0fs, 並列 %d) ---'
          % (len(dis), len(tasks), time.time() - t0, jobs))
    return dis


def _w_vwin(task):
    """1 対を「枝刈りなしの全数」と「梯子」の両方で解く。"""
    M, m, T, cap = task
    from m_imgclosed import preimages
    t0 = time.time()
    _, Bs, trunc, nw = preimages(M, m, f=_F, cap=cap)
    ta = time.time() - t0
    t0 = time.time()
    _, B, stage, nodes, capd = find2(M, m, f=_F, ladder=_LADDER, T=T,
                                     usefast=False)
    _clear()
    return M, m, T, set(Bs), trunc, nw, B, stage, ta, time.time() - t0


def cmd_vwin(lim=3, mmax=2, tmax=6, jobs=None, zcap=1, cap=400000):
    """**枝刈りを一切しない全数**（`m_imgclosed.preimages`）と梯子を突き合わせる。

    `valid`（`m_imgclosed.find` との突き合わせ）は両方とも `d2b3` が先に当たって
    しまうので探索そのものを試せない。こちらは `d2b3` を使わずに
      * 全数が逆像を持つのに梯子が「なし」と言う（＝ SL の枝刈りで取り逃がす）
      * 梯子が出した B が全数の集合に無い（＝ こちらのバグ）
    の 2 つを数える。窓は RD1 の [A<max(m-1,1)>, A)、列数は ceil(1.5|T|) まで。"""
    global _F, _LADDER
    _F, _LADDER = b2d3, LADDER_FAST
    A = [tuple(M) for M in sorted(gen3('BMS', lim, zcap=zcap), key=key)
         if len(M) > 1]
    tasks = []
    for M in A:
        N = b2d3(list(M))
        for m in range(1, mmax + 1):
            T = tuple(expand(N, m))
            if len(T) <= tmax:
                tasks.append((M, m, T, cap))
    print('全数と突き合わせ: <=%d 列 %d 個 x m<=%d のうち |T|<=%d の %d 対'
          % (lim, len(A), mmax, tmax, len(tasks)), flush=True)
    if jobs is None:
        jobs = min(os.cpu_count() or 1, 28)
    t0 = time.time()
    ctx = mp.get_context('fork')
    with ctx.Pool(min(jobs, max(1, len(tasks)))) as pool:
        res = list(pool.imap_unordered(_w_vwin, tasks, chunksize=1))
    lost, wrong, trunc, both0 = [], [], 0, 0
    for M, m, T, Bs, tr, nw, B, stage, ta, tb in res:
        if tr:
            trunc += 1
        if B is not None and B not in Bs and not tr:
            wrong.append((M, m, B))
        if Bs and B is None:
            lost.append((M, m, len(Bs)))
        if not Bs and B is None:
            both0 += 1
    print('  全数が空 & 梯子も なし : %d 対（両方「像の外」）' % both0)
    print('  全数は逆像を持つのに梯子が取り逃がした : %d 対' % len(lost))
    for M, m, k in lost[:8]:
        print('    取り逃がし %-30s m=%d （全数は %d 個）' % (show(M), m, k))
    print('  梯子の B が全数の集合に無い（バグ） : %d 対' % len(wrong))
    for M, m, B in wrong[:8]:
        print('    ずれ %-30s m=%d  B=%s' % (show(M), m, show(B)))
    print('  全数が打ち切りに当たった対 : %d' % trunc)
    print('  (%.0fs, 並列 %d)' % (time.time() - t0, jobs))
    return lost, wrong


def cmd_one(spec, m, f=b2d3, ladder=LADDER_DEEP):
    M = parse(spec, 3)
    t0 = time.time()
    T, B, stage, nodes, cap = find2(M, m, f=f, ladder=ladder)
    print('A      %s  (%d 列)' % (show(M), len(M)))
    print('T=<%d>  %s  (%d 列, DBMS 標準形 %s)' % (m, show(T), len(T),
                                                  isstd(T, 'DBMS')))
    print('逆像   %s' % (show(B) if B else 'なし'))
    print('  段 %s  節点 %d  打ち切り %s  %.1fs'
          % (stage, nodes, cap, time.time() - t0))
    return B


def cmd_est(lim, mmax=3, zcap=1, ns=150, jobs=None, seed=1):
    """走らせる前の見積もり。**標本を実際に測って**外挿する（当てずっぽうにしない）。

    段 1 は逐次で測って 1 対の CPU 秒を出し、段 2 はその標本の外れだけを
    並列で回して 1 対の CPU 秒を出す。どちらも列数が増えると 1 対が高くなる
    （木が深くなり `conv3` も長くなる）ので、**測る対象と同じ `lim` で**測る。"""
    import random
    t0 = time.time()
    A = [tuple(M) for M in sorted(gen3('BMS', lim, zcap=zcap), key=key)
         if len(M) > 1]
    N = len(A) * mmax
    tg = time.time() - t0
    if jobs is None:
        jobs = min(os.cpu_count() or 1, 28)
    random.seed(seed)
    S = random.sample(A, min(ns, len(A)))
    print('<=%d 列 z<=%d: A %d 個 x m<=%d = %d 対  (gen3 %.0fs)  標本 %d 個'
          % (lim, zcap, len(A), mmax, N, tg, len(S)), flush=True)
    r1 = imgclosed_fast(b2d3, S, mmax, jobs=1, fallback=False)
    rate1 = r1.secs / max(1, r1[1])
    p = len(r1.badpairs) / max(1, r1[1])
    print('  段 1: 標本 %d 対を逐次 %.0fs -> 1 対 %.1fms、外れ %.2f%%'
          % (r1[1], r1.secs, rate1 * 1000, p * 100))
    r2 = imgclosed_fast(b2d3, S, mmax, jobs=jobs)
    cpu2 = sum(t[0] for t in r2.times)
    rate2 = cpu2 / max(1, len(r2.times))
    print('  段 2: 標本の外れ %d 対で CPU %.0fs -> 1 対 %.0fs（救出 %d）'
          % (len(r2.times), cpu2, rate2, len(r2.rescued)))
    e1 = rate1 * N / jobs
    e2 = p * N * rate2 / jobs
    print('  見積もり（%d 並列）: 段 1 %.0fs ＋ 段 2 %.0fs = **%.0f 分**'
          % (jobs, e1, e2, (e1 + e2) / 60))
    print('  （段 1 だけなら %.0fs。fast コマンド）' % e1)
    return e1, e2


if __name__ == '__main__':
    a = sys.argv[1:] or ['scan', '5']
    cmd = a[0]
    if cmd in ('scan', 'fast'):
        score(b2d3,
              int(a[1]) if len(a) > 1 else 5,
              int(a[2]) if len(a) > 2 else 3,
              int(a[3]) if len(a) > 3 else 1,
              int(a[4]) if len(a) > 4 else None,
              fallback=(cmd == 'scan'))
    elif cmd == 'valid':
        cmd_valid(int(a[1]) if len(a) > 1 else 4,
                  int(a[2]) if len(a) > 2 else 3,
                  int(a[3]) if len(a) > 3 else 1,
                  int(a[4]) if len(a) > 4 else None,
                  a[5] if len(a) > 5 else 'scan')
    elif cmd == 'vwin':
        cmd_vwin(int(a[1]) if len(a) > 1 else 3,
                 int(a[2]) if len(a) > 2 else 2,
                 int(a[3]) if len(a) > 3 else 6,
                 int(a[4]) if len(a) > 4 else None)
    elif cmd == 'one':
        cmd_one(a[1], int(a[2]))
    elif cmd == 'est':
        cmd_est(int(a[1]), int(a[2]) if len(a) > 2 else 3,
                int(a[3]) if len(a) > 3 else 1,
                int(a[4]) if len(a) > 4 else 150)
    else:
        print(__doc__)
