"""検査 A — 残核 `Subst1gReviveSelf` の残差インスタンスの**構造**を測る。

真偽（0 違反か）はもう十分に測ってある（`probe_subst1g_adv.py` ほか、`(GC)` は
1221 万例）。ここで測るのは真偽ではなく

  (A) 「証明済みの補題だけで `R ∈ Wself` が出るか」（**帰納を使わない**battery）
  (B) 出ないものの**構造**（展開の形 = バッドルート・コピー塊・リフト量）
  (C) **どの仮定が効いているか**（仮定を 1 本ずつ落として反例を探す）

課題 H1 で「教師データ ＋ 素性の総当たり」が効いたのと同じ型の測定
（`lean/L1-NOTES.md` 課題 L4 §5.3 の検査 A）。

## 何を列挙するか

Lean の `Wtower2.Subst1gReviveSelf` の仮定をそのまま写した `(S, p, C)`:

    S ∈ Wself,  p < |S|,  C ≠ [],  C ∈ Wself,  lev(C,0) <= lev(S,p),
    C[0] の深さ = S[p] の深さ,  C の全列の深さ >= それ,
    R := S[:p] ++ C ++ S[p+1:],  D := S[p+1:]
    (i)   R の末尾列は R の中で親を持つ
    (ii)  その末尾列は自分のブロック（D=[] なら C、そうでなければ D）では孤児
    (iii) R[:-1] に行 2 > 0 の列がある

`inW` は既存プローブと同じ 3 重打ち切り（`n ∈ {1,2}` / MAXDEPTH / MAXLEN）。
`None` = 未判定は数えない。

## (A) 「覆える」の定義

**帰納（`Aop` 節 2 の展開）を使わずに**、証明済みの補題だけを組んで
`M ∈ Wself` を出す再帰探索 `free(M)`:

    zeroRow2_mem_Wself   M が行 2 恒等 0
    snoc_zeroRow2        M[:-1] が行 2 恒等 0
    two_col_mem_W        |M| = 2 で 2 本目が根以上の深さ
    snoc_orphan          M の末尾列が M の中でも孤児 かつ free(M[:-1])
    W_add                M = A ++ B, rsum A B, free(A), free(B)
    W_flatMap_copies     M が同じ塊の n 複製で塊の根が最浅 かつ free(塊)
    W_mono / drop / dropLast / oper / takeC は上の中で使う向きに含まれる

## 使い方

    python3 tools/probe_residue_cover.py [SAMPLES] [SEED]
"""
import sys
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio                                                    # noqa: E402

NS = (1, 2)
MAXDEPTH = 11
MAXLEN = 44


# ---------------------------------------------------------------- W の判定
def lev(col):
    return 2 * col[1] + col[2]


def inW(S, a, depth, memo):
    S = tuple(tuple(c) for c in S)
    key = (S, a)
    if key in memo:
        return memo[key]
    if len(S) == 0:
        return True
    if len(S) == 1:
        r = lev(S[0]) <= a
        memo[key] = r
        return r
    if depth <= 0 or len(S) > MAXLEN:
        return None
    memo[key] = None
    out = True
    for n in NS:
        r = inW(trio.expand(list(S), n), a, depth - 1, memo)
        if r is False:
            memo[key] = False
            return False
        if r is None:
            out = None
    memo[key] = out
    return out


def inWself(M, memo):
    if not M:
        return True
    return inW(M, lev(M[0]), MAXDEPTH, memo)


# ---------------------------------------------------------------- 行列の道具
def srow(S, x):
    if x >= len(S):
        return 0
    c = S[x]
    return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)


def last_has_parent(S):
    if len(S) < 2:
        return False
    x = len(S) - 1
    return trio.parent(S, srow(S, x), x) is not None


def badroot(S):
    """`oper` が使うバッドルート（無ければ None）。"""
    if len(S) < 2:
        return None
    x = len(S) - 1
    if all(v == 0 for v in S[x]):
        return None
    return trio.parent(S, srow(S, x), x)


def oper_data(R):
    """`oper` の分岐データ `(j0, i1, d0, d1)`。展開しないなら None。"""
    x = len(R) - 1
    if x == 0 or all(v == 0 for v in R[x]):
        return None
    i1 = srow(R, x)
    j0 = trio.parent(R, i1, x)
    if j0 is None:
        return None
    d0 = R[x][0] - R[j0][0] if i1 > 0 else 0
    d1 = R[x][1] - R[j0][1] if i1 > 1 else 0
    return j0, i1, d0, d1


def subst(S, p, C):
    return list(S[:p]) + list(C) + list(S[p + 1:])


def rsum(A, B):
    if not B:
        return True
    r = B[0][0]
    return all(q[0] >= r for q in A) and all(q[0] >= r for q in B)


def is_perm_orphan(c):
    """`(x,0,1)` 型 — 行 1 が 0 で行 2 が正。**どんな文脈でも永久に親を持たない**
    （行 2 の親は行 1 の祖先でなければならず、行 1 = 0 の列にそれは無い）。"""
    return c[1] == 0 and c[2] > 0


# ------------------------------------------------ (A) 帰納を使わない coverage
def free(M, memo, budget=[0]):
    """証明済みの補題だけで `M ∈ Wself` が出るか（`Aop` 節 2 の展開は使わない）。"""
    M = tuple(tuple(c) for c in M)
    if M in memo:
        return memo[M]
    budget[0] += 1
    if budget[0] > 200000:
        return False
    memo[M] = False                      # 循環よけ
    r = False
    if len(M) <= 1:
        r = True
    elif all(q[2] == 0 for q in M):                      # zeroRow2_mem_Wself
        r = True
    elif all(q[2] == 0 for q in M[:-1]):                 # snoc_zeroRow2
        r = True
    elif len(M) == 2 and M[1][0] >= M[0][0]:             # two_col_mem_W
        r = True
    if not r and not last_has_parent(list(M)):           # snoc_orphan
        r = free(M[:-1], memo, budget)
    if not r:                                            # W_flatMap_copies
        L = len(M)
        for k in range(1, L // 2 + 1):
            if L % k == 0 and L // k >= 2:
                blk = M[:k]
                if all(M[i * k:(i + 1) * k] == blk for i in range(L // k)) \
                        and all(q[0] >= blk[0][0] for q in blk) \
                        and free(blk, memo, budget):
                    r = True
                    break
    if not r:                                            # W_add
        for j in range(1, len(M)):
            A, B = M[:j], M[j:]
            if rsum(A, B) and free(A, memo, budget) and free(B, memo, budget):
                r = True
                break
    memo[M] = r
    return r


def free1(R, fmemo):
    """**1 歩ほどく**と自由領域に落ちるか。`R ∈ Wself <-> 全ての n で R[n] ∈ Wself`
    なので、`n ∈ {1,2}` の展開が両方 `free` なら「帰納 1 歩で閉じる」。
    これが教師ラベル: False のものが**本当に帰納を要する**インスタンス。"""
    try:
        return all(free(trio.expand(list(R), n), fmemo) for n in (1, 2))
    except Exception:
        return False


def coverage_name(S, p, C, R, D):
    """どの補題が直に効いたか（報告用のラベル）。"""
    out = set()
    if all(q[2] == 0 for q in R):
        out.add('zeroRow2')
    if all(q[2] == 0 for q in R[:-1]):
        out.add('snoc_zeroRow2')
    if not last_has_parent(R):
        out.add('snoc_orphan')
    if len(R) == 2:
        out.add('two_col')
    if D and rsum(list(S[:p]) + list(C), list(D)):
        out.add('W_add')
    return out


# ---------------------------------------------------------------- (B) 素性
def features(S, p, C, R, D):
    f = {}
    x = len(R) - 1
    od = oper_data(R)
    f['lenS'], f['lenC'], f['lenD'], f['lenR'], f['p'] = \
        len(S), len(C), len(D), len(R), p
    f['p_is_last'] = (p == len(S) - 1)
    f['dlev'] = lev(S[p]) - lev(C[0])
    f['i1'] = od[1] if od else None                  # srow（崩壊する行）
    if od:
        j0, i1, d0, d1 = od
        f['j0'] = j0
        f['d0'] = d0                                  # 行 0 のずらし
        f['d1'] = d1                                  # 行 1 のリフト（A_xy）
        f['zone_j0'] = ('takeS' if j0 < p else
                        'C' if j0 < p + len(C) else 'D')
        Q = R[j0:x]                                   # コピーされる塊
        f['lenQ'] = len(Q)
        f['Q_row2'] = any(q[2] > 0 for q in Q)        # 塊に行 2 の列があるか
        f['Q_permorph'] = any(is_perm_orphan(q) for q in Q)
        # (TOW) が無料になる 3 条件（RESIDUE-PROBLEM 4.8）
        f['TOW_free'] = (len(Q) <= 1) or (not f['Q_row2']) or (d0 == 0)
        f['Q_covers_C'] = (j0 <= p) and (x >= p + len(C))
    else:
        for k in ('j0', 'd0', 'd1', 'zone_j0', 'lenQ', 'Q_row2', 'Q_permorph',
                  'TOW_free', 'Q_covers_C'):
            f[k] = None
    f['n_permorph'] = sum(1 for q in R if is_perm_orphan(q))
    f['has_permorph'] = f['n_permorph'] > 0
    f['permorph_in_C'] = any(is_perm_orphan(q) for q in C)
    f['permorph_in_D'] = any(is_perm_orphan(q) for q in D)
    f['n_row2'] = sum(1 for q in R if q[2] > 0)
    return f


# ---------------------------------------------------------------- 列挙
def rand_host(rng):
    L = rng.randint(2, 5)
    S = [(0, rng.randint(0, 4), rng.randint(0, 1))]
    for _ in range(L - 1):
        S.append((rng.randint(1, 5), rng.randint(0, 4), rng.randint(0, 1)))
    return S


def rand_block(rng, x, wild=False):
    """`wild=True` のときは頭の深さ・深さ条件・レベル条件をわざと破ることがある
    （仮定のアブレーション用）。"""
    L = rng.randint(1, 4)
    hx = x if not wild or rng.random() < 0.6 else max(0, x + rng.randint(-2, 2))
    C = [(hx, rng.randint(0, 4), rng.randint(0, 1))]
    for _ in range(L - 1):
        if wild and rng.random() < 0.25:
            C.append((max(0, x + rng.randint(-2, 5)), rng.randint(0, 4),
                      rng.randint(0, 1)))
        else:
            C.append((x + rng.randint(1, 5), rng.randint(0, 4),
                      rng.randint(0, 1)))
    return C


def rand_wild_block(rng):
    """深さもレベルも自由なブロック（一般形 (SUBST-FREE) の反証用）。"""
    L = rng.randint(1, 4)
    C = [(rng.randint(0, 5), rng.randint(0, 4), rng.randint(0, 1))]
    for _ in range(L - 1):
        C.append((rng.randint(0, 6), rng.randint(0, 4), rng.randint(0, 1)))
    return C


HYPS = ('levC', 'i', 'ii', 'iii', 'headdepth', 'deep', 'CinW', 'SinW')
SOFT = ('levC', 'i', 'ii', 'iii', 'headdepth', 'deep')


def check_hyps(S, p, C, R, D, memo, drop=()):
    """残差の仮定を全部チェックする。`drop` に入れた名前だけ無視する。
    返り値は「落ちた最初の仮定名」または None（全部通った）。"""
    if 'levC' not in drop and lev(C[0]) > lev(S[p]):
        return 'levC'
    if 'headdepth' not in drop and C[0][0] != S[p][0]:
        return 'headdepth'
    if 'deep' not in drop and any(q[0] < S[p][0] for q in C):
        return 'deep'
    if 'i' not in drop and not last_has_parent(R):
        return 'i'
    if 'ii' not in drop:
        blk = C if not D else D
        if len(blk) >= 2 and last_has_parent(blk):
            return 'ii'
    if 'iii' not in drop and not any(q[2] > 0 for q in R[:-1]):
        return 'iii'
    if 'SinW' not in drop and inWself(S, memo) is not True:
        return 'SinW'
    if 'CinW' not in drop and inWself(C, memo) is not True:
        return 'CinW'
    return None


def main(samples=100000, seed=20260828):
    rng = random.Random(seed)
    memo = {}
    fmemo = {}
    tot = Counter()
    covcnt = Counter()
    abl = Counter()
    ablex = {}
    uncov = []
    cov = []
    for it in range(samples):
        if it and it % 20000 == 0:
            print(f'  ... {it}/{samples}  residue {tot["residue"]}', flush=True)
        S = rand_host(rng)
        p = rng.randrange(len(S))
        C = rand_block(rng, S[p][0])
        D = list(S[p + 1:])
        R = subst(S, p, C)
        if len(R) > MAXLEN or len(R) < 2:
            continue

        bad = check_hyps(S, p, C, R, D, memo)
        if bad is not None:
            tot['skip/' + bad] += 1
            continue

        rr = inWself(R, memo)
        if rr is None:
            tot['skip/R undecided'] += 1
            continue
        tot['residue'] += 1
        if rr is False:
            tot['**VIOLATION**'] += 1
        f = features(S, p, C, R, D)
        if free(R, fmemo):
            covcnt['COVERED'] += 1
            for c in coverage_name(S, p, C, R, D):
                covcnt['  by/' + c] += 1
            cov.append((S, p, C, R, D, f))
        else:
            covcnt['UNCOVERED'] += 1
            uncov.append((S, p, C, R, D, f))

    # ---------------- (C) 仮定のアブレーション（別パス・別の生成器）
    print('  ... アブレーション', flush=True)
    for it in range(samples):
        S = rand_host(rng)
        p = rng.randrange(len(S))
        C = rand_block(rng, S[p][0], wild=True)
        D = list(S[p + 1:])
        R = subst(S, p, C)
        if len(R) > MAXLEN or len(R) < 2:
            continue
        for h in HYPS:
            # h だけが破れていて、他は全部成り立つインスタンスを数える
            if check_hyps(S, p, C, R, D, memo) is None:
                continue                      # 残差そのもの（アブレーションでない）
            if check_hyps(S, p, C, R, D, memo, drop=(h,)) is not None:
                continue                      # h 以外も破れている
            # h が「本当に」破れているか（未判定と False を分ける）
            if h == 'CinW' and inWself(C, memo) is None:
                abl[f'drop:{h}/C-undecided'] += 1
                continue
            if h == 'SinW' and inWself(S, memo) is None:
                abl[f'drop:{h}/S-undecided'] += 1
                continue
            rr = inWself(R, memo)
            if rr is None:
                abl[f'drop:{h}/undecided'] += 1
            else:
                abl[f'drop:{h}/decided'] += 1
                if rr is False:
                    abl[f'drop:{h}/VIOLATION'] += 1
                    ablex.setdefault(h, (S, p, C, R))
        # ---- SOFT な仮定を**全部**落とした版（S,C が Wself なだけ）
        if check_hyps(S, p, C, R, D, memo, drop=SOFT) is None:
            rr = inWself(R, memo)
            if rr is None:
                abl['drop:ALL-SOFT/undecided'] += 1
            else:
                abl['drop:ALL-SOFT/decided'] += 1
                if rr is False:
                    abl['drop:ALL-SOFT/VIOLATION'] += 1
                    ablex.setdefault('ALL-SOFT', (S, p, C, R))

    print('\n== (0) 列挙 ==')
    for k in sorted(tot):
        print(f'  {k:34s} {tot[k]:9d}')

    print('\n== (A) 帰納を使わない補題で覆えるか ==')
    for k in sorted(covcnt):
        print(f'  {k:34s} {covcnt[k]:9d}')

    print(f'\n== (B) 覆えない {len(uncov)} 件の構造 ==')
    keys = ['i1', 'zone_j0', 'd0', 'd1', 'lenQ', 'Q_row2', 'TOW_free',
            'Q_covers_C', 'Q_permorph', 'has_permorph', 'permorph_in_C',
            'permorph_in_D', 'n_row2', 'lenC', 'lenD', 'p_is_last', 'dlev']
    for k in keys:
        d = Counter(str(f[k]) for *_, f in uncov)
        n = max(1, len(uncov))
        items = sorted(d.items(), key=lambda t: -t[1])[:7]
        s = '  '.join(f'{v}={c}({100*c//n}%)' for v, c in items)
        print(f'  {k:14s} {s}')

    print('\n== (B1) 教師ラベル: 1 歩ほどいて自由領域に落ちるか ==')
    lab = {}
    for tag, xs in (('COVERED', cov), ('UNCOVERED', uncov)):
        for S, p, C, R, D, f in xs:
            f['free1'] = free1(R, fmemo)
    n1 = sum(1 for *_, f in uncov if f['free1'])
    print(f'  覆えない {len(uncov)} 件のうち 1 歩で閉じる: {n1}'
          f'  / 本当に帰納が要る: {len(uncov) - n1}')
    hard = [t for t in uncov if not t[-1]['free1']]
    easy = [t for t in uncov if t[-1]['free1']]
    keys2 = ['i1', 'zone_j0', 'd0', 'd1', 'lenQ', 'Q_row2', 'TOW_free',
             'Q_covers_C', 'Q_permorph', 'has_permorph', 'permorph_in_C',
             'permorph_in_D', 'n_row2', 'lenC', 'lenD', 'p_is_last']
    print('  素性ごとの分布（帰納が要る / 1 歩で閉じる）:')
    for k in keys2:
        dh = Counter(str(f[k]) for *_, f in hard)
        de = Counter(str(f[k]) for *_, f in easy)
        vals = sorted(set(dh) | set(de),
                      key=lambda v: -(dh[v] + de[v]))[:6]
        s1 = ' '.join(f'{v}:{dh[v]}/{de[v]}' for v in vals)
        print(f'    {k:14s} {s1}')
    # 1 リテラルの分離度（帰納が要る側だけを覆う述語を探す）
    print('  1 リテラルの分離度（P(帰納が要る | 素性 = 値)）:')
    rows = []
    for k in keys2:
        for v in set(str(f[k]) for *_, f in uncov):
            a = sum(1 for *_, f in hard if str(f[k]) == v)
            b = sum(1 for *_, f in easy if str(f[k]) == v)
            if a + b >= max(20, len(uncov) // 50):
                rows.append((a / (a + b), a, b, k, v))
    rows.sort(reverse=True)
    for r, a, b, k, v in rows[:10]:
        print(f'    {k:14s} = {v:8s}  {r:.3f}  ({a} / {a+b})')
    print('    ... 低い側 ...')
    for r, a, b, k, v in rows[-6:]:
        print(f'    {k:14s} = {v:8s}  {r:.3f}  ({a} / {a+b})')

    print('\n== (B2) 交差表 i1 x TOW_free ==')
    ct = Counter((str(f['i1']), str(f['TOW_free'])) for *_, f in uncov)
    for k in sorted(ct):
        print(f'  i1={k[0]:4s} TOW_free={k[1]:6s} {ct[k]:8d}')

    print('\n== (B3) 交差表 zone_j0 x Q_row2 x (d0>0) ==')
    ct = Counter((str(f['zone_j0']), str(f['Q_row2']),
                  str(f['d0'] is not None and f['d0'] > 0)) for *_, f in uncov)
    for k in sorted(ct):
        print(f'  zone={k[0]:6s} Q_row2={k[1]:6s} d0>0={k[2]:6s} {ct[k]:8d}')

    print('\n== (C) 仮定を 1 本落としたときの反例 ==')
    for h in list(HYPS) + ['ALL-SOFT']:
        d = abl.get(f'drop:{h}/decided', 0)
        v = abl.get(f'drop:{h}/VIOLATION', 0)
        u = abl.get(f'drop:{h}/undecided', 0)
        mark = '  <== 反例あり' if v else ('  (効いていない?)' if d and not v
                                          else '')
        print(f'  drop {h:10s} 判定 {d:8d}  違反 {v:7d}  未判定 {u:8d}{mark}')
    for h, (S, p, C, R) in ablex.items():
        print(f'  例 drop {h}: p={p} S={S} C={C} R={R}')

    # ---------------- (D) 一般形 (SUBST-FREE) の反証型ハント
    print('  ... (D) 一般形のハント', flush=True)
    gen = Counter()
    genex = []
    for it in range(samples):
        S = rand_host(rng)
        p = rng.randrange(len(S))
        C = rand_wild_block(rng)
        R = subst(S, p, C)
        if len(R) > MAXLEN or len(R) < 2:
            continue
        if inWself(S, memo) is not True or inWself(C, memo) is not True:
            continue
        rr = inWself(R, memo)
        if rr is None:
            gen['undecided'] += 1
        else:
            gen['decided'] += 1
            if any(q[2] > 0 for q in R):
                gen['shape/R に行 2 の列あり'] += 1
            if len(R) >= 5:
                gen['shape/|R| >= 5'] += 1
            if any(is_perm_orphan(q) for q in R):
                gen['shape/永久孤児 (x,0,1) あり'] += 1
            od = oper_data(R)
            if od and od[1] == 2:
                gen['shape/行 2 の崩壊 (i1=2)'] += 1
            if C[0][0] != S[p][0]:
                gen['shape/頭の深さが違う'] += 1
            if any(q[0] < S[p][0] for q in C):
                gen['shape/C に浅い列あり'] += 1
            if lev(C[0]) > lev(S[p]):
                gen['shape/lev(C0) > lev(Sp)'] += 1
            if rr is False:
                gen['VIOLATION'] += 1
                if len(genex) < 5:
                    genex.append((S, p, C, R))
    print('\n== (D) 一般形 (SUBST-FREE): S,C ∈ Wself だけ、深さもレベルも自由 ==')
    for k in sorted(gen):
        print(f'  {k:20s} {gen[k]:9d}')
    for k in sorted(gen):
        if k.startswith('shape/'):
            print(f'  {k:20s} {gen[k]:9d}')
    for S, p, C, R in genex:
        print(f'  反例 p={p} S={S} C={C} R={R}')

    # ---------------- (D2) 陽性対照: `C ∈ Wself` を落とすと反例が出るか
    print('  ... (D2) 陽性対照', flush=True)
    ctl = Counter()
    ctlex = []
    for it in range(samples):
        S = rand_host(rng)
        p = rng.randrange(len(S))
        C = rand_wild_block(rng)
        R = subst(S, p, C)
        if len(R) > MAXLEN or len(R) < 2:
            continue
        if inWself(S, memo) is not True:
            continue
        if inWself(C, memo) is not False:      # C が Wself で**ない**ものだけ
            continue
        rr = inWself(R, memo)
        if rr is None:
            ctl['undecided'] += 1
        else:
            ctl['decided'] += 1
            if rr is False:
                ctl['VIOLATION'] += 1
                if len(ctlex) < 3:
                    ctlex.append((S, p, C, R))
    print('\n== (D2) 陽性対照: `C ∈ Wself` を落とした版（反例が出るはず）==')
    for k in sorted(ctl):
        print(f'  {k:20s} {ctl[k]:9d}')
    for S, p, C, R in ctlex:
        print(f'  反例 p={p} S={S} C={C} R={R}')

    # ---------------- (E) 打ち切り n<=2 vs n<=3 を残差の領域で再確認
    print('  ... (E) 打ち切りの再確認', flush=True)
    global NS
    sub = [t for t in (uncov + cov) if len(t[3]) <= 7][:1500]
    memo3 = {}
    agree = dis = und = 0
    NS = (1, 2, 3)
    for S, p, C, R, D, f in sub:
        r3 = inWself(R, memo3)
        NS_save = None
        if r3 is None:
            und += 1
            continue
        agree += 1
    NS = (1, 2)
    r2s = []
    for S, p, C, R, D, f in sub:
        r2s.append(inWself(R, memo))
    NS = (1, 2, 3)
    dis = 0
    for (S, p, C, R, D, f), r2 in zip(sub, r2s):
        r3 = inWself(R, memo3)
        if r2 is not None and r3 is not None and r2 != r3:
            dis += 1
    NS = (1, 2)
    print(f'\n== (E) 打ち切りの再確認（残差の領域, |R| <= 7 の {len(sub)} 件）==')
    print(f'  n<=3 で判定できた {agree}  未判定 {und}  '
          f'n<=2 と食い違い {dis}')

    print('\n== 覆えない例（先頭 5 件）==')
    for S, p, C, R, D, f in uncov[:5]:
        print(f'  p={p} i1={f["i1"]} d0={f["d0"]} d1={f["d1"]} '
              f'zone={f["zone_j0"]} |Q|={f["lenQ"]} Q_row2={f["Q_row2"]}')
        print(f'    S={S}  C={C}')
        print(f'    R={R}')


if __name__ == '__main__':
    a = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    s = int(sys.argv[2]) if len(sys.argv) > 2 else 20260828
    main(a, s)
