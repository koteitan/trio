# -*- coding: utf-8 -*-
"""**(PREV-1)(PREV-2)(PREV-3) —— H12 の `nextrel1_snoc_prev` は距離 1 の場面を覆うか。**

## 逐語（`lean/H12Export.lean:5206`）

    theorem nextrel1_snoc_prev {C : TrioSeq} {p : N x N x N} (hC : C != [])
        (h0 : entry C 0 (C.length - 1) < p.1)
        (h1 : entry C 1 (C.length - 1) < p.2.1) :
        nextrel1 (C ++ [p]) (C.length - 1) C.length

## 母集団（= §R284 と同じ箱）

    シート `psiI.json` の行列 C0（重複除去）、`1 <= k < |C0|`
    `C = C0[:k]`、`p = C0[k]`、`T = C ++ [p] = C0[:k+1]`
    **開いている (WSnocOpen1)** := (a) C に行 2 が正の列がある
                                 (b) srow(T, k) != 0
                                 (c) parent(T, srow(T,k), k) is not None

    **距離** := `k - max{ j < k : C[j][2] > 0 }`（= §R284 の「最も近い行 2 列との距離」）
    **窓長** := `k - c`（`c = parent(T, srow(T,k), k)`）—— `r295` の `V = S[c:|S|-1]` に一致

## 事前の見積もり（測る前に書く）

    (PREV-1) 両立は **60% 程度**と見ます。破れは **行 0 側**が主だと予想。
      ⚠ 反例の形: `C[k-1] = (3,2,1)`, `p = (2,1,0)` —— `p` が浅く戻る手。
        このとき `entry C 0 (k-1) = 3 > 2 = p.1` で **h0 が破れる**。
    (PREV-2) 「直前が親」は距離 1 の 47.41% とは **一致しない**と見ます
      （距離は行 2 の列の位置、親は `srow` に応じた別の関係）。
    (PREV-3) 窓長 = 親までの距離。2 以上が主なら最小形では覆えない。
"""
import sys, time, json
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r263 import load
from r126 import srow


def scenes():
    """開いている場面を全部返す: (C0, k, C, p, T, sr, c)"""
    out = []
    for C0 in load():
        X = [tuple(v) for v in C0]
        for k in range(1, len(X)):
            C = X[:k]; p = X[k]; T = X[:k + 1]
            if not any(q[2] > 0 for q in C): continue      # (a)
            sr = srow(T, k)
            if sr == 0: continue                            # (b)
            c = trio.parent(T, sr, k)
            if c is None: continue                          # (c)
            out.append((X, k, C, p, T, sr, c))
    return out


def dist2(C, k):
    """最も近い行 2 列との距離 k - max(pos)。無ければ None。"""
    ps = [j for j in range(k) if C[j][2] > 0]
    return k - max(ps) if ps else None


def pct(a, b):
    return 100.0 * a / b if b else float('nan')


def main():
    t0 = time.time()
    S = scenes()
    print('== 母集団 ==')
    print('  開いている場面（分母）: %d' % len(S))

    # ---------- (PREV-1) ----------
    print()
    print('== (PREV-1) 距離別に、H12 の 2 不等式が成り立つか ==')
    print('  h0 := C[k-1][0] < p[0] , h1 := C[k-1][1] < p[1]')
    G = {}
    for (X, k, C, p, T, sr, c) in S:
        d = dist2(C, k)
        h0 = C[k - 1][0] < p[0]
        h1 = C[k - 1][1] < p[1]
        key = d if d is not None and d <= 4 else ('>=5' if d is not None else 'なし')
        for kk in (key, 'ALL'):
            g = G.setdefault(kk, Counter())
            g['n'] += 1
            g['h0'] += h0; g['h1'] += h1
            g['both'] += (h0 and h1)
            if not (h0 and h1):
                if not h0 and not h1: g['破:両方'] += 1
                elif not h0: g['破:行0のみ'] += 1
                else: g['破:行1のみ'] += 1
        # srow 別（距離 1 のみ）
        if d == 1:
            g = G.setdefault('距離1/srow=%d' % sr, Counter())
            g['n'] += 1; g['h0'] += h0; g['h1'] += h1; g['both'] += (h0 and h1)
            if not (h0 and h1):
                if not h0 and not h1: g['破:両方'] += 1
                elif not h0: g['破:行0のみ'] += 1
                else: g['破:行1のみ'] += 1

    hdr = '%-18s %8s %9s %9s %9s | %9s %9s %9s' % (
        '群', '分母', 'h0', 'h1', '★両立', '破:行0', '破:行1', '破:両方')
    print(hdr)
    order = [1, 2, 3, 4, '>=5', 'なし', 'ALL', '距離1/srow=1', '距離1/srow=2']
    for kk in order:
        g = G.get(kk)
        if not g: continue
        n = g['n']
        print('%-18s %8d %8.4f%% %8.4f%% %8.4f%% | %8.4f%% %8.4f%% %8.4f%%' % (
            str(kk), n, pct(g['h0'], n), pct(g['h1'], n), pct(g['both'], n),
            pct(g['破:行0のみ'], n), pct(g['破:行1のみ'], n), pct(g['破:両方'], n)))

    # 距離 1 で両立が破れる例
    print()
    print('  ⛔ 距離 1 で両立が破れる例（先頭 5 件）:')
    cnt = 0
    for (X, k, C, p, T, sr, c) in S:
        if dist2(C, k) != 1: continue
        h0 = C[k - 1][0] < p[0]; h1 = C[k - 1][1] < p[1]
        if h0 and h1: continue
        print('    k=%d srow=%d 親=%d 窓長=%d C[k-1]=%s p=%s h0=%s h1=%s'
              % (k, sr, c, k - c, C[k - 1], p, h0, h1))
        cnt += 1
        if cnt >= 5: break
    if cnt == 0: print('    （無し）')

    # ---------- (PREV-2) ----------
    print()
    print('== (PREV-2) 場面全体で「直前が親」（c = k-1）は何 % ==')
    P = {}
    for (X, k, C, p, T, sr, c) in S:
        for kk in ('ALL', 'srow=%d' % sr):
            g = P.setdefault(kk, Counter())
            g['n'] += 1
            g['prev'] += (c == k - 1)
            g['h0h1'] += (C[k - 1][0] < p[0] and C[k - 1][1] < p[1])
            g['prev&h0h1'] += (c == k - 1 and C[k - 1][0] < p[0] and C[k - 1][1] < p[1])
    print('%-10s %8s %12s %12s %14s' % ('群', '分母', '★直前が親', '2不等式', '両方'))
    for kk in ('ALL', 'srow=1', 'srow=2'):
        g = P.get(kk)
        if not g: continue
        n = g['n']
        print('%-10s %8d %11.4f%% %11.4f%% %13.4f%%' % (
            kk, n, pct(g['prev'], n), pct(g['h0h1'], n), pct(g['prev&h0h1'], n)))

    # 2 不等式 => 直前が親（H12 の主張）の実測確認
    bad = 0; tot = 0
    for (X, k, C, p, T, sr, c) in S:
        if C[k - 1][0] < p[0] and C[k - 1][1] < p[1] and sr == 1:
            tot += 1
            if c != k - 1: bad += 1
    print('  ⚠ 健全性チェック（srow=1 かつ 2 不等式 ⟹ 直前が親）: 分母 %d、破れ %d 件' % (tot, bad))

    # 直前が親 vs 距離 1 の一致
    same = both1 = only_prev = only_d1 = 0
    for (X, k, C, p, T, sr, c) in S:
        a = (c == k - 1); b = (dist2(C, k) == 1)
        if a and b: both1 += 1
        elif a: only_prev += 1
        elif b: only_d1 += 1
        else: same += 1
    n = len(S)
    print('  ⟹ 「直前が親」と「距離 1」の一致: 両方 %.4f%% / 親のみ %.4f%% / 距離のみ %.4f%% / どちらも無し %.4f%%'
          % (pct(both1, n), pct(only_prev, n), pct(only_d1, n), pct(same, n)))

    # ---------- (PREV-3) ----------
    print()
    print('== (PREV-3) 親でない場合、窓は何列か（窓長 = k - c） ==')
    W = Counter(); WS = {}
    for (X, k, C, p, T, sr, c) in S:
        w = k - c
        W[w if w <= 5 else '>=6'] += 1
        WS.setdefault('srow=%d' % sr, Counter())[w if w <= 5 else '>=6'] += 1
    n = len(S)
    print('%-8s %10s %10s' % ('窓長', '件数', '割合'))
    for kk in [1, 2, 3, 4, 5, '>=6']:
        if kk in W:
            print('%-8s %10d %9.4f%%' % (str(kk), W[kk], pct(W[kk], n)))
    print('  ⟹ ★ 窓長 1（＝最小形）: %.4f%%、⛔ 窓長 >= 2（＝残り）: %.4f%%'
          % (pct(W[1], n), pct(n - W[1], n)))
    for kk in ('srow=1', 'srow=2'):
        g = WS.get(kk)
        if not g: continue
        m = sum(g.values())
        print('  %s: 分母 %d、窓長 1 = %.4f%%、>=2 = %.4f%%' % (kk, m, pct(g[1], m), pct(m - g[1], m)))

    print()
    print('（%.1f 秒）' % (time.time() - t0))


if __name__ == '__main__':
    main()
