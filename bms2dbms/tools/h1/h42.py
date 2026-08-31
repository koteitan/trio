# -*- coding: utf-8 -*-
"""**課題 H42 —— 塔を 1 段足したとき、バッドルートは新しい段に入るか、逃げるか。**

H41 で `M⟦n⟧ = A ++ B_0 ++ … ++ B_{n-1}`（`B_k` は `k` だけの関数）が
シート 4482 行**すべて**で成り立つと分かった。`T_k := M⟦k+1⟧ = A ++ B_0 ++ … ++ B_k`。

    `T_{k+1}` のバッドルート = parent(T_{k+1}, srow(末尾), 末尾)

これが

    **新しい段 `B_{k+1}` の中**  ⟹ 復活なし（「深い側に足す」だけで済む）
    **前の段 `B_j` (j <= k)**    ⟹ **復活**（ホスト側へ逃げる）
    **`A` の中**                 ⟹ **復活**（いちばん遠くへ逃げる）
    **親が無い**                 ⟹ 孤児（`dropLast` に潰れる）

⚠ `probe_subst1g.py` / `probe_subst1g_adv.py` は**退化した `inW`** を使うので
   所属判定には使えない（課題 H36）。**ここは所属を一切使わない構造の測定**。

使い方: python3 h1/h42.py [K] [行数の上限]
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
import r66, trio, h41
import wcert as wc
from collections import Counter

K = int(sys.argv[1]) if len(sys.argv) > 1 else 4
LIM = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def badroot(S):
    j = len(S) - 1
    if tuple(S[j]) == (0, 0, 0):
        return 'zero'
    return trio.parent([tuple(c) for c in S], srow(S, j), j)


def layout(M, N):
    """(a, b, [M[1..N]]) —— A の長さ a と段の幅 b。塔でなければ None。"""
    E = {n: [tuple(c) for c in trio.expand(list(M), n)] for n in range(1, N + 1)}
    L = [len(E[n]) for n in range(1, N + 1)]
    if len(set(L)) == 1:
        return None
    b = L[1] - L[0]
    a = L[0] - b
    if b <= 0 or a < 0 or any(L[n - 1] != a + n * b for n in range(1, N + 1)):
        return None
    return a, b, E


def where(M, K):
    """k = 0..K-1 について `T_{k+1}` のバッドルートの行き先を返す。"""
    lay = layout(M, K + 2)
    if lay is None:
        return None
    a, b, E = lay
    out = []
    for k in range(K):
        T = E[k + 2]                      # T_{k+1} = M[k+2]、段は 0..k+1
        r = badroot(T)
        if r is None:
            out.append(('孤児', None))
        elif r == 'zero':
            out.append(('末尾が零列', None))
        elif r < a:
            out.append(('**A へ逃げる**', -1))
        else:
            j = (r - a) // b              # 何段目に居るか
            last = k + 1
            if j == last:
                out.append(('新しい段の中', 0))
            else:
                out.append(('**前の段へ逃げる**', last - j))
    return out


if __name__ == '__main__':
    T0 = r66.load_ladder()[:LIM]
    print('母集団: `psiI.json` の 3 行 z<2 **%d 行**（シート行番号順 ＝ 順序数順）'
          % len(T0))
    print('   1 段足す回数 K = %d（`T_1`..`T_K`、つまり `M⟦2⟧`..`M⟦%d⟧`）' % (K, K + 1))
    t0 = time.time()
    res = []
    for row, M, ocf in T0:
        w = where(M, K)
        res.append((row, M, ocf, w))
    print('   (%.0fs)' % (time.time() - t0))
    print()

    # 1. 行ごとの判定（K 回のどこかで逃げたら「逃げる行」）
    kinds = Counter()
    rows_esc = []
    for row, M, ocf, w in res:
        if w is None:
            kinds['塔にならない（H41 の (d)）'] += 1
            continue
        k = set(x[0] for x in w)
        if any('逃げる' in s for s in k):
            kinds['**逃げる（復活する）**'] += 1
            rows_esc.append((row, M, ocf, w))
        elif k <= {'孤児', '末尾が零列'}:
            kinds['全部 孤児 / 零列（`dropLast`）'] += 1
        else:
            kinds['逃げない（新しい段の中）'] += 1
    n = len(res)
    print('**1. 行ごとの内訳**')
    for k, v in kinds.most_common():
        print('   %-40s %5d (%.2f%%)' % (k, v, 100.0 * v / n))
    print()

    # 2. どこまで逃げるか
    print('**2. 逃げる場合、どこまで逃げるか**（1 段足すごとの延べ）')
    dist = Counter()
    for row, M, ocf, w in res:
        if w is None:
            continue
        for s, d in w:
            if '逃げる' not in s:
                continue
            dist['`A` の中' if d == -1 else '%d 段前' % d] += 1
    tt = sum(dist.values())
    for k, v in sorted(dist.items(), key=lambda t: -t[1]):
        print('   %-14s %6d (%.1f%%)' % (k, v, 100.0 * v / max(1, tt)))
    print()

    # 3. 逃げる最小の行
    print('**3. 逃げる行のうち、順序数がいちばん小さいもの**')
    for row, M, ocf, w in sorted(rows_esc, key=lambda t: t[0])[:5]:
        first = next(i for i, x in enumerate(w) if '逃げる' in x[0])
        print('   行 %-5d %s' % (row, ocf))
        print('      M = %s' % ''.join('(%d,%d,%d)' % q for q in M))
        print('      %d 段目を足したときに %s（%s）'
              % (first + 1, w[first][0],
                 '`A` の中' if w[first][1] == -1 else '%d 段前' % w[first][1]))
    print()

    # 4. 逃げない行の割合（＝易しい版 (TOWER) の値打ち）
    safe = kinds['逃げない（新しい段の中）']
    print('**4. 逃げない行 = %d / %d (%.2f%%)  ＝ 易しい版 (TOWER) の値打ち**'
          % (safe, n, 100.0 * safe / n))
    # H41 の種別と交差
    print('   H41 の種別との交差:')
    cross = Counter()
    for row, M, ocf, w in res:
        kd = h41.classify(M, 6)[0]
        if w is None:
            cross[(kd, '塔でない')] += 1
        elif any('逃げる' in x[0] for x in w):
            cross[(kd, '**逃げる**')] += 1
        elif set(x[0] for x in w) <= {'孤児', '末尾が零列'}:
            cross[(kd, '孤児')] += 1
        else:
            cross[(kd, '逃げない')] += 1
    for k, v in sorted(cross.items()):
        print('      %-24s %5d' % (str(k), v))
    print()

    # 退化検査
    print('**退化検査**（教訓 11/12）')
    pop = [r for r in res if r[3] is not None]
    f = lambda r: any('逃げる' in x[0] for x in r[3])
    for nm, tv in (('「|M| <= 6」', lambda r: len(r[1]) <= 6),
                   ('「行 2 が全部 0」', lambda r: all(q[2] == 0 for q in r[1])),
                   ('「M の末尾が行 2 = 0」', lambda r: r[1][-1][2] == 0),
                   ('「H41 の種別が (b)」',
                    lambda r: h41.classify(r[1], 6)[0] == 'b')):
        wc.audit(pop, f, tv, '「逃げる」判定 vs ' + nm)
