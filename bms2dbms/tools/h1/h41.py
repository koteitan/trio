# -*- coding: utf-8 -*-
"""**課題 H41 —— `M⟦n⟧` は「固定の接頭辞 ++ 持ち上げ塔」か。シート母集団で全数。**

母集団は `psiI.json` の 3 行 z<2 行（**シートの行番号順 ＝ 順序数順**、教訓 11）。

判定は **`trio.expand` の中身を読まずに、展開結果の直接比較**で行う:

    L_n = |M[n]|                              n = 1..N
    (d)  L_n が n に依らない                    ⟹ `dropLast` 型
    そうでなければ L_n = a + n*b（b = L_2 - L_1, a = L_1 - b）と置き
    A     = M[n][:a]                          （全 n で一致するか）
    B_n,k = M[n][a+k*b : a+(k+1)*b]           k = 0..n-1
    (c)  B_n,k が n に依る                      ⟹ 塔ではない
    (b)  B_n,k は k だけの関数だが、持ち上げが列ごとに違う
    (a)  **B_k = B_0 + (e*k, d*k, 0)**（e,d は列に依らない定数）⟹ 持ち上げ塔

使い方: python3 h1/h41.py [N] [行数の上限]
"""
import sys, os, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import r66, trio
from wcert import wcert
import wcert as wc
from collections import Counter

N = int(sys.argv[1]) if len(sys.argv) > 1 else 8
LIM = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9


def classify(M, N=8):
    """(種別, A, Q, e, d) を返す。種別は 'a' / 'b' / 'c' / 'd' / '?'。"""
    M = [tuple(c) for c in M]
    E = {}
    for n in range(1, N + 1):
        E[n] = [tuple(c) for c in trio.expand(list(M), n)]
    L = [len(E[n]) for n in range(1, N + 1)]
    if len(set(L)) == 1:
        return 'd', E[1], None, None, None          # 伸びない
    b = L[1] - L[0]
    a = L[0] - b
    if b <= 0 or a < 0 or any(L[n - 1] != a + n * b for n in range(1, N + 1)):
        return '?', None, None, None, None          # 長さが線形でない
    A = E[1][:a]
    if any(E[n][:a] != A for n in range(1, N + 1)):
        return 'c', None, None, None, None          # 接頭辞が n で動く
    blk = {}
    for n in range(1, N + 1):
        for k in range(n):
            Bk = tuple(E[n][a + k * b: a + (k + 1) * b])
            if k in blk and blk[k] != Bk:
                return 'c', A, None, None, None     # 段の中身が n で動く
            blk[k] = Bk
    Q = blk[0]
    # 持ち上げが列に依らない定数 (e, d) か
    e = d = None
    for k in range(1, len(blk)):
        for q0, qk in zip(Q, blk[k]):
            if qk[2] != q0[2]:
                return 'b', A, Q, None, None        # 行 2 が動く
            ek, dk = qk[0] - q0[0], qk[1] - q0[1]
            if ek % k or dk % k:
                return 'b', A, Q, None, None        # k に線形でない
            ek, dk = ek // k, dk // k
            if e is None:
                e, d = ek, dk
            elif (ek, dk) != (e, d):
                return 'b', A, Q, None, None        # 列ごとに違う
    return 'a', A, Q, (e or 0), (d or 0)


if __name__ == '__main__':
    T = r66.load_ladder()[:LIM]
    print('母集団: `psiI.json` の 3 行 z<2 **%d 行**（シートの行番号順 ＝ 順序数順）'
          % len(T))
    print('   列数 %d..%d   n = 1..%d'
          % (min(len(b) for _, b, _ in T), max(len(b) for _, b, _ in T), N))
    t0 = time.time()
    res = []
    for row, M, ocf in T:
        res.append((row, M, ocf) + classify(M, N))
    print('   (%.0fs)' % (time.time() - t0))
    print()

    # 1. 内訳
    c = Counter(r[3] for r in res)
    NAME = {'a': '(a) **A ++ 持ち上げ塔**（e,d が列に依らない定数）',
            'b': '(b) 段の中身は n に依らないが、持ち上げが一様でない',
            'c': '(c) 段の中身が n で変わる（塔ではない）',
            'd': '(d) n で伸びない（`dropLast` 型）',
            '?': '(?) 長さが n に線形でない'}
    print('**1. 内訳**')
    for k in ('a', 'b', 'c', 'd', '?'):
        if c[k]:
            print('   %-52s %5d (%.2f%%)'
                  % (NAME[k], c[k], 100.0 * c[k] / len(res)))
    print()

    # 2. (a) のときの d の分布
    A_ = [r for r in res if r[3] == 'a']
    print('**2. (a) %d 件での `d`（行 1 の伸び）の分布**' % len(A_))
    cd = Counter(r[7] for r in A_)
    for k, v in sorted(cd.items()):
        tag = ('  ⟸ `ShiftTowerClosed` で足りる' if k == 0
               else '  ⟸ **持ち上げ塔 (LTOW) が要る**')
        print('   d=%-3d %5d (%.2f%%)%s' % (k, v, 100.0 * v / len(A_), tag))
    ce = Counter(r[6] for r in A_)
    print('   `e`（行 0 の伸び）の分布: %s' % dict(sorted(ce.items())))
    print()

    # 3. (a) にならない最小の行
    bad = [r for r in res if r[3] != 'a']
    print('**3. (a) にならない行のうち、順序数がいちばん小さいもの**')
    for r in sorted(bad, key=lambda r: r[0])[:5]:
        print('   行 %-5d %-10s %s' % (r[0], NAME[r[3]][:3], r[2]))
        print('      M = %s' % (''.join('(%d,%d,%d)' % q for q in r[1])))
    print()

    # 4. A 側の証明書
    print('**4. `A` の側が `wcert` で覆えるか**')
    cov = sum(1 for r in A_ if r[4] is not None and wcert(r[4]) is not None)
    both = sum(1 for r in A_ if r[7] >= 1 and r[4] is not None
               and wcert(r[4]) is not None)
    d1 = sum(1 for r in A_ if r[7] >= 1)
    print('   (a) %d 件のうち `wcert(A)` が届く: **%d (%.1f%%)**'
          % (len(A_), cov, 100.0 * cov / max(1, len(A_))))
    print('   そのうち **d >= 1**（(LTOW) が要る）: **%d (%.1f%%)**'
          % (both, 100.0 * both / max(1, len(A_))))
    print('   （d >= 1 は (a) 全体では %d (%.1f%%)）'
          % (d1, 100.0 * d1 / max(1, len(A_))))
    print()

    # 退化検査
    print('**退化検査**（教訓 11/12）')
    pop = res
    f = lambda r: r[3] == 'a'
    for nm, tv in (('「|M| <= 3」', lambda r: len(r[1]) <= 3),
                   ('「|M| <= 8」', lambda r: len(r[1]) <= 8),
                   ('「M の末尾が行 2 = 0」', lambda r: r[1][-1][2] == 0),
                   ('「行 2 が全部 0」', lambda r: all(q[2] == 0 for q in r[1]))):
        wc.audit(pop, f, tv, '(a) 判定 vs ' + nm)
