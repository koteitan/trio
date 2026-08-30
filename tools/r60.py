# -*- coding: utf-8 -*-
"""課題 R36 / R37 / R38 —— **証明書を 7 本に増やして `WCat`（A ≠ B）の覆いを測る。**

team-lead が Lean を洗って見つけた見落とし（どれも証明ずみ）:

    (C5') `snoc_zeroRow2`（`Wtower2.lean:3127`）  M' ++ [t]、M' は行 2 ≡ 0、**t は任意**
    (C6') `snoc_orphan`（`:3053`）                **任意の `Wself` の元** ++ [孤児]。**繰り返せる**
    (C11) `W_add`（`Wset.lean:1682`）             A ++ B、側条件 `rsum A B`
          `rsum A B : ∀ p ∈ A ++ B, entry B 0 0 <= p.1`（**B の根が全体で最浅**）
    (C10) `W_flatMap_copies`（`:2552`）           同じ Q を n 個 ⟹ **A = B は無料**
    (C8)  `W_shift`（`:1320`）                    行 0 のシフトは段を上げない

⚠ 私の旧 (C4) は「**底が 1 列**の孤児の塔」だった。(C6') は**底が任意の証明書**なので
真に強い。しかも旧 `why_self` は「孤児を全部剥がしてから」基礎を見ていたが、
**(C5') は接頭辞で閉じていない**ので **1 段ごとに全部の基礎を見る**必要がある。
"""
import sys, random
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
from r49 import has_parent


def lev0(M):
    return 2 * M[0][1] + M[0][2] if M else 0


def base_cert(M):
    """剥がしを使わない基礎の証明書。"""
    if len(M) <= 1:
        return 'C1'
    if all(p[2] == 0 for p in M):
        return 'C2'
    if all(p[0] == 0 for p in M):
        return 'C3'
    if all(p[2] == 0 for p in M[:-1]):
        return "C5' snoc_zeroRow2"
    return None


def why2(M):
    """(C1)(C2)(C3)(C5') を基礎に、(C6') `snoc_orphan` を末尾から**1 段ずつ**当てる。"""
    M = tuple(map(tuple, M))
    b = base_cert(M)
    if b:
        return b
    X = M; k = 0
    while len(X) >= 2:
        j = len(X) - 1
        if X[j] != (0, 0, 0) and has_parent(X, j):
            return None                      # 孤児でないので剥がせない
        X = X[:-1]; k += 1
        b = base_cert(X)
        if b:
            return "C6'(%d 段)+%s" % (k, b.split()[0])
    return None


def wadd_ok(A, B):
    """`rsum A B`: B の根の行 0 が `A ++ B` の全列以下。"""
    r = B[0][0]
    return all(r <= p[0] for p in A) and all(r <= p[0] for p in B)


def cat_cert(A, B):
    """`A ++ B` の証明書（(C10) と (C11) も含む）。"""
    if A == B:
        return 'C10 (A=B は無料)'
    if lev0(B) <= lev0(A) and wadd_ok(A, B):
        return 'C11 W_add'
    return why2(A + B)


if __name__ == '__main__':
    CAP = int(sys.argv[1]); PAIRS = int(sys.argv[2])
    rng = random.Random(20260829)
    COLS = [(a, b, c) for a in range(6) for b in range(6) for c in range(2)]
    P = set()
    while len(P) < CAP:
        P.add(tuple(rng.choice(COLS) for _ in range(rng.randint(1, 5))))
    P = list(P)
    from r57 import why_self as why_old
    old = [M for M in P if why_old(M) is not None]
    new = [M for M in P if why2(M) is not None]
    print('== R36: 証明書の覆い（母数 %d）' % len(P))
    print('   旧 4 本 (C1)-(C4)      %d (%.0f%%)' % (len(old), 100 * len(old) / len(P)))
    print('   **新 7 本（C5\' C6\' 込み） %d (%.0f%%)**'
          % (len(new), 100 * len(new) / len(P)))
    so, sn = set(old), set(new)
    print('   ⚠ 退化検査: 新 ⊋ 旧 か -> 新だけ %d 個 / 旧だけ %d 個'
          % (len(sn - so), len(so - sn)))
    c = Counter()
    for M in new:
        c[why2(M).split('+')[0].split()[0]] += 1
    print('   内訳 %s' % dict(c))

    print('== R37: `WCat`（**A ≠ B** に絞る。A = B は `W_flatMap_copies` で無料）')
    OK = new
    pairs = []
    while len(pairs) < PAIRS:
        A = rng.choice(OK); B = rng.choice(OK)
        if A != B:
            pairs.append((A, B))
    d = Counter(); f = Counter(); ex = []
    for A, B in pairs:
        if lev0(B) > lev0(A):
            d['`lev B 0 <= lev A 0` が成り立たない（前提外）'] += 1
            continue
        d['前提を満たす (A,B)'] += 1
        w = cat_cert(A, B)
        if w:
            d['**A ++ B に証明書が届く**'] += 1
            d['  ' + w.split('+')[0].split()[0]] += 1
        else:
            d['届かない'] += 1
            # R38: `W_add` との差 —— B の根の位置
            mn = min(p[0] for p in A)
            g = B[0][0] - mn
            f['B の根 <= A の最浅（W_add が使えるはず）' if g <= 0
              else 'B の根が A の最浅より %s' % ('1 深い' if g == 1 else
                                                 ('2 深い' if g == 2 else '3 以上深い'))] += 1
            f['A の末尾と B の先頭の行 0 の差 %s'
              % ('B が浅い' if B[0][0] < A[-1][0] else
                 ('同じ' if B[0][0] == A[-1][0] else 'B が深い'))] += 1
            # 行 2 = 1 の列は孤児か、親を持つか
            T = A + B
            for j, p in enumerate(T):
                if p[2] == 1:
                    f['行 2 = 1 の列: **親を持つ**' if has_parent(T, j)
                      else '行 2 = 1 の列: 孤児'] += 1
            f['A 単体 %s' % why2(A).split('+')[0].split()[0]] += 1
            f['B 単体 %s' % why2(B).split('+')[0].split()[0]] += 1
            if len(ex) < 4:
                ex.append((A, B))
    for k in sorted(d, key=str):
        print('   %-46s %d' % (k, d[k]))
    print('== R38: 届かない形の分類')
    for k in sorted(f, key=str):
        print('   %-46s %d' % (k, f[k]))
    for A, B in ex:
        print('   届かない例 A=%s  B=%s' % (''.join(map(str, A)), ''.join(map(str, B))))
