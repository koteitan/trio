# -*- coding: utf-8 -*-
"""課題 R33-1b: **`Wself` の証明書を集めて `(TOW)` の地図を作り直す。**

§R33-1 で `(TOW)` は **u の要らない `Wself` の文**に還元できた:

    (TOW) ⟺ ∀ Q e n, Q ∈ Wself → (根が最浅) → **shTower Q e n ∈ Wself**

そこで `Wself` に入ることを**構成的に確定**できる族を全部集める。

## 証明書（すべて Lean で証明ずみ、または既存補題から 1 行）

    (C1) **|M| <= 1**            `singleton_mem_W`（`Wchar.lean:99`）
         `[(d,v,z)] ∈ W a ⟺ 2v+z <= a`。a = lev M 0 で成立。`[] ∈ W u` は `W_nil`。
    (C2) **行 2 ≡ 0**            `zeroRow2_mem_Wself`（`Wtower2.lean:2985`）
    (C3) **行 0 ≡ 0**            `flat_mem_W`（`Wtower2.lean:257`）
         `(∀j, entry M 0 j = 0) → lev M 0 <= a → M ∈ W a`
    (C4) **孤児の塔**（段なし版）  `oper M n = Pred M`（n に依らない）＋ 節 2
         最後の列が零または親無し ⟹ `Pred M ∈ Wself` から `M ∈ Wself`
         **第 0 列が不変**なので `lev (Pred M) 0 = lev M 0` ⟹ 段が揃う（§R33-0）

    ⚠ (C4) は私の `Wlo` より**強い**。`Wlo` は底に `lev M 0 = 0` を要求していたが、
    `Wself` では (C1) が任意の 1 列を許すのでその制限が要らない。
"""
import sys, time, random
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from r49 import Wlo, has_parent


def lev0(Q):
    return 2 * Q[0][1] + Q[0][2] if Q else 0


def shTower(Q, e, n):
    return tuple((p[0] + k * e, p[1], p[2]) for k in range(n) for p in Q)


def why_self(M):
    """`M ∈ Wself` を確定できる証明書の名前（できなければ None）。"""
    M = tuple(map(tuple, M))
    if len(M) <= 1:
        return 'C1 |M|<=1'
    if all(p[2] == 0 for p in M):
        return 'C2 行 2 ≡ 0'
    if all(p[0] == 0 for p in M):
        return 'C3 行 0 ≡ 0'
    # C4: 孤児の塔（底は任意の 1 列でよい）
    X = M; k = 0
    while len(X) >= 2:
        j = len(X) - 1
        if X[j] != (0, 0, 0) and has_parent(X, j):
            break
        X = X[:-1]; k += 1
    if len(X) <= 1:
        return 'C4 孤児の塔'
    if all(p[2] == 0 for p in X):
        return 'C4+C2 孤児を剥がすと行 2 ≡ 0'
    if all(p[0] == 0 for p in X):
        return 'C4+C3 孤児を剥がすと行 0 ≡ 0'
    return None


if __name__ == '__main__':
    CAP = int(sys.argv[1]); EMAX = int(sys.argv[2]); NMAX = int(sys.argv[3])
    rng = random.Random(20260829)
    COLS = [(a, b, c) for a in range(6) for b in range(6) for c in range(2)]
    P = set()
    while len(P) < CAP:
        P.add(tuple(rng.choice(COLS) for _ in range(rng.randint(1, 6))))
    P = list(P)

    print('== 証明書ごとの `Wself` の覆い（乱択 %d 個、長さ 1..6、行 2 は 0..1）' % len(P))
    c = Counter()
    for M in P:
        c[why_self(M) or '**証明書が無い**'] += 1
    for k in sorted(c, key=str):
        print('   %-34s %d' % (k, c[k]))
    print('   （旧 `Wlo` だけだと %d 個）' % sum(1 for M in P if Wlo(M)))

    # --- (TOW) の地図
    QQ = [Q for Q in P if all(Q[0][0] <= p[0] for p in Q)]
    print('== `(TOW)` の地図（側条件「根が最浅」を満たす Q %d 個 × e=0..%d × n=2..%d）'
          % (len(QQ), EMAX, NMAX))
    d = Counter(); ex = []
    for Q in QQ:
        wq = why_self(Q)
        if wq is None:
            d['Q 自体に証明書が無い（前提が確認できない）'] += 1
            continue
        for e in range(EMAX + 1):
            for n in range(2, NMAX + 1):
                T = shTower(Q, e, n)
                wt = why_self(T)
                if wt is not None:
                    d['**結論も確定（%s）**' % wt.split()[0]] += 1
                else:
                    d['結論の証明書が届かない'] += 1
                    if len(ex) < 6:
                        ex.append((Q, wq, e, n, T))
    for k in sorted(d, key=str):
        print('   %-40s %d' % (k, d[k]))
    print('== 届かない例（`Q` には証明書があるのに `shTower` には無い）')
    for Q, wq, e, n, T in ex:
        print('   Q=%-26s [%s]  e=%d n=%d' % (''.join(map(str, Q)), wq, e, n))
        print('     -> %s' % ''.join(map(str, T)))
