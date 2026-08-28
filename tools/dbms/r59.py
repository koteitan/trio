# -*- coding: utf-8 -*-
"""課題 R35 —— **`WCat` を直に測る**（`lean/Wtower2.lean:1974`）。

    WCat : ∀ u A B, A ∈ W u → B ∈ W u → **A ++ B ∈ W u**
    `shiftTowerClosed_of_cat`（:1982）: **WCat ⟹ ShiftTowerClosed、しかも
    「根が最浅」の側条件が落ちる。**

`(TOW)` の `e = 0` は `shTower Q 0 n = Q ++ … ++ Q` なので `WCat` の `A = B` の場合。
`e >= 1`（沈める）の話が消えるぶん問いが素直で、側条件が無いぶん母数も広い。

`Wself` の形で測る（§R33-1 の還元より `u` は要らない）:

    **A ∈ Wself ∧ B ∈ Wself ⟹ A ++ B ∈ Wself ?**

⚠ `lev (A ++ B) 0 = lev A 0` なので段は A 側に揃う。`B ∈ W (lev A 0)` は
`B ∈ Wself ∧ lev B 0 <= lev A 0` と同値（`mem_Wself_iff`）。**そこも数える。**

証明書は §R33-1b の 4 本 (C1)-(C4)（`r57.why_self`）。
"""
import sys, random
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from r57 import why_self
from r49 import has_parent


def lev0(M):
    return 2 * M[0][1] + M[0][2] if M else 0


def peel_stop(M):
    """(C4) の剥がしが止まる位置（残った長さ）。剥がしきれたら 0。"""
    M = tuple(map(tuple, M))
    while len(M) >= 2:
        j = len(M) - 1
        if M[j] != (0, 0, 0) and has_parent(M, j):
            return len(M)
        M = M[:-1]
    return 0


if __name__ == '__main__':
    CAP = int(sys.argv[1]); PAIRS = int(sys.argv[2])
    rng = random.Random(20260829)
    COLS = [(a, b, c) for a in range(6) for b in range(6) for c in range(2)]
    P = set()
    while len(P) < CAP:
        P.add(tuple(rng.choice(COLS) for _ in range(rng.randint(1, 5))))
    P = list(P)
    OK = [M for M in P if why_self(M) is not None]
    print('母数 %d 個 -> **証明書つき %d 個 (%.0f%%)**' % (len(P), len(OK), 100 * len(OK) / len(P)))

    pairs = [(rng.choice(OK), rng.choice(OK)) for _ in range(PAIRS)]
    pairs += [(A, A) for A in rng.sample(OK, min(PAIRS // 4, len(OK)))]   # A = B（= e=0 の塔）
    c = Counter(); f = Counter(); ex = []
    for A, B in pairs:
        T = A + B
        if lev0(B) > lev0(A):
            c['`B ∈ W (lev A 0)` が成り立たない（前提外）'] += 1
            continue
        c['前提を満たす (A,B)'] += 1
        w = why_self(T)
        tag = 'A=B' if A == B else 'A≠B'
        if w is not None:
            c['**A ++ B にも証明書が届く（%s）**' % w.split()[0]] += 1
            c['  届いた（%s）' % tag] += 1
        else:
            c['届かない'] += 1
            c['  届かない（%s）' % tag] += 1
            z2A = any(p[2] for p in A); z2B = any(p[2] for p in B)
            f['行 2 の 1 が %s' % ('A と B の両方' if z2A and z2B else
                                  ('A だけ' if z2A else ('B だけ' if z2B else '**どちらにも無い**')))] += 1
            st = peel_stop(T)
            f['剥がしが止まる位置: %s' % ('B の中（|A| より後ろ）' if st > len(A) else
                                         ('ちょうど境界 |A|' if st == len(A) else 'A の中'))] += 1
            if len(ex) < 5:
                ex.append((A, B, st))
    print('== `WCat` の地図')
    for k in sorted(c, key=str):
        print('   %-46s %d' % (k, c[k]))
    print('== 届かない形の分類')
    for k in sorted(f, key=str):
        print('   %-46s %d' % (k, f[k]))
    print('== 退化検査: 「届いた」は自明な族に潰れていないか')
    d = Counter()
    for A, B in pairs:
        T = A + B
        if lev0(B) > lev0(A) or why_self(T) is None:
            continue
        triv = (len(T) <= 1) or all(p[2] == 0 for p in T) or all(p[0] == 0 for p in T)
        d['自明（|T|<=1 / 行 2 ≡ 0 / 行 0 ≡ 0）' if triv else '**自明でない（C4 が効いた）**'] += 1
    for k in sorted(d, key=str):
        print('   %-46s %d' % (k, d[k]))
    for A, B, st in ex:
        print('   届かない例  A=%s  B=%s  (|A|=%d, 剥がしは %d で止まる)'
              % (''.join(map(str, A)), ''.join(map(str, B)), len(A), st))
