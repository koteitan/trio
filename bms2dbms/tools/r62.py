# -*- coding: utf-8 -*-
"""課題 R41: **(C11) と (C12) —— 節 2 の 1 段で終わる証明書**。

    (C11) **∀ n >= 1, `M⟦n⟧` の行 2 が全部 0**  ⟹  M ∈ Wself
          （節 2 ＋ (C2) `zeroRow2_mem_Wself`。**測度は要らない。1 段で終わる**）
    (C12) **∀ n >= 1, `M⟦n⟧` に証明書 (C1)-(C6') が当たる** ⟹ M ∈ Wself

種は §R34 の例:  M = (0,1,0)(1,4,0)(1,5,1) -> **M⟦2⟧ = (0,1,0)(1,4,0)(1,5,0)(2,8,0)**
行 2 = 1 の列が消えて行 1 が持ち上がる ⟹ **像が行 2 ≡ 0 に落ちる**。
`lean/Pair/Bridge.lean:38` の `emb` により、**行 2 ≡ 0 は 2 行の世界**（証明ずみ）。
⟹ (C11) が効くなら「**1 段で 2 行に落ちる**」という意味になる。

⚠ `∀n` は n = 1..N で切る。**N を振って結果が動かないこと**を必ず確かめる。
"""
import sys, random
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from r60 import why2


def exps(M, N):
    out = []
    for n in range(1, N + 1):
        E = tuple(map(tuple, trio.expand(list(M), n)))
        out.append(E)
    return out


def c11(M, N):
    """すべての展開が行 2 ≡ 0 か。"""
    return all(all(p[2] == 0 for p in E) for E in exps(M, N) if E)


def c12(M, N):
    """すべての展開に証明書が当たるか。"""
    return all(why2(E) is not None for E in exps(M, N) if E)


if __name__ == '__main__':
    CAP = int(sys.argv[1])
    rng = random.Random(20260829)
    COLS = [(a, b, c) for a in range(6) for b in range(6) for c in range(2)]
    P = set()
    while len(P) < CAP:
        M = tuple(rng.choice(COLS) for _ in range(rng.randint(2, 6)))
        if any(p[2] for p in M):
            P.add(M)
    P = list(P)
    NO = [M for M in P if why2(M) is None]
    print('母数: **行 2 に 1 がある**行列 %d 個。うち (C1)-(C6\') で証明書が無い %d 個'
          % (len(P), len(NO)), flush=True)
    for N in (3, 5, 8):
        c = Counter()
        for M in NO:
            a, b = c11(M, N), c12(M, N)
            c['**(C11) すべての展開が行 2 ≡ 0**'] += a
            c['**(C12) すべての展開に証明書**'] += b
            c['(C11) は外れるが (C12) は当たる'] += (b and not a)
        print('   N=%d:  (C11) %d (%.0f%%) / (C12) %d (%.0f%%) / うち C12 だけ %d'
              % (N, c['**(C11) すべての展開が行 2 ≡ 0**'],
                 100 * c['**(C11) すべての展開が行 2 ≡ 0**'] / len(NO),
                 c['**(C12) すべての展開に証明書**'],
                 100 * c['**(C12) すべての展開に証明書**'] / len(NO),
                 c['(C11) は外れるが (C12) は当たる']), flush=True)
    # 外れる M では、行 2 の 1 が残る n はどれか
    d = Counter()
    for M in NO:
        E = exps(M, 8)
        bad = [n + 1 for n, X in enumerate(E) if X and any(p[2] for p in X)]
        if not bad:
            continue
        d['行 2 が残る最小の n = %d' % bad[0]] += 1
        d['**n = 1..8 のすべてで残る**' if len(bad) == len([x for x in E if x]) else
          '一部の n だけ残る'] += 1
    print('== (C11) が外れる M で、行 2 の 1 が残る n')
    for k in sorted(d, key=str):
        print('   %-36s %d' % (k, d[k]))
