# -*- coding: utf-8 -*-
"""課題 R33-1c: **行 2 に 1 がある行列の `Wself` の証明書**を探す。

§R33-1b で `(TOW)` の残り 21% は 100% が「行 2 に 1 がある Q」だと分かった。
既存の証明書 (C1)-(C4) は、最後の列が孤児でないと動けない:

    節 2 が n に依らないのは `oper M n = Pred M` のとき ＝ 最後の列が零か孤児
    節 3 も `domT M m` が「最後の列が孤児」を要求する

⟹ **最後の列が親を持つ M** を確定する道は「節 2 を本当に全部の n で見る」しかない。

## 候補の規則 (C5) —— **塔の 1 段を剥がす**

    M[n] = M.take j0 ++ (ブロックの n 個の写し、k 番目は k*d0, k*d1 だけ持ち上げ)
    ⟹ **M[n+1] は M[n] にもう 1 枚ブロックを足したもの**

もし **n 枚目のブロックの列が `M[n+1]` の中で全部孤児**なら、(C4) の剥がしで
`M[n+1]` は `M[n]` まで落ちる。それが**すべての n** で成り立てば、

    M[1] ∈ Wself  ⟹  ∀n, M[n] ∈ Wself  ⟹  **M ∈ Wself**（節 2）

`∀n` は n = 1..N で確かめるしかない（**そこは切り詰め**）。ただし持ち上げは
k について単調なので、孤児かどうかは k が大きいところで安定するはず ——
**安定するか**も測る（n を増やして判定が変わらないこと）。
"""
import sys, time, random
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from r57 import why_self, shTower
from r49 import has_parent


def peel(M):
    """(C4) の剥がし: 最後の列が零か孤児である限り落とす。"""
    M = tuple(map(tuple, M))
    while len(M) >= 2:
        j = len(M) - 1
        if M[j] != (0, 0, 0) and has_parent(M, j):
            break
        M = M[:-1]
    return M


def c5(M, N):
    """(C5): `M[n+1]` が (C4) の剥がしで `M[n]` まで落ちるか（n = 1..N）。
    落ちるなら `M[1] ∈ Wself` から `M ∈ Wself` が出る（∀n は N で切っている）。"""
    M = tuple(map(tuple, M))
    if len(M) < 2:
        return None
    E = [tuple(map(tuple, trio.expand(list(M), n))) for n in range(1, N + 2)]
    for n in range(1, N + 1):
        if peel(E[n]) != E[n - 1]:          # E[n] = M[n+1], E[n-1] = M[n]
            return False
    return why_self(E[0]) is not None       # M[1] に証明書があるか


if __name__ == '__main__':
    CAP = int(sys.argv[1]); N = int(sys.argv[2])
    rng = random.Random(20260829)
    COLS = [(a, b, c) for a in range(6) for b in range(6) for c in range(2)]
    P = set()
    while len(P) < CAP:
        P.add(tuple(rng.choice(COLS) for _ in range(rng.randint(2, 6))))
    P = list(P)
    NO = [M for M in P if why_self(M) is None]
    print('母数 %d 個のうち **(C1)-(C4) で証明書が無い** %d 個に (C5) を当てる（n=1..%d）'
          % (len(P), len(NO), N), flush=True)
    c = Counter(); ex = []
    for M in NO:
        r = c5(M, N)
        if r is True:
            c['**(C5) で確定**'] += 1
            if len(ex) < 5: ex.append(M)
        elif r is False:
            c['剥がしが 1 段で止まる'] += 1
        else:
            c['|M| < 2'] += 1
    for k in sorted(c, key=str):
        print('   %-30s %d' % (k, c[k]))
    # 安定性: N を変えて判定が動くか
    print('== (C5) の判定は N で動くか（切り詰めの向きの検査）', flush=True)
    base = {M: c5(M, 3) for M in NO[:1500]}
    for NN in (4, 6, 8):
        d = Counter()
        for M in NO[:1500]:
            d['同じ' if c5(M, NN) == base[M] else '**変わった**'] += 1
        print('   N=3 -> N=%d  %s' % (NN, dict(d)), flush=True)
    for M in ex:
        print('   (C5) で確定した例  %s' % ''.join(map(str, M)))
