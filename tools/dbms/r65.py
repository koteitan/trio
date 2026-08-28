# -*- coding: utf-8 -*-
"""課題 R44: **`WCat` ⟺ 証明ずみ ∧ `WCatCore`** を検算する。

    def WCatCore : Prop :=
      ∀ (u : ℕ) (A B : TrioSeq), A ∈ W u → B ∈ W u → A ≠ [] → B ≠ [] →
        (∀ p ∈ B, entry B 0 0 ≤ p.1) →        -- **B の根は B の中で最浅**
        A ++ B ∈ W u

（`rsum` は `A ++ B` **全体**を見るが、`WCatCore` の側条件は **`B` だけ**。そこが違い。）

## 還元の筋（帰納法は `|B|` について）

    s := B の最初の最小の位置
    s = 0 なら **B の根は B の最浅** ⟹ `WCatCore` が直に効く（底）
    s >= 1 なら B = B1 ++ B2（B1 = B.take s, B2 = B.drop s）
      **B2 の根は B2 の中で最浅**（構成から。s は最初の最小なので B2[0] = min B）
      `A ++ B = (A ++ B1) ++ B2`
      `A ++ B1 ∈ W u`  … |B1| < |B| で帰納法
      `B2 ∈ W u`       … `W_drop` は `B.drop s ∈ W (lev B s)` なので
                         **`lev B s <= u` が要る**  <- **ここが落とし穴。測る**
      ⟹ `WCatCore (A ++ B1) B2` で `A ++ B ∈ W u`

## 検算すること

    (1) 底で「B の根 = B の最浅」が **100%** か（7436 件全部で）
    (2) 各段で **B2 の根 = B2 の最浅** が 100% か
    (3) 各段で **`lev B s <= u`**（`B2 ∈ W u` が出るか）—— **ここが割れるかもしれない**
    (4) `WCatCore` を神託として仮定したとき、**7436 件が全部片づくか**
"""
import sys, random
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from r60 import why2, lev0, wadd_ok
from r61 import cat_direct


def lv(p):
    return 2 * p[1] + p[2]


def argmin0(B):
    mn = min(p[0] for p in B)
    return next(j for j, p in enumerate(B) if p[0] == mn)


def core_applies(B):
    """`WCatCore` の側条件: B の根が B の中で最浅。"""
    return all(B[0][0] <= p[0] for p in B)


def reduce(A, B, u, c, depth=0):
    """`WCatCore` を神託として `A ++ B ∈ W u` を出せるか。"""
    if depth > 40:
        c['**40 段で打ち切り**'] += 1
        return False
    if cat_direct(A, B):
        c['証明ずみで片づく'] += 1
        return True
    if core_applies(B):
        c['**WCatCore が直に効く（底）**'] += 1
        return True
    s = argmin0(B)                      # s >= 1
    B1, B2 = B[:s], B[s:]
    c['B2 の根 = B2 の最浅' if core_applies(B2) else '**B2 の根が B2 の最浅でない**'] += 1
    # `B2 ∈ W u` は `W_drop` で `W (lev B s)` まで。u 以下か
    if lv(B[s]) <= u:
        c['`lev B s <= u`（B2 ∈ W u が出る）'] += 1
    else:
        c['**`lev B s > u` ⟹ B2 ∈ W u が出ない**'] += 1
        return False
    if not reduce(A, B1, u, c, depth + 1):
        return False
    c['**WCatCore で継げた**'] += 1
    return True


if __name__ == '__main__':
    CAP = int(sys.argv[1]); PAIRS = int(sys.argv[2])
    rng = random.Random(20260829)
    COLS = [(a, b, c) for a in range(6) for b in range(6) for c in range(2)]
    P = set()
    while len(P) < CAP:
        P.add(tuple(rng.choice(COLS) for _ in range(rng.randint(1, 6))))
    OK = [M for M in P if why2(M) is not None]
    c = Counter(); res = Counter(); n = 0; nf = 0
    while n < PAIRS:
        A = rng.choice(OK); B = rng.choice(OK)
        if A == B or lev0(B) > lev0(A):
            continue
        n += 1
        if cat_direct(A, B):
            continue
        nf += 1
        res['**片づいた**' if reduce(A, B, lev0(A), c) else '**片づかない**'] += 1
    print('== R44: `WCatCore` を神託にすると `WCat` が出るか')
    print('   母数: A != B かつ `lev B 0 <= lev A 0` の %d 組のうち、'
          '証明ずみでは届かない **%d 件**' % (PAIRS, nf))
    for k in sorted(res, key=str):
        print('   %-44s %d' % (k, res[k]))
    print('== 各段の検算')
    for k in sorted(c, key=str):
        print('   %-44s %d' % (k, c[k]))
