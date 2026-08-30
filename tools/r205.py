# -*- coding: utf-8 -*-
"""**課題 (a1) —— 「根の行 2 = 1 ∧ 行 2 が定数でない」`Q` は実在するか。**

## ⛔ まず制約の確認（team-lead の立てた規則）

> **「`W` 所属の判定はしないこと」（決定率 0%）**

⟹ **`Q ∈ W u` は判定しない。** 代わりに**判定できる代理**を 3 つ測る:

    **(A) 標準形 `ST_TS`**（`Trio.lean:127`。`diagSeqT 0 v` から `oper` で到達）
    **(B) 標準形の**窓**（`S[a:b]`）** … `W` の議論が実際に触る形
    **(C) 消費側から `oper` で降りた `V`**（(z3) の機構）
    **(D) 一様な箱** … 陽性対照

## 的（`L105Cap.lean:5794` の逐語から）

```lean
def MTowerClosedRow2 : Prop :=
  ∀ (u d e n : ℕ) (Q : TrioSeq), Q ∈ W u →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    (∃ p ∈ Q, 0 < p.2.2) → mTower Q d e n ∈ W u
```

**穴の形** = `entry Q 2 0 > 0` ∧ 行 2 が定数でない ∧ `hr0` ∧ `∃ p ∈ Q, 0 < p.2.2`。

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ (A) 標準形の根は**常に `(0,0,0)`** と予想。理由: `oper M n = M.take j0 ++ …` で
>   `j0 = 0` のときも第 0 コピー（`k=0`）の先頭は `M[j0] = M[0]` ⟹ **第 0 列は不変**。
>   ⟹ **0 件、しかも証明できる**。**
> **⚠ (B) 窓では起きる。見積もり 5〜30%。**
> **⚠ (C) 消費側から降りた `V` でも起きる。見積もり 5〜25%。**
> **⟹ ★ したがって「穴は空虚」ではないと予想する。**
> **⚠ 反例（L3 に有利な形）: (B)(C) が 0 件。**
"""
import sys, itertools, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1
from r169 import domT
from r171 import step_det
from r201 import dOf, eOf


def hr0(Q):  return all(Q[0][0] < Q[j][0] for j in range(1, len(Q)))
def hole(Q):
    """穴の形: 根の行 2 が正 ∧ 行 2 が定数でない ∧ hr0 ∧ どれかの行 2 が正。"""
    if len(Q) < 2: return False
    z = [p[2] for p in Q]
    return z[0] > 0 and len(set(z)) > 1 and hr0(Q) and any(x > 0 for x in z)


def diag(v):
    return [(j, j, min(j, 1)) for j in range(v + 1)]


# ---------- (A) 標準形 ----------
def standard(vmax, depth, NS):
    c = Counter(); seen = set()
    front = [tuple(diag(v)) for v in range(1, vmax + 1)]
    for x in front: seen.add(x)
    for _ in range(depth):
        nxt = set()
        for S in front:
            for n in NS:
                T = tuple(tuple(x) for x in trio.expand([list(y) for y in S], n))
                if len(T) >= 1 and T not in seen:
                    seen.add(T); nxt.add(T)
        if not nxt: break
        front = list(nxt)
        if len(front) > 4000: front = front[:4000]
    for S in seen:
        c['標準形'] += 1
        if S and S[0][2] > 0: c['⚠ 根の行 2 が正'] += 1
        if hole(list(S)):     c['⚠★ 穴の形'] += 1
    print(f'### (A) 標準形（`diagSeqT 0 v`, v<={vmax} から {depth} 段展開、n∈{tuple(NS)}）')
    print(f'    標準形 {c["標準形"]}   ⚠ 根の行 2 が正 {c["⚠ 根の行 2 が正"]}   '
          f'**⚠★ 穴の形 {c["⚠★ 穴の形"]}**')
    return seen


# ---------- (B) 標準形の窓 ----------
def windows(seen):
    c = Counter()
    for S in seen:
        L = len(S)
        for a in range(L):
            for b in range(a + 2, L + 1):
                V = list(S[a:b])
                c['窓'] += 1
                if V[0][2] > 0: c['根の行 2 が正'] += 1
                if hole(V):
                    c['⚠★ 穴の形'] += 1
    print(f'### (B) 標準形の窓 `S[a:b]`   窓 {c["窓"]}   根の行 2 が正 {c["根の行 2 が正"]} '
          f'({100*c["根の行 2 が正"]/max(c["窓"],1):6.2f}%)   '
          f'**⚠★ 穴の形 {c["⚠★ 穴の形"]} ({100*c["⚠★ 穴の形"]/max(c["窓"],1):6.3f}%)**')


# ---------- (C) 消費側から降りた V ----------
def consumer(L, R1, VS, ZS, TS, NS, depth, beam, seed):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    c = Counter(); rnd = random.Random(seed)
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt)
        if srow(R, len(R) - 1) != 2: continue
        if not any(domT(R, m) for m in range(4)): continue
        for v in VS:
            for z in ZS:
                if trio.parent([(0, v, z)] + R, 2, len(R)) is None: continue
                for t in TS:
                    M = [tuple(x) for x in Lift1([(0, v, z)] + R, t)]
                    Q = M[:-1]
                    if len(Q) < 2: continue
                    if hole(Q): c['⚠★ 消費側の Q が穴の形'] += 1
                    c['消費側の Q'] += 1
                    front = [(tuple(Q), dOf(M), eOf(M))]
                    for dep in range(1, depth + 1):
                        nxt = set()
                        for (X, dd, ee) in front:
                            for n in NS:
                                for j in range(len(X)):
                                    r = step_det(list(X), dd, ee, n, j)
                                    if r is None or len(r[0]) < 2: continue
                                    c[('深さ', dep, 'V')] += 1
                                    if hole(list(r[0])): c[('深さ', dep, '⚠★ 穴の形')] += 1
                                    nxt.add((tuple(r[0]), r[1], r[2]))
                        if not nxt: break
                        front = list(nxt)
                        if len(front) > beam:
                            rnd.shuffle(front); front = front[:beam]
    print(f'### (C) 消費側 |R|={L} 行1<{R1}   消費側の `Q` {c["消費側の Q"]}   '
          f'**⚠★ `Q` が穴の形 {c["⚠★ 消費側の Q が穴の形"]}**')
    for dep in range(1, depth + 1):
        s = c[('深さ', dep, 'V')]
        if not s: continue
        print(f'    深さ {dep}: `V` {s:9d}  **⚠★ 穴の形 {c[("深さ",dep,"⚠★ 穴の形")]:8d} '
              f'({100*c[("深さ",dep,"⚠★ 穴の形")]/s:7.4f}%)**')


# ---------- (D) 陽性対照 ----------
def control(E, LS, nsamp, seed):
    rnd = random.Random(seed); c = Counter()
    for _ in range(nsamp):
        L = rnd.choice(LS)
        Q = [(rnd.randrange(E), rnd.randrange(E), rnd.randrange(2)) for _ in range(L)]
        c['一様'] += 1
        if hole(Q): c['⚠★ 穴の形'] += 1
    print(f'### (D) 陽性対照（一様な箱 値域<{E}）  {c["一様"]}   '
          f'**⚠★ 穴の形 {c["⚠★ 穴の形"]} ({100*c["⚠★ 穴の形"]/max(c["一様"],1):6.2f}%)** ← 鳴るべき')


if __name__ == '__main__':
    t0 = time.time()
    seen = standard(6, 4, (1, 2, 3))
    windows(seen)
    consumer(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 3, 200, 361)
    consumer(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2,3), 2, 150, 363)
    control(4, (3,4,5,6), 40000, 365)
    print(f'[{time.time()-t0:.1f}s]')
