# -*- coding: utf-8 -*-
"""**課題 (b1) —— `TowerP V d0 d1` の 6 つの連言のうち、どれが `V` で自動か。**

## 前提の逐語（`L106.lean` §206。team-lead の散文ではなくファイルから）

```lean
def TowerP (Q : TrioSeq) (d e : ℕ) : Prop :=
  ∃ M : TrioSeq, M.dropLast = Q ∧ 2 ≤ M.length ∧ 0 < e ∧
    entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d ∧
    (∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l) ∧
    le1 M 0 (0 + M.dropLast.length) ∧
    entry M.dropLast 0 0 = 0 ∧ entry M.dropLast 2 0 = 0
```

`M` は**存在量化**、`M.dropLast = Q` ⟹ **`M = Q ++ [c]`**。展開すると（`|M| = |Q|+1`）:

    **(1) `2 <= |M|`**       ⟺ `1 <= |Q|`
    **(2) `0 < e`**          ← ⚠ team-lead の 4 つに入っていない
    **(3) `hd0e`**  `entry M 0 |Q| = entry M 0 0 + d` ⟺ **`c.0 = Q[0].0 + d`**
    **(4) `hr0M`**  `∀ 0<l<|Q|+1, Q[0].0 < M[l].0` ⟺ **`hr0(Q)` ∧ `Q[0].0 < c.0`**（⟺ `0 < d`）
    **(5) `hlp`**   **`le1 (Q ++ [c]) 0 |Q|`**
    **(6) `hbase`** **`entry Q 0 0 = 0`** ← ⚠ team-lead の 4 つに入っていない。**強い**
    **(7) `hz0`**   `entry Q 2 0 = 0`

⟹ **`c` は `c.0` が決まり、`c.1`・`c.2` だけ自由 ⟹ 判定できる。**

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ (2) `0 < d1`（新しい `e`）: §R176 で「`srow <= 1` ⟹ `e' = 0`」を出している。
>   非減少でない段でも `srow <= 1` は多い ⟹ **成立 5〜30%** と予想。**
> **⚠ (6) `hbase(V)`（`V[0].0 = 0`）: 窓の根は塔の中の列なので行 0 は普通 > 0
>   ⟹ **成立 0〜5%** と予想。⚠ ただし `W_shift`（`Wset:1320`）で正規化できるかもしれない。**
> **⚠ (7) `hz0(V)` … 85〜90%（(w4) の既知）。(4) `hr0(V)` … 未測定。**
> **⟹ ★ `TowerP V d0 d1` 全体は **数 % 以下**と予想。そこが穴。**
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

CBOUND = 40


def hr0(Q):   return all(Q[0][0] < Q[l][0] for l in range(1, len(Q)))
def hbase(Q): return Q[0][0] == 0
def hz0(Q):   return Q[0][2] == 0


def hd0e_hlp(Q, d):
    """(3)(4)(5): `c.0 = Q[0].0 + d`、`Q[0].0 < c.0`、`le1 (Q++[c]) 0 |Q|` を満たす
    `c` が在るか。`c.1` は 0..CBOUND、`c.2` は 0/1 を走査。"""
    if d == 0: return False, False          # (4) が破れる
    c0 = Q[0][0] + d
    lo = max(p[1] for p in Q) + CBOUND
    for c1 in range(0, lo + 1):
        for c2 in (0, 1):
            M = list(Q) + [(c0, c1, c2)]
            if trio.is_ancestor(M, 1, 0, len(Q)):
                return True, True
    return True, False                       # (3)(4) は satisfiable、(5) が破れる


def check(Q, d, e, c):
    """`TowerP Q d e` の各連言を数える。"""
    c['単位'] += 1
    ok = True
    if len(Q) >= 1: c['(1) 2<=|M|'] += 1
    else: ok = False
    if e > 0: c['(2) 0 < e'] += 1
    else: ok = False
    if hr0(Q): c['(4a) hr0(Q)'] += 1
    else: ok = False
    a, b = hd0e_hlp(Q, d)
    if a: c['(3)(4b) hd0e ∧ 0<d'] += 1
    else: ok = False
    if b: c['(5) hlp'] += 1
    else: ok = False
    if hbase(Q): c['(6) hbase (行0の根=0)'] += 1
    else: ok = False
    if hz0(Q): c['(7) hz0'] += 1
    else: ok = False
    if ok: c['★★ TowerP 全体'] += 1


def run_consumer(L, R1, VS, ZS, TS, NS, depth, beam, seed):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    cQ = Counter(); cV = {k: Counter() for k in range(1, depth + 1)}
    rnd = random.Random(seed); t0 = time.time()
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
                    d, e = dOf(M), eOf(M)
                    check(Q, d, e, cQ)
                    front = [(tuple(Q), d, e)]
                    for dep in range(1, depth + 1):
                        nxt = set()
                        for (X, dd, ee) in front:
                            for n in NS:
                                for j in range(len(X)):
                                    r = step_det(list(X), dd, ee, n, j)
                                    if r is None or len(r[0]) < 2: continue
                                    check([tuple(x) for x in r[0]], r[1], r[2], cV[dep])
                                    nxt.add((tuple(r[0]), r[1], r[2]))
                        if not nxt: break
                        front = list(nxt)
                        if len(front) > beam:
                            rnd.shuffle(front); front = front[:beam]
    print(f'### 消費側 |R|={L} 行1<{R1}  [{time.time()-t0:.1f}s]')
    KEYS = ['(1) 2<=|M|', '(2) 0 < e', '(3)(4b) hd0e ∧ 0<d', '(4a) hr0(Q)',
            '(5) hlp', '(6) hbase (行0の根=0)', '(7) hz0', '★★ TowerP 全体']
    for tag, c in [('消費側の Q', cQ)] + [(f'降りた V 深さ{k}', cV[k]) for k in cV]:
        t = c['単位']
        if not t: continue
        print(f'  {tag}（単位 {t}）')
        for k in KEYS:
            print(f'      {k:24s} {c[k]:9d} ({100*c[k]/t:8.4f}%)')
    print()


if __name__ == '__main__':
    run_consumer(2, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 2, 150, 381)
    run_consumer(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 2, 100, 383)
