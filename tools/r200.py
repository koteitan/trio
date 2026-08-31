# -*- coding: utf-8 -*-
"""**課題 (z2) —— `cone2` を消費側の `Q` で測る。**

## 前提の逐語（教訓 2）

`Wset.lean:4046`:

```lean
def LiftTowerExp2 : Prop := ∀ (v z a t : ℕ) (R : TrioSeq), argOK R → R ≠ [] → z ≤ 1 →
  2*(v+t)+z ≤ a → (∀ n, 1 ≤ n → R⟦n⟧ ∈ Wstar2) → (∀ k, k < R.length → R.take k ∈ Wstar2) →
  (∃ m, domT R m) → srow R (R.length - 1) = 2 →
  hasParent ((0,v,z) :: R) (srow R (R.length - 1)) R.length → Lift1 ((0,v,z) :: R) t ∈ W a
```

`H12H2.lean:331-335`: 塔の `Q` は **`Lift1 ((0,v,z) :: R.dropLast) t`**。

`cone2`（`L105Cap:11310` の H12 の言葉「行 2 が正の列は全部錐の中」を式にしたもの）:

    `cone2 X ⟺ ∀ j, 0 < entry X 2 j → le1 X 0 j`

## ⚠ 母集団は消費側の**上位集合**（明記。(u2) と同じ）

判定できる前提だけを課す: `argOK R`（行 0 >= 1）、`R ≠ []`、`z <= 1`、
`∃ m, domT R m`、`srow R (|R|-1) = 2`、`hasParent ((0,v,z)::R) 2 |R|`。
**`Wstar2` 所属は判定しない**（教訓: 「`W` 所属の判定はしないこと」）。

## ★ 予想（教訓 45）＋ 見積もり

> **⚠ `hz0(Q)`: `Q[0] = (0, v+t, z)` なので `entry Q 2 0 = z`。**
>   **`L105Cap:3840` `towerExpBigZ_srow2_z_zero` が `z = 0` を強制 ⟹ **100%** と予想。**
> **⚠ `cone2(Q)`: `R.dropLast` の内部の列は錐の外にありうる（§R133 で錐の外は普通に起きる）。**
>   **⟹ **100% にならない**と予想。見積もり **20〜60%**。**
> **⟹ そうなら `cone2` は `h2all` と**同じ場所**（`R.dropLast` の内部）で死ぬ。**
> **⚠ 反例（L3 に有利な形）: 100%。そのとき供給できる。**
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1
from r169 import domT


def cone2(X):
    return all(trio.is_ancestor(X, 1, 0, j) for j in range(len(X)) if X[j][2] > 0)


def bad_cols(X):
    return [j for j in range(len(X)) if X[j][2] > 0 and not trio.is_ancestor(X, 1, 0, j)]


def run(L, R1, VS, ZS, TS):
    COL = [(a, b, c) for a in range(1, 4) for b in range(R1) for c in (0, 1)]
    c = Counter(); ex = []; t0 = time.time()
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt); jR = len(R) - 1
        if srow(R, jR) != 2: continue
        if not any(domT(R, m) for m in range(4)): continue
        for v in VS:
            for z in ZS:
                M = [(0, v, z)] + R
                if trio.parent(M, 2, len(R)) is None: continue
                c['★ 前提を通った (R,v,z)'] += 1
                for t in TS:
                    Q = [tuple(x) for x in Lift1([(0, v, z)] + R[:-1], t)]
                    c['単位 (R,v,z,t)'] += 1
                    h0 = (Q[0][2] == 0)
                    cn = cone2(Q)
                    if h0: c['(z2b) hz0(Q)'] += 1
                    if cn: c['★ (z2a) cone2(Q)'] += 1
                    if h0 and cn: c['★ (z2b) hz0 ∧ cone2'] += 1
                    if not cn:
                        b = bad_cols(Q)
                        c[('(z2c) 破れる列', '根 j=0' if 0 in b else 'R.dropLast の内部')] += 1
                        c[('(z2c) 破れた本数', min(len(b), 4))] += 1
                        if len(ex) < 3: ex.append((R, v, z, t, Q, b))
    u = c['単位 (R,v,z,t)']
    print(f'### |R|={L} 行1<{R1} v∈{tuple(VS)} z∈{tuple(ZS)} t∈{tuple(TS)}  '
          f'前提を通った (R,v,z) {c["★ 前提を通った (R,v,z)"]}  単位 {u}  [{time.time()-t0:.1f}s]')
    if not u: print('  （0 件）\n'); return
    for k in ['(z2b) hz0(Q)', '★ (z2a) cone2(Q)', '★ (z2b) hz0 ∧ cone2']:
        print(f'    {k:26s} {c[k]:9d} / {u} ({100*c[k]/u:7.3f}%)')
    print('    (z2c) 破れる場所: ', dict((k[1], c[k]) for k in c
                                    if isinstance(k, tuple) and k[0] == '(z2c) 破れる列'))
    print('    (z2c) 破れた列の本数: ', dict(sorted((k[1], c[k]) for k in c
                                    if isinstance(k, tuple) and k[0] == '(z2c) 破れた本数')))
    for x in ex: print(f'      ⚠ 破れ例 R={x[0]} v={x[1]} z={x[2]} t={x[3]} Q={x[4]} 破れる列={x[5]}')
    print()


if __name__ == '__main__':
    for L in (2, 3, 4):
        run(L, 3, (0, 1, 2), (0, 1), (0, 1, 2))
    print('#### 教訓 21: 箱を広げる（行 1 の値域を上げる）')
    run(3, 5, (0, 1, 2, 3), (0, 1), (0, 1, 2, 3))
