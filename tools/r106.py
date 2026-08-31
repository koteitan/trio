# -*- coding: utf-8 -*-
"""**課題 R103 —— `TowerExpBigRow2` の追加前提 `(∃ p ∈ R.dropLast, p.2.2 ≠ z)` の 2 択。**

核（`L105Cap.lean:2880`、`towerOK_of_towerExpBigRow2` は緑）:

    ∀ v z m a R, argOK R → 2 <= |R| → z <= 1 → 2v+z <= a → domT R m →
      R.dropLast ∈ Wstar → **(∃ p ∈ R.dropLast, p.2.2 ≠ z)** →
      hasParent ((0,v,z) :: R) (srow R (|R|-1)) |R| → ∀ n>=1, ((0,v,z)::R)⟦n⟧ ∈ W a

  (q1) `z=0`（`R.dropLast` に行 2 = 1 の列）と `z=1`（行 2 = 0 の列）は両方起きるか
  (q2) 比率と最小の実例
  (q3) ★ `z=1` の枝は空虚か。`domT` ⟹ 親は必ず根（`parent_cons_eq_zero`）なので
       `srow=2` なら `nextrel2` が `z=1 < c` を要求 ⟹ **`c >= 2`**。
       ⟹ **断片（行 2 <= 1）に限れば `z=1 ∧ srow=2` は不可能**のはず

⚠ `Wstar_closed`（`Wset.lean:4372`）に `zle1` の仮定は**無い**（自分で読んだ）。
   ⟹ 核は行 2 >= 2 の `R` も引き受ける。**そこで `z=1 ∧ srow=2` は起きる。**
   ただし消費側 `mem_Wstar`（`:4646`）/ `mem_of_Aclosed`（`:4642`）は `zle1 M` を持っている。
   ⟹ **`TowerOK` に `zle1 R` を足せる可能性がある**（Lean 側で要確認。私は主張しない）。
   両方の母集団で測る。

⚠ `R.dropLast ∈ Wstar` は有限では判定できない（R94）。**この前提だけ落として測る**
   （＝ 上位集合。前提が空虚でないことの証明にはならないので、そう明記する。教訓 41）。
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r98 import oper_lean


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def run(DS, BS, CS, VS, ZS, LS, label):
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    n = 0
    r = Counter(); ex = {}
    t0 = time.time()
    for L in LS:
        for Rt in itertools.product(COL, repeat=L):
            R = list(Rt)
            if any(p[0] < 1 for p in R):
                continue                                   # argOK
            j = len(R) - 1
            i1 = srow(R, j)
            if trio.parent(R, i1, j) is not None:
                continue                                   # domT の ¬hasParent
            if lev(R[j]) - 1 < 0:
                continue                                   # domT の lev = m+1
            for v in VS:
                for z in ZS:
                    if trio.parent([(0, v, z)] + R, i1, len(R)) is None:
                        continue                           # hasParent（親は必ず根）
                    if not any(p[2] != z for p in R[:-1]):
                        continue                           # 追加前提
                    n += 1
                    r[f'z={z}'] += 1
                    r[f'z={z} srow={i1}'] += 1
                    r[f'z={z} srow={i1} c={R[j][2]}'] += 1
                    key = f'z={z} srow={i1}'
                    if key not in ex:
                        ex[key] = (R, v, z, R[j][2])
    dt = time.time() - t0
    print(f'### {label}  ({dt:.1f}s)  **前提を全部満たす事例 {n} 件**'
          f'（`R.dropLast ∈ Wstar` は除く）')
    if n == 0:
        print('  ⚠ **0 件 ⟹ この母集団では前提が空虚**')
        return
    for k in sorted(r):
        print(f'  {k:26s} {r[k]:9d}  ({100*r[k]/n:5.2f}%)')
    for k in sorted(ex):
        print(f'  最小の例 {k}: R={ex[k][0]} v={ex[k][1]} z={ex[k][2]} c={ex[k][3]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    LS = tuple(range(2, a.L + 1))                          # 2 <= |R|
    run((1, 2, 3), (0, 1, 2, 3), (0, 1), (0, 1, 2, 3), (0, 1), LS,
        f'R103 (I) **断片（行 2 <= 1）** |R|<={a.L}')
    run((1, 2, 3), (0, 1, 2, 3), (0, 1, 2, 3), (0, 1, 2, 3), (0, 1), LS,
        f'R103 (II) 行 2 <= 3 を許す（核の文どおり） |R|<={a.L}')
