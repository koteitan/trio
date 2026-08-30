# -*- coding: utf-8 -*-
"""**課題 (u2)（L3 / H12 の依頼）—— 消費側で `zle1 R` が何 %。**

## 逐語で写した（`file:line`）

    `Wset.lean:2470` **`def zle1 (M : TrioSeq) : Prop := ∀ p ∈ M, p.2.2 ≤ 1`**
      ⟹ **`R` の全列の行 2 が 1 以下**
    `Wset.lean:4046` **`LiftTowerExp2`** の前提:
      `argOK R` ／ `R ≠ []` ／ **`z ≤ 1`** ／ `2*(v+t)+z ≤ a` ／ `∀ n≥1, R⟦n⟧ ∈ Wstar2` ／
      `∀ k<|R|, R.take k ∈ Wstar2` ／ **`∃ m, domT R m`** ／ **`srow R (|R|-1) = 2`** ／
      **`hasParent ((0,v,z) :: R) (srow R (|R|-1)) |R|`**
      ⚠ **`zle1 R` は前提に入っていない。**
    `L105Cap:3840` **`towerExpBigZ_srow2_z_zero`**:
      `R ≠ []` ∧ **`z ≤ 1`** ∧ **`zle1 R`** ∧ `domT R m` ∧ `srow R (|R|-1) = 2` ∧
      `hasParent ((0,v,z) :: R) 2 |R|` **⟹ `z = 0`**

## ★ 導出（測るまでもない部分）

> **断片（行 2 ∈ {0,1}）では `zle1 R` は**自動**（全列の行 2 が 1 以下）。**
> **⟹ 上の定理の対偶より、断片の中では
> **`z = 1` ∧ `srow = 2` ∧ `domT` ∧ `hasParent` は起こりえない**（＝ 空虚）。**
> **⟹ (u2b) の答えは「`z = 1` では `zle1 R` が破れる」ではなく
> 「断片では `z = 1` の `srow = 2` の枝そのものが空虚」。**

## ★ 予想と見積もり（教訓 45）

    **(u2a)** 断片の箱では `zle1 R` は **100%**（定義から自明）。行 2 <= 2 の箱では下がる
    **(u2b)** 断片の箱で **`z=1` ∧ `srow=2` ∧ `domT` ∧ `hasParent` は 0 件**（定理の対偶）
              ⚠ **見積もり 0 件。1 件でも出れば定理か私の写しが誤り**
    **(u2c)** 行 2 <= 2 の箱では 0 件でなくなるはず（陽性対照）

**箱と単位**: 単位 `(R, v, z)`。箱 = `R` の列は 行0 ∈ 1..3（`argOK`）、行1<3、**行2 <= cm（1 と 2）**、
`|R| = 2..4`、`v ∈ 0..2`、`z ∈ {0,1}`。**`W` 所属（`Wstar2`）は判定しない（明記・除外）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow


def zle1(R):
    return all(p[2] <= 1 for p in R)


def domT(R, m):
    """`domT R m`: 末尾列に親が無く `lev >= 1`（§R125 の実装に合わせる）。"""
    j = len(R) - 1
    return trio.parent(R, srow(R, j), j) is None and (2 * R[j][1] + R[j][2]) >= 1


def run(cm, L, VS, ZS, R1):
    COL = [(a, b, c) for a in range(1, 4) for b in range(R1) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt)
        jR = len(R) - 1
        if srow(R, jR) != 2:
            continue                                   # 消費側の前提
        if not any(domT(R, m) for m in range(4)):
            continue                                   # `∃ m, domT R m`
        z1 = zle1(R)
        for v in VS:
            for z in ZS:
                M = [(0, v, z)] + R
                if trio.parent(M, srow(R, jR), len(R)) is None:
                    continue                           # `hasParent ((0,v,z)::R) 2 |R|`
                c['★ 消費側の（判定できる）前提を通った'] += 1
                c[('zle1 R', z1)] += 1
                c[('z 別', z)] += 1
                c[('★ z ∧ zle1', z, z1)] += 1
                if z == 1 and z1:
                    c['⛔⛔ z=1 ∧ zle1（定理に反する）'] += 1
                    ex.setdefault('⛔ 定理に反する', (R, v, z))
                if z == 1:
                    ex.setdefault('z=1 の例', (R, v, z, z1))
    tot = c['★ 消費側の（判定できる）前提を通った']
    print(f'### 行2<={cm} |R|={L} 行1<{R1}  前提を通った `(R,v,z)` {tot:9d}  [{time.time()-t0:.1f}s]')
    if not tot:
        print('  （0 件）\n'); return
    print(f'  **(u2a) `zle1 R` … {c[("zle1 R", True)]:9d} / {tot} '
          f'({100*c[("zle1 R", True)]/tot:6.2f}%)**')
    for z in ZS:
        n_ = c[('z 別', z)]
        if n_:
            print(f'      z={z}: 分母 {n_:9d}  `zle1 R` {c[("★ z ∧ zle1", z, True)]:9d} '
                  f'({100*c[("★ z ∧ zle1", z, True)]/n_:6.2f}%)')
    print(f'  **⛔⛔ `z=1` ∧ `zle1 R`（定理に反する）… {c["⛔⛔ z=1 ∧ zle1（定理に反する）"]}**')
    for k in sorted(ex):
        print(f'      {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=4)
    a = ap.parse_args()
    for cm in (1, 2):
        for L in range(2, a.L + 1):
            run(cm, L, (0, 1, 2), (0, 1), 3)
