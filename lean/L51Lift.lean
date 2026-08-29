/-
課題 L51: **`(0,0,0)(1,1,1)(2,1,1) ∈ Wself`**（＝ `ψ(Ω_(ω^2))`）を狙う。

`D_2 = (0,0,0)(1,1,1)(2,2,1)` はフラグメント全体（BM4-Analysis ブックの天井
`ψ(K·ω)` より上）なので、狙うべきは **2 行の極限 `D_1 = (0,0,0)(1,1,1)` の
すぐ上の最小の行列**である。

## 展開の形（`oper` の定義から手で計算。team-lead の Python と一致）

    Mt = (0,0,0)(1,1,1)(2,1,1),   At = (0,0,0)(1,1,1)

    j1 = 2、entry Mt 2 2 = 1 > 0 なので **srow = 2**
    行 2 で親を探すと entry Mt 2 j0 < 1 を満たすのは j0 = 0 だけ ⟹ **parent = 0**
    d0 = entry Mt 0 2 - entry Mt 0 0 = 2,  d1 = entry Mt 1 2 - entry Mt 1 0 = 1
    take 0 = []、コピーは列 0..1（＝ At）で、le0 も le1 も 0 から届く

    ⟹ **Mt⟦n⟧ = (range n).flatMap (fun k => shiftr01 (2*k) k At)**
             = **liftTower At 2 n**

    n=1  (0,0,0)(1,1,1)
    n=2  (0,0,0)(1,1,1)(2,1,0)(3,2,1)
    n=3  (0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(5,3,1)

**`Mt⟦n⟧` は `At` 自身の持ち上げ塔である。** team-lead の
`At ++ (range (n-1)).flatMap (fun k => shiftr01 (2k) k Q)`（`Q = (2,1,0)(3,2,1)`）
と同じもの（`Q = shiftr01 2 1 At`）。

## ⟹ 要る一般命題 (LTOW)

`shTower`（`L47W.lean`）は**行 0 しかずらさない**。ここは**段 k ごとに行 1 も k 上がる**。
-/
import Wtower2

namespace TRIO
namespace L51

open Wset

/-- **持ち上げ塔**: `k` 枚目の写しは行 0 を `e*k`、**行 1 を `k`** ずらす。
`Wset.shTower Q e n`（行 0 だけ）の強化版。 -/
noncomputable def liftTower (Q : TrioSeq) (e n : ℕ) : TrioSeq :=
  (List.range n).flatMap fun k => shiftr01 (e * k) k Q

@[simp] theorem liftTower_zero (Q : TrioSeq) (e : ℕ) : liftTower Q e 0 = [] := rfl

theorem liftTower_succ (Q : TrioSeq) (e n : ℕ) :
    liftTower Q e (n + 1) = liftTower Q e n ++ shiftr01 (e * n) n Q := by
  unfold liftTower
  rw [List.range_succ, List.flatMap_append]
  simp

@[simp] theorem liftTower_one (Q : TrioSeq) (e : ℕ) : liftTower Q e 1 = Q := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, liftTower_succ]
  simp [shiftr01]

/-- **(LTOW)** —— 課題 L51 で切り出したい一般命題。**最小の形はまだ未確定**。
いまは「`Q ∈ W u` と根の条件から持ち上げ塔が `W u` に留まる」と置く。

⚠ `Wset.ShiftTowerClosed`（行 0 だけ）と違い、**行 1 が段ごとに上がる**。
`ulift_mem_W` は行 1 のシフトで段を `+2d` 上げるので、素朴には `W u` に留まらない。
留まりうる理由は `mem_Wself_iff`（根の `lev` しか効かない）だが、
**`+2d` を回避する道具がまだ無い**。 -/
def LiftTowerClosed : Prop :=
  ∀ (u e n : ℕ) (Q : TrioSeq), Q ∈ W u → (∀ p ∈ Q, entry Q 0 0 ≤ p.1) →
    liftTower Q e n ∈ W u

/-! ### 目標の行列 -/

/-- `(0,0,0)(1,1,1)` ＝ 2 行 BMS の極限 `ψ(Ω_ω)`。`snoc_zeroRow2` で `Wself`。 -/
def At : TrioSeq := [(0, 0, 0), (1, 1, 1)]

/-- `(0,0,0)(1,1,1)(2,1,1)` ＝ `ψ(Ω_(ω^2))`。**課題 L51 の標的**。 -/
def Mt : TrioSeq := [(0, 0, 0), (1, 1, 1), (2, 1, 1)]

@[simp] theorem At_length : At.length = 2 := rfl
@[simp] theorem Mt_length : Mt.length = 3 := rfl

/-- `At` は `snoc_zeroRow2` で `Wself`（前置き `[(0,0,0)]` は行 2 ≡ 0）。 -/
theorem At_mem_Wself : At ∈ Wself := by
  have h : At = [((0, 0, 0) : ℕ × ℕ × ℕ)] ++ [((1, 1, 1) : ℕ × ℕ × ℕ)] := rfl
  rw [h]
  refine snoc_zeroRow2 ?_ _
  intro p hp
  simp at hp
  rw [hp]

theorem At_mem_W_zero : At ∈ W 0 := by
  have h := At_mem_Wself
  have hlev : lev At 0 = 0 := by simp [lev, entry, At]
  rw [Wself, Set.mem_setOf_eq, hlev] at h
  exact h

/-- `Mt` の根のレベルは 0。⟹ `Mt ∈ Wself ↔ Mt ∈ W 0`。 -/
theorem lev_Mt_zero : lev Mt 0 = 0 := by simp [lev, entry, Mt]

theorem Mt_mem_Wself_iff : Mt ∈ Wself ↔ Mt ∈ W 0 := by
  rw [Wself, Set.mem_setOf_eq, lev_Mt_zero]

/-! ### `Mt` の展開（課題 L51 (3)）

`Mt⟦n⟧ = liftTower At 2 n` を示したい。`oper` の `if` を全部潰す必要がある:

    srow Mt 2 = 2          entry Mt 2 2 = 1 > 0 から
    hasParent Mt 2 2       j0 = 0 が唯一（entry Mt 2 j0 < 1 は j0 = 0 のみ）
    parent Mt 2 2 = 0      Classical.epsilon ＋ 一意性
    le0 Mt 0 0 / 0 1       nextrel0 の鎖 0 → 1 → 2
    le1 Mt 0 0 / 0 1       nextrel1 の鎖（le0 が要る）
-/

theorem entry_Mt : ∀ j < 3,
    entry Mt 0 j = j ∧ entry Mt 1 j = min j 1 ∧ entry Mt 2 j = min j 1 := by
  intro j hj
  rcases j with _ | _ | _ | j
  · simp [entry, Mt]
  · simp [entry, Mt]
  · simp [entry, Mt]
  · omega

theorem srow_Mt : srow Mt 2 = 2 := by simp [srow, entry, Mt]

end L51
end TRIO
