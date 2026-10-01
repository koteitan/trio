/-
**順位があれば評価の割り当ては存在する。**

`Val` は割り当て ρ（`Cons`）と順位（`Rk`）の両方を要求する。順位があれば、ρ は右辺の写像 F の反復で作れる:
ρ_0 = 0、ρ_{k+1} = F(ρ_k)。順位 < k の呼び出しの値は k 回目以降変わらない（`iter_stable`）ので、
十分大きな K で ρ_K は等式をすべて満たす（`cons_of_rk`）。
3 行の展開 M[n] の値は、順位を作ってからこの定理で割り当てを得て、一意性で式を確かめる。
-/
import Ytosk.Val

namespace Ytosk

open T

/-- One application of the right sides. -/
def rhsF (M : Mat) (ρ : Valn) : Valn := ⟨fun i => oRhs M ρ i, fun i => vRhs M ρ i⟩

/-- The `k`-th iterate from `0`. -/
def rhsIt (M : Mat) : Nat → Valn
  | 0 => ⟨fun _ => z, fun _ => z⟩
  | k + 1 => rhsF M (rhsIt M k)

/-- `vRhs` only reads the dependencies listed in `Rk`. -/
theorem vRhs_congr {M : Mat} {ρ₁ ρ₂ : Valn} {i : Nat}
    (hp : ∀ m, entry M 1 i ≠ 0 → par M 1 i = some m → ρ₁.v m = ρ₂.v m)
    (hu : ∀ k, entry M 1 i ≠ 0 → entry M 2 i = 0 → upg M i = some k → ρ₁.v k = ρ₂.v k)
    (hb : ∀ j ∈ children M i, entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → col M j = bump M i →
      ∀ k ∈ children M j, ρ₁.o k = ρ₂.o k) :
    vRhs M ρ₁ i = vRhs M ρ₂ i := by
  unfold vRhs
  by_cases h1 : entry M 1 i = 0
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    have hpar : vOpt ρ₁ (par M 1 i) = vOpt ρ₂ (par M 1 i) := by
      cases hm : par M 1 i with
      | none => rfl
      | some m => exact hp m h1 hm
    rw [hpar]
    by_cases h2 : entry M 2 i = 0
    · rw [if_pos h2, if_pos h2]
      cases hk : upg M i with
      | none => rfl
      | some k => simp only; rw [hu k h1 h2 hk]
    · rw [if_neg h2, if_neg h2]
      congr 4
      congr 1
      apply List.map_congr_left
      intro j hj
      unfold bumpTerm
      split
      · rename_i hbj
        congr 2
        apply List.map_congr_left
        intro k hk
        exact hb j hj h1 h2 hbj k hk
      · rfl

/-- `oRhs` only reads `v(i)` and the counted children. -/
theorem oRhs_congr {M : Mat} {ρ₁ ρ₂ : Valn} {i : Nat} (hv : ρ₁.v i = ρ₂.v i)
    (hc : ∀ c ∈ children M i, col M c ≠ bump M i → ¬ (isUpg M c = true ∧ topped M c = true) →
      ρ₁.o c = ρ₂.o c) :
    oRhs M ρ₁ i = oRhs M ρ₂ i := by
  unfold oRhs
  rw [hv]
  congr 3
  apply List.map_congr_left
  intro c hcm
  unfold cnt
  split
  · rfl
  · rename_i hbc
    split
    · rfl
    · rename_i huc
      exact hc c hcm hbc huc

/-- **Stability of the iteration.** A call of rank `< k` keeps its value from step `k` on. -/
theorem iter_stable {M : Mat} {rk : Bool → Nat → Nat} (hr : Rk M rk) :
    ∀ k, ∀ i, i < M.length → ∀ m,
      (rk true i < k → (rhsIt M (k + m)).o i = (rhsIt M k).o i) ∧
      (rk false i < k → (rhsIt M (k + m)).v i = (rhsIt M k).v i) := by
  intro k
  induction k with
  | zero => intro i _ m; exact ⟨fun h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro i hi m
    obtain ⟨hvo, hc, hR⟩ := hr i hi
    -- `v` first
    have hv : rk false i < k + 1 → (rhsIt M (k + 1 + m)).v i = (rhsIt M (k + 1)).v i := by
      intro hlt
      rw [show k + 1 + m = (k + m) + 1 by omega]
      show vRhs M (rhsIt M (k + m)) i = vRhs M (rhsIt M k) i
      apply vRhs_congr
      · intro m' h1 hm
        have hlt' := (hR h1).1 m' hm
        exact (ih m' (by have := par_lt M 1 i m' hm; omega) m).2 (by omega)
      · intro k' h1 h2 hk
        have hlt' := (hR h1).2.1 h2 k' hk
        exact (ih k' (upg_lt hi hk) m).2 (by omega)
      · intro j hj h1 h2 hbj k' hk'
        have hlt' := (hR h1).2.2 h2 j hj hbj k' hk'
        exact (ih k' (mem_children hk').2 m).1 (by omega)
    refine ⟨fun hlt => ?_, hv⟩
    rw [show k + 1 + m = (k + m) + 1 by omega]
    show oRhs M (rhsIt M (k + m)) i = oRhs M (rhsIt M k) i
    apply oRhs_congr
    · exact (ih i hi m).2 (by omega)
    · intro c hcm hbc huc
      have hlt' := hc c hcm hbc huc
      exact (ih c (mem_children hcm).2 m).1 (by omega)

theorem nat_le_sum_of_mem : ∀ {l : List Nat} {a : Nat}, a ∈ l → a ≤ l.sum
  | [], _, h => absurd h (List.not_mem_nil)
  | b :: l, a, h => by
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := nat_le_sum_of_mem h; omega

/-- A bound for all ranks. -/
def rkBound (M : Mat) (rk : Bool → Nat → Nat) : Nat :=
  ((List.range M.length).map (fun i => rk true i + rk false i)).sum + 1

theorem rk_lt_bound (M : Mat) (rk : Bool → Nat → Nat) {i : Nat} (hi : i < M.length) (b : Bool) :
    rk b i < rkBound M rk := by
  unfold rkBound
  have hmem : rk true i + rk false i ∈ (List.range M.length).map (fun i => rk true i + rk false i) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have := nat_le_sum_of_mem hmem
  cases b <;> omega

/-- **Existence.** A ranking gives a valuation satisfying the equations. -/
theorem cons_of_rk {M : Mat} {rk : Bool → Nat → Nat} (hr : Rk M rk) :
    Cons M (rhsIt M (rkBound M rk)) := by
  intro i hi
  have hs := iter_stable hr (rkBound M rk) i hi 1
  refine ⟨?_, ?_⟩
  · rw [← hs.1 (rk_lt_bound M rk hi true)]; rfl
  · rw [← hs.2 (rk_lt_bound M rk hi false)]; rfl

/-- A ranking gives a value. -/
theorem val_of_rk {M : Mat} {rk : Bool → Nat → Nat} (hr : Rk M rk) :
    Val M (root M (rhsIt M (rkBound M rk))) :=
  ⟨_, rk, cons_of_rk hr, hr, rfl⟩

end Ytosk
