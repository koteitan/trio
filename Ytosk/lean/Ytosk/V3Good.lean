/-
**3 行: 値の基本の不変条件 Good3 と、枠の分解。**

Good3: o・v は標準形、数える子の値は左から減る（和は連結）。このとき
- o(i) = ψ_{v(i)}(spArg(v(i), 0, 数える子の値の連結))（`o_spArg`）、
- 最後の数える子 c の枠では o(i) = ψ_{v(i)}(spArg(v(i), B, o(c)))（B はそれより前の数える子の状態、`o_frame`）、
- 書き換えない枠では B ++ o(c) は標準形（`app_ot_of_notrig`）。
-/
import Ytosk.V3Mono

namespace Ytosk

open T

/-- The values of the counted children of `i`. -/
noncomputable def cvals (M : Mat) (ρ : Valn) (i : Nat) : List T :=
  nzs ((children M i).map (cnt M ρ i))

/-- **Basic value invariant.** -/
structure Good3 (M : Mat) (ρ : Valn) : Prop where
  ot_o : ∀ i, i < M.length → isOT (ρ.o i) = true
  ot_v : ∀ i, i < M.length → isOT (ρ.v i) = true
  dec : ∀ i, i < M.length → (cvals M ρ i).Pairwise (fun a b => b ≤ a)

/-- The `o` value is a single summand. -/
theorem o_psi_form {M : Mat} {ρ : Valn} (hC : Cons M ρ) {i : Nat} (hi : i < M.length) :
    ∃ s y, ρ.o i = psi s y z := by
  rw [(hC i hi).1]
  unfold oRhs
  show ∃ s y, add (sp (sf (ρ.v i)) z (sf _)) (sf z) = psi s y z
  rw [sp_eq_spArg]; exact ⟨_, _, rfl⟩

theorem single_o {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {i : Nat}
    (hi : i < M.length) : Single (ρ.o i) :=
  ⟨hG.ot_o i hi, o_psi_form hC hi⟩

/-- The contributions are zero or single summands. -/
theorem cnt_single {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) (i : Nat) :
    ∀ t ∈ (children M i).map (cnt M ρ i), t = z ∨ Single t := by
  intro t ht
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
  unfold cnt
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · exact Or.inr (single_o hC hG (mem_children hc).2)

theorem cvals_single {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) (i : Nat) :
    ∀ t ∈ cvals M ρ i, Single t := by
  intro t ht
  unfold cvals nzs at ht
  rw [List.mem_filter] at ht
  rcases cnt_single hC hG i t ht.1 with h | h
  · exact absurd h (by simpa using ht.2)
  · exact h

/-- **`o` as `ψ` of the normalized argument.** -/
theorem o_spArg {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) {i : Nat}
    (hi : i < M.length) :
    ρ.o i = psi (ρ.v i) (spArg (ρ.v i) z (sumN (cvals M ρ i))) z := by
  rw [(hC i hi).1]
  unfold oRhs
  rw [sumN_skip_z (cnt_single hC hG i) (hG.dec i hi)]
  have hS := (sumN_dec _ (cvals_single hC hG i) (hG.dec i hi)).1
  exact sf_psi_spArg (hG.ot_v i hi) hS

end Ytosk
