/-
**影の枠を、閉じた状態（RwClosed）より弱い RwClosedL で扱う（2026-10-17、lead）。**

RwClosed（書き換える枠で B < hi(y) なら B は閉じている、ClosedA）は標準形の不変条件ではない（ext3s の sv の行列の
M[3]、desc.md）。影の場合に `relR_frameU` が本当に要る結論 RelRU（区間 (b, A] のどの c でも成分が c の成分で
押さえられる）はそこでも真で、強すぎたのは hSh（閉じた状態）の形。

- `ClosedL a B A`: 段 u ≤ a の B の成分 g は、B 以下、a の成分以下、または区間 (B, A] のどの c でも
  z か c の成分以下。ClosedA から出る（`ClosedA.toL`）。
- `RwClosedL`: RwClosed の結論を ClosedL（A = H(a, H(s, y))）に弱めたもの。
- `relR_of_closedLU`: `relR_of_closedU` の ClosedL 版。
- `shadow_hShL`: `shadow_hSh` の ClosedL 版（影の新しい状態 B + ψ_s(y′) の成分の条件）。
- `relR_frameUL`: `relR_frameU` の hSh を ClosedL 版に弱めた形。影の場合は relR_of_closedLU、それ以外は
  relR_frameU（hSh は使われない）。
-/
import Ytosk.V3T0ShB

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **`B` is closed below `a` relative to the interval up to `A`.** -/
def ClosedL (a B A : T) : Prop :=
  ∀ u, ¬ lt a u = true → ∀ g ∈ comps u B, g ≤ B ∨ (∃ d ∈ comps u a, g ≤ d) ∨
    ∀ c, B < c → c ≤ A → ∃ d ∈ Gc u c, g ≤ d

theorem ClosedA.toL {a B A : T} (h : ClosedA a B) : ClosedL a B A :=
  fun u hu g hg => (h u hu g hg).elim Or.inl (fun h' => Or.inr (Or.inl h'))

/-- **The weak form of `RwClosed`**: at a rewriting frame with `B < hi(y)` not a prefix, `B` is closed relative to
the interval up to `H(a, H(s, y))`. -/
def RwClosedL (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → ∀ s y,
    ρ.o c = psi s y z →
    lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true →
    spArg (ρ.v i) z (sumN (Lc.map ρ.o)) < (split y (psi (succ s) z z)).1 →
    (¬ ∃ R', (split y (psi (succ s) z z)).1 = app (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) R') →
    ClosedL (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) (H (ρ.v i) (H s y))

/-- A non-rewriting step appends the child. -/
theorem step_eq_app_of_not {a B s y : T} (hBc : ∀ r ∈ summands B, psi s y z ≤ r)
    (hn : ¬ (lt B y = true ∧ lt (psi a z z) (psi s y z) = true)) : step a B s y z = app B (psi s y z) := by
  unfold step; rw [if_neg hn]; exact add_eq_app_of_ge ⟨s, y, rfl⟩ B hBc

/-- **`relR_of_closedU` with the interval escape.** -/
theorem relR_of_closedLU {U : T → Prop} {q a X A : T} (hX : isOT (psi a X z) = true) (hqa : ¬ lt a q = true)
    (hcl : ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u X, g < X ∨ (∃ d ∈ comps u a, g ≤ d) ∨
      ∀ c, H a X < c → c ≤ A → ∃ d ∈ Gc u c, g ≤ d)
    (hyp : ∀ u, U u → ¬ lt q u = true → ∀ d ∈ comps u a, d < H a X ∨ ∃ d' ∈ comps u q, d ≤ d') :
    RelRU U q (H a X) A := by
  intro u hU hu c hc1 hc2 g hg
  have hau : ¬ lt a u = true := fun h => hu (lt_of_le_of_lt (not_lt.mp hqa) (show a < u from h))
  have hXH : X ≤ H a X := le_H hX
  have hsub : ∀ g ∈ comps u X, g < H a X ∨ ∃ d ∈ Gc u c ++ comps u q, g ≤ d := by
    intro g hg
    rcases hcl u hU hau g hg with h | ⟨d, hd, hgd⟩ | h
    · exact Or.inl (lt_of_lt_of_le h hXH)
    · rcases hyp u hU hu d hd with h | ⟨d', hd', hdd'⟩
      · exact Or.inl (lt_of_le_of_lt hgd h)
      · exact Or.inr ⟨d', List.mem_append_right _ hd', le_trans hgd hdd'⟩
    · obtain ⟨d, hd, hgd⟩ := h c hc1 hc2
      exact Or.inr ⟨d, List.mem_append_left _ hd, hgd⟩
  rw [H_eq hX, comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · apply hsub; rw [← split_app (psi (succ a) z z) X, comps_app]; exact List.mem_append_left _ hg
  · split at hg
    · simp [comps] at hg
    · rename_i hlo
      have hXlt : X < H a X := y_lt_H hX hlo
      rw [comps_psi_z_of_ge hau] at hg
      simp only [List.mem_cons, List.mem_append] at hg
      rcases hg with rfl | hg | hg
      · exact Or.inl hXlt
      · exact hsub g hg
      · rcases hyp u hU hu g hg with h | ⟨d', hd', hdd'⟩
        · exact Or.inl h
        · exact Or.inr ⟨d', List.mem_append_right _ hd', hdd'⟩

/-- **`shadow_hSh` with `ClosedL`**: the components of the shadow state `B + ψ_s(y′)` are below it, below a
component of `a`, or below a component of every term of the interval `(H(a, B + ψ_s(y′)), A]`. -/
theorem shadow_hShL {U : T → Prop} {a B s y y' A : T}
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hnt : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true))
    (hy'z : y' ≠ z)
    (hl : Lhd z (psi s y' z) (psi s y z))
    (hX'ot : isOT (psi a (app B (psi s y' z)) z) = true)
    (hB : ClosedL a B A)
    (hVR : ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u s,
      g ≤ psi s z z ∨ g ≤ B ∨ ∃ d ∈ comps u a, g ≤ d) :
    ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u (app B (psi s y' z)),
      g < app B (psi s y' z) ∨ (∃ d ∈ comps u a, g ≤ d) ∨
        ∀ c, H a (app B (psi s y' z)) < c → c ≤ A → ∃ d ∈ Gc u c, g ≤ d := by
  intro u hU hu g hg
  have has : a ≤ s := by
    rcases psi_lt_psi_z_iff.mp (show psi a z z < psi s y z from ht.2) with h | ⟨h, _⟩
    · exact le_of_lt h
    · rw [h]
  have hy'pos : z < y' := lt_of_le_of_ne (z_le y') (Ne.symm hy'z)
  have h2' : psi a z z < psi s y' z := by
    rcases (le_iff _ _).mp has with h | h
    · exact psi_lt_psi_z_iff.mpr (Or.inl h)
    · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨h, hy'pos⟩)
  have hy'B : y' ≤ B := by
    by_contra hn
    exact hnt ⟨lt_of_not_ge hn, h2'⟩
  have hBz : B ≠ z := fun e => by rw [e] at hy'B; exact hy'z (le_antisymm hy'B (z_le _))
  set X' := app B (psi s y' z) with hX'
  have hBX : B < X' := lt_app_ne (by simp)
  have hXH : X' ≤ H a X' := le_H hX'ot
  have hyB : psi s y z ≤ B := le_of_summand_first hBz hBc
  have hsu : ¬ lt s u = true := fun h => hu (lt_of_le_of_lt has h)
  -- the interval escape of `B` moves to the interval above `H a X′`
  have hlift : ∀ g, (∀ c, B < c → c ≤ A → ∃ d ∈ Gc u c, g ≤ d) →
      ∀ c, H a X' < c → c ≤ A → ∃ d ∈ Gc u c, g ≤ d :=
    fun g h c hc1 hc2 => h c (lt_of_lt_of_le hBX (le_trans hXH (le_of_lt hc1))) hc2
  -- the subscript components
  have hsub : ∀ g ∈ comps u s, g < X' ∨ ∃ d ∈ comps u a, g ≤ d := by
    intro g hg
    rcases hVR u hU hu g hg with h | h | h
    · left
      refine lt_of_le_of_lt h (lt_of_le_of_lt ?_ (lt_of_le_of_lt hyB hBX))
      rcases (le_iff _ _).mp (z_le y) with h' | h'
      · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, h'⟩))
      · rw [← h']
    · exact Or.inl (lt_of_le_of_lt h hBX)
    · exact Or.inr h
  -- the components of `B`
  rw [hX', comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases hB u hu g hg with h | h | h
    · exact Or.inl (lt_of_le_of_lt h hBX)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (hlift g h))
  -- the components of `ψ_s(y′)`
  simp only [comps, if_neg hsu, List.append_nil, List.mem_cons, List.mem_append] at hg
  rcases hg with rfl | hg | hg
  · exact Or.inl (lt_of_le_of_lt hy'B hBX)
  · -- through `◁` at `c = ψ_s(B + 1)`
    have hc1 : psi s y' z < psi s (app B one) z :=
      psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_lt hy'B (lt_app_ne (by simp [one]))⟩)
    have hc2 : psi s (app B one) z ≤ psi s y z := by
      rcases (le_iff _ _).mp (app_one_le_of_lt ht.1) with h | h
      · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, h⟩))
      · rw [h]
    have hgm : g ∈ comps u (psi s y' z) := by
      simp only [comps, if_neg hsu, List.append_nil, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl hg)
    obtain ⟨d, hd, hgd⟩ := hl.2 u _ hc1 hc2 g hgm
    simp only [comps, if_neg hsu, List.append_nil, Gc, List.mem_append, List.mem_cons] at hd
    have hB1 : app B one < X' := by
      have h1 : psi z z z < psi s y' z := by
        rcases (le_iff _ _).mp (z_le s) with h | h
        · exact psi_lt_psi_z_iff.mpr (Or.inl h)
        · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨h, hy'pos⟩)
      exact app_lt_app_left B h1
    rcases hd with (rfl | hd | hd) | hd | hd
    · exact Or.inl (lt_of_le_of_lt hgd hB1)
    · -- `d` is a component of `B + 1`
      rw [comps_app] at hd
      rcases List.mem_append.mp hd with hd | hd
      · rcases hB u hu d hd with h | ⟨d', hd', h⟩ | h
        · exact Or.inl (lt_of_le_of_lt (le_trans hgd h) hBX)
        · exact Or.inr (Or.inl ⟨d', hd', le_trans hgd h⟩)
        · refine Or.inr (Or.inr (hlift g (fun c hc1 hc2 => ?_)))
          obtain ⟨d', hd', h'⟩ := h c hc1 hc2
          exact ⟨d', hd', le_trans hgd h'⟩
      · have : d = z := by
          revert hd; simp only [one, comps]
          split_ifs <;> simp
        rw [this] at hgd
        exact Or.inl (lt_of_le_of_lt hgd (lt_of_le_of_lt (z_le B) hBX))
    · rcases hsub d hd with h | h
      · exact Or.inl (lt_of_le_of_lt hgd h)
      · obtain ⟨d', hd', h'⟩ := h; exact Or.inr (Or.inl ⟨d', hd', le_trans hgd h'⟩)
    · rw [hd] at hgd; exact Or.inl (lt_of_le_of_lt hgd (lt_of_le_of_lt (z_le B) hBX))
    · simp at hd
  · exact (hsub g hg).elim Or.inl (fun h => Or.inr (Or.inl h))

/-- **`relR_frameU` with the weak shadow condition** (`hShL` in place of the closed state `hSh`). In the shadow case
(the old child rewrites, the new one does not, and `hi(y)` does not extend `B`) the relation comes from
`relR_of_closedLU`; otherwise `relR_frameU` does not use its `hSh`. -/
theorem relR_frameUL {U : T → Prop} {q a B s y s' y' : T}
    (hc : isOT (psi s y z) = true) (hc' : isOT (psi s' y' z) = true)
    (hBc : ∀ r ∈ summands B, psi s y z ≤ r)
    (hrel : (LhdE (psi s' y' z) (psi s y z) ∧ (y' ≠ z → s' = s)) ∨ (y' = z ∧ y = z ∧ WkVA s' s ∧ WCS a s'))
    (hX' : isOT (psi a (step a B s' y' z) z) = true) (hY0 : isOT (psi a (step a B s y z) z) = true)
    (hN : LhdE (psi a (step a B s' y' z) z) (psi a (step a B s y z) z))
    (hRC : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → s' = s → ∀ q', ¬ lt s q' = true →
      (∀ u, U u → ¬ lt q' u = true → ∀ g ∈ comps u s, g ≤ psi s z z ∨ g < H s y' ∨ ∃ d ∈ comps u q', g ≤ d) →
      RelRU U q' (H s y') (H s y))
    (hVR : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → (split y (psi (succ s) z z)).1 ≠ z →
      ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u s, g ≤ psi s z z ∨ g ≤ B ∨ ∃ d ∈ comps u a, g ≤ d)
    (hVNR : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → s' ≠ s →
      ¬ ((split y (psi (succ s) z z)).1 = B ∧ a < s') → ∀ u, U u → ¬ lt a u = true →
      ∀ g ∈ comps u s', g ≤ psi s' z z ∨ g ≤ B ∨ ∃ d ∈ comps u a, g ≤ d)
    (hShL : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) →
      ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) →
      (¬ ∃ R, (split y (psi (succ s) z z)).1 = app B R) →
      ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u (app B (psi s' y' z)),
        g < app B (psi s' y' z) ∨ (∃ d ∈ comps u a, g ≤ d) ∨
          ∀ c, H a (app B (psi s' y' z)) < c → c ≤ H a (H s y) → ∃ d ∈ Gc u c, g ≤ d)
    (hqa : ¬ lt a q = true)
    (hyp : ∀ u, U u → ¬ lt q u = true → ∀ g ∈ comps u a,
      g ≤ psi a z z ∨ g < H a (step a B s' y' z) ∨ ∃ d ∈ comps u q, g ≤ d) :
    RelRU U q (H a (step a B s' y' z)) (H a (step a B s y z)) := by
  by_cases hsh : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) ∧
      ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) ∧
      (¬ ∃ R, (split y (psi (succ s) z z)).1 = app B R)
  · obtain ⟨ht, ht', hpre⟩ := hsh
    have hc'c : psi s' y' z ≤ psi s y z := by
      rcases hrel with ⟨h, _⟩ | ⟨rfl, rfl, _⟩
      · exact h.le
      · exact absurd ht.1 (T.not_lt_z _)
    have hBc' : ∀ r ∈ summands B, psi s' y' z ≤ r := fun r hr => le_trans hc'c (hBc r hr)
    have e' : step a B s' y' z = app B (psi s' y' z) := by
      unfold step; rw [if_neg ht']; exact add_eq_app_of_ge ⟨s', y', rfl⟩ B hBc'
    have e : step a B s y z = H s y := by unfold step; rw [if_pos ht]
    have hXz : step a B s' y' z ≠ z := step_ne_z hc'
    have hyp' : ∀ u, U u → ¬ lt q u = true → ∀ d ∈ comps u a,
        d < H a (step a B s' y' z) ∨ ∃ d' ∈ comps u q, d ≤ d' := by
      intro u hU hu d hd
      rcases hyp u hU hu d hd with h | h | h
      · exact Or.inl (lt_of_le_of_lt h (om_lt_H hX' hXz))
      · exact Or.inl h
      · exact Or.inr h
    rw [e'] at hX' hyp' ⊢
    rw [e]
    exact relR_of_closedLU hX' hqa (hShL ht ht' hpre) hyp'
  · exact relR_frameU hc hc' hBc hrel hX' hY0 hN hRC hVR hVNR
      (fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hsh) hqa hyp

end Ytosk
