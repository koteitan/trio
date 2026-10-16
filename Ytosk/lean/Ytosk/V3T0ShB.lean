/-
**t = 0: 書き換えない枠（影）を直接扱う（2026-10-17、t0）。**

D の枠 (i, c) で、M では書き換え N では書き換えない場合（影）は、lo(y) = 0 かつ B = P + κ（κ は y の最後の加数の
G3 の切り口、κ ≥ T′）に限られる（`trig_or_shadow`）。このとき
- RE は保たれる: 親の古い引数は y = P + ψ_a(x)、新しい引数は B + ψ_s(y′) = P + (κ + ψ_s(y′))（`re_shadow`）。
- RelRU の成分の条件（relR_frameU の hSh）は、M の枠の B が閉じている（`Closed (v i) B`）ことと VSmallRP から出る
  （`shadow_hSh`）。y′ の成分は Lhd z (ψ_s y′) (ψ_s y) を c = ψ_s(B + 1) で使って B と s の成分に帰着する。
したがって T0CutResGGC（影が起きないこと）の代わりに、M の書き換える枠の B が閉じていることを仮定すればよい。
-/
import Ytosk.V3T0DepU

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## 順序の補題 -/

/-- `B < y` gives `B + 1 ≤ y`. -/
theorem app_one_le_of_lt : ∀ {B y : T}, B < y → app B one ≤ y
  | z, y, h => by
    simp only [app]
    exact one_le_of_ne_z (fun e => by subst e; exact T.not_lt_z _ h)
  | psi a b c, z, h => absurd h (T.not_lt_z _)
  | psi a b c, psi d e f, h => by
    simp only [app]
    rcases T.psi_lt_psi.mp h with h1 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h3⟩
    · exact le_of_lt (T.psi_lt_psi.mpr (Or.inl h1))
    · exact le_of_lt (T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨rfl, h2⟩)))
    · rcases (le_iff _ _).mp (app_one_le_of_lt h3) with h4 | h4
      · exact le_of_lt (T.psi_lt_psi.mpr (Or.inr (Or.inr ⟨rfl, rfl, h4⟩)))
      · rw [h4]

theorem le_of_summand_first {B q : T} (hB : B ≠ z) (hq : ∀ p ∈ summands B, q ≤ p) : q ≤ B := by
  cases B with
  | z => exact absurd rfl hB
  | psi a b c => exact le_trans (hq (psi a b z) (by simp [summands])) (head_le_self (psi a b c))

/-! ## 影の枠の成分の条件 -/

/-- **The component condition of a shadow frame** (relR_frameU's `hSh`), from `Closed a B` and the
subscript bound (VSmallRP). -/
theorem shadow_hSh {U : T → Prop} {a B s y y' : T}
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hnt : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true))
    (hy'z : y' ≠ z)
    (hl : Lhd z (psi s y' z) (psi s y z))
    (hB : Closed a B)
    (hVR : ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u s,
      g ≤ psi s z z ∨ g ≤ B ∨ ∃ d ∈ comps u a, g ≤ d) :
    ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u (app B (psi s y' z)),
      g < app B (psi s y' z) ∨ ∃ d ∈ comps u a, g ≤ d := by
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
  have hyB : psi s y z ≤ B := le_of_summand_first hBz hBc
  have hsu : ¬ lt s u = true := fun h => hu (lt_of_le_of_lt has h)
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
  have hBc' : ∀ g ∈ comps u B, g < X' := fun g hg => lt_of_le_of_lt (hB u hu g hg) hBX
  rw [hX', comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact Or.inl (hBc' g hg)
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
      · exact Or.inl (lt_of_le_of_lt (le_trans hgd (hB u hu d hd)) hBX)
      · have : d = z := by
          revert hd; simp only [one, comps]
          split_ifs <;> simp
        rw [this] at hgd
        exact Or.inl (lt_of_le_of_lt hgd (lt_of_le_of_lt (z_le B) hBX))
    · rcases hsub d hd with h | h
      · exact Or.inl (lt_of_le_of_lt hgd h)
      · obtain ⟨d', hd', h'⟩ := h; exact Or.inr ⟨d', hd', le_trans hgd h'⟩
    · rw [hd] at hgd; exact Or.inl (lt_of_le_of_lt hgd (lt_of_le_of_lt (z_le B) hBX))
    · simp at hd
  · exact hsub g hg

/-! ## 書き換えの一致か影か -/

/-- **A rewriting frame keeps rewriting, or it is a shadow**: `lo(y) = 0` and `B = P + κ` with `κ` a G3 cut of the
last summand and `κ ≥ T′`. -/
theorem trig_or_shadow {a B s y y' : T} (hRE : REr y y')
    (hK : B ≠ z → PH3cKindG B (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s)
    (htr : lt B y = true ∧ lt (psi a z z) (psi s y z) = true) :
    (lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true) ∨
      ((split y (psi (succ s) z z)).2 = z ∧ ∃ P a' x T', y = app P (psi a' x z) ∧ y' = app P T' ∧
        ∃ κ ∈ cutsNSG s (psi a' x z), B = app P κ ∧ ¬ κ < T') := by
  by_cases hsh : (split y (psi (succ s) z z)).2 = z ∧ ∃ P a' x T', y = app P (psi a' x z) ∧ y' = app P T' ∧
      ∃ κ ∈ cutsNSG s (psi a' x z), B = app P κ ∧ ¬ κ < T'
  · exact Or.inr hsh
  · left
    refine trig_agreeG hRE hK (fun hlo _ P a' x T' e1 e2 κ hκ hBk => ?_) htr
    by_contra hn
    exact hsh ⟨hlo, P, a', x, T', e1, e2, κ, hκ, hBk, hn⟩

/-- **RE through a shadow frame**: the old argument is `y = P + ψ_a(x)`, the new one `B + ψ_s(y′) = P + (κ + ψ_s(y′))`. -/
theorem re_shadow {a B s y y' P a' x κ : T} (hc : isOT (psi s y z) = true)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q) (hyy : y' < y)
    (htr : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hnt : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true))
    (hlo : (split y (psi (succ s) z z)).2 = z) (hy : y = app P (psi a' x z)) (hBk : B = app P κ) :
    REr (step a B s y z) (step a B s y' z) := by
  have hlt : psi s y' z < psi s y z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hyy⟩)
  have hBc' : ∀ q ∈ summands B, psi s y' z ≤ q := fun q hq => le_trans (le_of_lt hlt) (hBc q hq)
  have hst : step a B s y z = y := by unfold step; rw [if_pos htr]; exact H_of_lo_z hc hlo
  have hst' : step a B s y' z = app B (psi s y' z) := by
    unfold step; rw [if_neg hnt]; exact add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc'
  rw [hst, hst']
  refine ⟨P, a', x, app κ (psi s y' z), hy, by rw [hBk, app_assoc], ?_⟩
  intro h; exact absurd (app_eq_z h).2 (by simp)

end Ytosk
