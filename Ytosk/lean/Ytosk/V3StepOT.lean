/-
**枠 1 段で親が標準形のままであること。**

標準形の親 ψ_a(B) に、B の加数以下の標準形の 1 加数 c = ψ_s(y) を正規化 step で足しても、
ψ_a(step a B s y) は標準形（`step_ot_of_le`）。仮定は
- `SubSmall a s`（添字の成分は Ω_s 以下）と、
- s ≥ a のとき、y の段 a の成分が step の結果以下であること。
2 つ目は外せない（`step_ot_needs_arg`: a = 0, c = ψ_1(ψ_0(Ω_2)) では、成分 Ω_2 が親の引数を超える。
書き換える枠 B = 0 でも書き換えない枠 B = ψ_1(Ω_1) でも偽）。
自然な十分条件: y の段 a の成分がどれも y 以下か B + c 以下（`step_ot`）。y が段 a で閉じていれば足りる
（`step_ot_of_closed`）。
-/
import Ytosk.V3NodeLhd

namespace Ytosk

open T

/-- Without rewriting, the step is the plain sum. -/
theorem step_add {B s y : T} (hBc : ∀ q ∈ summands B, psi s y z ≤ q) :
    add B (psi s y z) = app B (psi s y z) := by
  have := add_app_drop (lo := z) (B := B) (s := s) (y := y)
    (fun q hq hlt => lt_irrefl' _ (lt_of_lt_of_le hlt (hBc q hq))) (Or.inl rfl)
  rwa [app_z_right] at this

/-- **`y ≤ step a B s y`** when `a ≤ s`. -/
theorem y_le_step {a B s y : T} (hc : isOT (psi s y z) = true)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q) (hsa : ¬ lt s a = true) :
    y ≤ step a B s y z := by
  unfold step
  split_ifs with ht
  · rw [H_eq hc]
    have e := split_app (psi (succ s) z z) y
    by_cases hlo : (split y (psi (succ s) z z)).2 = z
    · rw [if_pos hlo]
      rw [hlo] at e
      rw [e]
    · rw [if_neg hlo]
      calc y = app (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 := e.symm
        _ ≤ _ := le_of_lt (app_lt_app_left _ (split_lo_lt hc hlo))
  · rw [step_add hBc]
    by_cases hyz : y = z
    · rw [hyz]; exact z_le _
    · have has : a ≤ s := not_lt.mp hsa
      have htr : lt (psi a z z) (psi s y z) = true := by
        show psi a z z < psi s y z
        rcases (le_iff _ _).mp has with h | rfl
        · exact psi_lt_psi_z_iff.mpr (Or.inl h)
        · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hyz)⟩)
      have hyB : y ≤ B := not_lt.mp (fun h => ht ⟨h, htr⟩)
      exact le_trans hyB (le_app_self _ _)

/-- **`Ω_s ≤ step a B s y`.** -/
theorem om_le_step {a B s y : T} (hc : isOT (psi s y z) = true)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q) :
    psi s z z ≤ step a B s y z := by
  unfold step
  split_ifs with ht
  · exact om_le_H hc (ne_z_of_lt ht.1)
  · rw [step_add hBc]
    exact le_trans (psi_le_psi_arg (z_le y)) (le_app_psi hBc)

/-- **`B + c ≤ step a B s y`**: rewriting never goes below the plain sum. -/
theorem app_le_step {a B s y : T} (hc : isOT (psi s y z) = true)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q) :
    app B (psi s y z) ≤ step a B s y z := by
  unfold step
  split_ifs with ht
  · rw [H_eq hc]
    have hBhi := B_le_hi hc ht.1 hBc
    have hcθ : psi s y z < psi (succ s) z z := psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self s))
    rcases (le_iff _ _).mp hBhi with h | h
    · exact le_trans (le_of_lt (app_lt_of_lt_hi h (split_fst_ge _ y) (Or.inr (by simpa [head] using hcθ))))
        (le_app_self _ _)
    · have hlo : (split y (psi (succ s) z z)).2 ≠ z := by
        intro hlo
        have e := split_app (psi (succ s) z z) y
        rw [hlo, app_z_right, ← h] at e
        have := ht.1; rw [← e] at this; exact lt_irrefl' _ this
      rw [if_neg hlo, ← h]
  · rw [step_add hBc]

/-- **One frame keeps the parent standard**: `ψ_a(step a B s y)` is standard when `ψ_a(B)` is, the
subscript is small, and (for `a ≤ s`) the components of `y` at the level `a` are at most the result. -/
theorem step_ot_of_le' {a B s y : T} (hBot : isOT (psi a B z) = true) (hc : isOT (psi s y z) = true)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q) (hsub : ∀ g ∈ comps a s, g ≤ psi s z z)
    (hy : ¬ lt s a = true → ∀ g ∈ comps a y, g ≤ step a B s y z) :
    isOT (psi a (step a B s y z) z) = true := by
  apply ot_parent_small (isOT_sub hBot) (isOT_step (isOT_arg hBot) hc)
  -- the components of `c` are at most the result
  have hcs : ∀ g ∈ comps a (psi s y z), g ≤ step a B s y z := by
    intro g hg
    by_cases hsa : lt s a = true
    · simp [comps, hsa] at hg
    · rw [comps_psi_z_of_ge hsa] at hg
      simp only [List.mem_cons, List.mem_append] at hg
      rcases hg with rfl | hg | hg
      · exact y_le_step hc hBc hsa
      · exact hy hsa g hg
      · exact le_trans (hsub g hg) (om_le_step hc hBc)
  by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
  · have hst : step a B s y z = H s y := by unfold step; rw [if_pos ht]
    rw [hst] at hcs ⊢
    intro g hg
    rw [H_eq hc, comps_app] at hg
    rcases List.mem_append.mp hg with hg | hg
    · -- a component of the high part is a component of `y`
      have hsa : ¬ lt s a = true := not_lt.mpr (le_of_trig ht.2)
      apply hcs
      rw [comps_psi_z_of_ge hsa]
      apply List.mem_cons_of_mem
      apply List.mem_append_left
      have hy' : g ∈ comps a (app (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2) := by
        rw [comps_app]; exact List.mem_append_left _ hg
      rwa [split_app] at hy'
    · split at hg
      · simp [comps] at hg
      · exact hcs g hg
  · have hst : step a B s y z = app B (psi s y z) := by
      unfold step; rw [if_neg ht, step_add hBc]
    rw [hst] at hcs ⊢
    intro g hg
    rw [comps_app] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact le_trans (le_of_lt (comps_lt hBot g hg)) (le_app_self _ _)
    · exact hcs g hg

/-- `step_ot_of_le'` with the components of the subscript at all levels `≤ a` bounded. -/
theorem step_ot_of_le {a B s y : T} (hBot : isOT (psi a B z) = true) (hc : isOT (psi s y z) = true)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q) (hsub : SubSmall a s)
    (hy : ¬ lt s a = true → ∀ g ∈ comps a y, g ≤ step a B s y z) :
    isOT (psi a (step a B s y z) z) = true :=
  step_ot_of_le' hBot hc hBc (hsub a (lt_irrefl' a)) hy

/-- **One frame keeps the parent standard** (natural form): every component of `y` at the level `a` is
at most `y` or at most the plain sum `B + c`. -/
theorem step_ot {a B s y : T} (hBot : isOT (psi a B z) = true) (hc : isOT (psi s y z) = true)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q) (hsub : SubSmall a s)
    (hy : ∀ g ∈ comps a y, g ≤ y ∨ g ≤ app B (psi s y z)) :
    isOT (psi a (step a B s y z) z) = true := by
  refine step_ot_of_le hBot hc hBc hsub (fun hsa g hg => ?_)
  rcases hy g hg with h | h
  · exact le_trans h (y_le_step hc hBc hsa)
  · exact le_trans h (app_le_step hc hBc)

/-- **One frame keeps the parent standard** when `y` is closed at the levels `≤ a`. -/
theorem step_ot_of_closed {a B s y : T} (hBot : isOT (psi a B z) = true)
    (hc : isOT (psi s y z) = true) (hBc : ∀ q ∈ summands B, psi s y z ≤ q) (hsub : SubSmall a s)
    (hcl : Closed a y) :
    isOT (psi a (step a B s y z) z) = true :=
  step_ot hBot hc hBc hsub (fun g hg => Or.inl (hcl a (lt_irrefl' a) g hg))

/-! ## y の仮定は外せない -/

/-- **Counterexample without the hypothesis on `y`**: `a = 0`, `c = ψ_1(ψ_0(Ω_2))` (standard, `SubSmall 0 1`).
Its level-0 component `Ω_2` exceeds the parent's argument, both in a rewriting frame (`B = 0`, the result is
`c`) and in a non-rewriting one (`B = ψ_1(Ω_1)`, the result is `B + c`). -/
theorem step_ot_needs_arg :
    let y : T := psi z (psi (psi z z one) z z) z
    let B : T := psi one (psi one z z) z
    isOT (psi z B z) = true ∧ isOT (psi one y z) = true ∧ (∀ q ∈ summands B, psi one y z ≤ q) ∧
    SubSmall z one ∧
    isOT (psi z (step z B one y z) z) = false ∧ isOT (psi z (step z z one y z) z) = false := by
  intro y B
  have hsub : SubSmall z one := by
    intro u hu g hg
    by_cases huz : u = z
    · subst huz; revert g; decide
    · have hzu : lt z u = true := lt_of_le_of_ne (z_le u) (Ne.symm huz)
      exact absurd hzu hu
  exact ⟨by decide, by decide, by decide, hsub, by decide, by decide⟩

end Ytosk
