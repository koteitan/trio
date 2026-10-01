/-
**2 行: 枠の不変条件 PreHi・PreFC と、枠の分類。**

- PreHi: 書き換えが起きる枠で前の兄弟の状態 B ≠ 0 なら、B は子の引数 y の高い部分（Ω_{s+1} 以上）そのもので、
  低い部分は空でない。このとき step は「後ろに足す」と同じ（`step_append`）。
- PreFC: 最初の子の枠（B = 0）で書き換えが起き、親と子の添字が等しいなら、子の引数は低い部分だけ（高い部分が空）。
- `o2r_frame'`: 親の値 = ψ(spArg(状態, 経路の子の値))。行列全体の Good2 でなく、その節点の子の値の条件だけを仮定する。
-/
import Ytosk.TwoRowX

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- The high part of `y` relative to `ψ_s`: the summands `≥ Ω_{s+1}`. -/
def hiP (s y : T) : T := (split y (psi (succ s) z z)).1
/-- The low part: the summands `< Ω_{s+1}`. -/
def loP (s y : T) : T := (split y (psi (succ s) z z)).2

theorem hiP_loP (s y : T) : app (hiP s y) (loP s y) = y := split_app _ y

/-- **PreHi** at every frame. -/
def PreHi (M : Mat) : Prop :=
  ∀ h p s y, p < M.length → par M 0 p = some h → o2r M p = psi s y z →
    bst M h p ≠ z → lt (bst M h p) y = true → lt (psi (vr M h) z z) (psi s y z) = true →
    hiP s y = bst M h p ∧ loP s y ≠ z

/-- **PreFC** at every first-child frame: with equal subscripts the argument is all low. -/
def PreFC (M : Mat) : Prop :=
  ∀ h p s y, p < M.length → par M 0 p = some h → o2r M p = psi s y z →
    bst M h p = z → lt z y = true → lt (psi (vr M h) z z) (psi s y z) = true → vr M h = s →
    hiP s y = z ∧ loP s y ≠ z

/-- **With a nonzero state and PreHi, the step appends.** -/
theorem step_append {a B s y : T} (hc : isOT (psi s y z) = true)
    (happ : isOT (app B (psi s y z)) = true)
    (hhi : lt B y = true → lt (psi a z z) (psi s y z) = true → hiP s y = B ∧ loP s y ≠ z) :
    step a B s y z = app B (psi s y z) := by
  unfold step
  split_ifs with htr
  · obtain ⟨h1, h2⟩ := hhi htr.1 htr.2
    rw [H_eq hc]
    unfold hiP at h1
    unfold loP at h2
    rw [if_neg h2, h1]
  · exact add_eq_app happ

/-- **The first-child step**: `H` when it rewrites, else the child itself. -/
theorem step_first {a s y : T} (hc : isOT (psi s y z) = true) :
    step a z s y z = if lt z y = true ∧ lt (psi a z z) (psi s y z) = true then
      app (hiP s y) (if loP s y = z then z else psi s y z) else psi s y z := by
  unfold step
  by_cases htr : lt z y = true ∧ lt (psi a z z) (psi s y z) = true
  · rw [if_pos htr, if_pos htr, H_eq hc]; rfl
  · rw [if_neg htr, if_neg htr, add_z_left]

/-- **The node over its last child**, from conditions on its children only. -/
theorem o2r_frame' {N : Mat} {h p : Nat} (hF : F1 N)
    (hlast : children N h = (children N h).filter (fun d => decide (d < p)) ++ [p])
    (hsing : ∀ t ∈ (children N h).map (o2r N), Single t)
    (hdec : ((children N h).map (o2r N)).Pairwise (fun a b => b ≤ a)) :
    o2r N h = psi (vr N h) (spArg (vr N h) (bst N h p) (o2r N p)) z := by
  set C := (children N h).filter (fun d => decide (d < p)) with hCdef
  have hS := sumN_dec _ hsing hdec
  have hdM := hdec
  rw [hlast, List.map_append] at hdM
  have hsumM : sumN ((children N h).map (o2r N)) = app (sumN (C.map (o2r N))) (o2r N p) := by
    have hs2 : ∀ t ∈ C.map (o2r N) ++ [o2r N p], Single t := by
      intro t ht; apply hsing; rw [hlast, List.map_append]; simpa using ht
    rw [hlast, List.map_append]
    exact sumN_snoc_dec hs2 hdM
  rw [o2r_spArg (isOT_vr hF h) hS.1, hsumM, spArg_app]
  rfl

/-! ## 単項を足した和の高い部分・低い部分、先頭部分の標準形 -/

theorem split_app_single {θ : T} : ∀ (P : T) {st u : T},
    split (app P (psi st u z)) θ =
      if (split P θ).2 = z ∧ ¬ lt (psi st u z) θ = true then (app P (psi st u z), z)
      else ((split P θ).1, app (split P θ).2 (psi st u z))
  | z, st, u => by
    by_cases h : lt (psi st u z) θ = true
    · simp [split, h]
    · simp [split, h]
  | psi a b c, st, u => by
    have ih := split_app_single c (θ := θ) (st := st) (u := u)
    by_cases h : lt (psi a b z) θ = true
    · simp only [app_psi, split, h, if_true]
      rw [if_neg (by simp)]
    · simp only [app_psi, split, h, if_false, Bool.false_eq_true]
      rw [ih]
      by_cases h2 : (split c θ).2 = z ∧ ¬ lt (psi st u z) θ = true
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2]

/-- **A standard `ψ_a(P + X)` stays standard without `X`.** -/
theorem ot_prefix {a P X : T} (h : isOT (psi a (app P X) z) = true) :
    isOT (psi a P z) = true := by
  obtain ⟨h1, h2, _, _, h5⟩ := isOT_psi_iff.mp h
  rw [isOT_psi_iff]
  refine ⟨h1, isOT_app_left h2, rfl, z_le _, ?_⟩
  intro g hg
  have hg' : g < app P X := h5 g (by rw [comps_app]; exact List.mem_append_left _ hg)
  have hsz := size_comps hg
  rcases lt_trichotomy' g P with hlt | heq | hgt
  · exact hlt
  · subst heq; omega
  · exfalso
    obtain ⟨c0, rfl, _, _⟩ := between_app (A := P) (x := z) (y := X) (c := g)
      (by rw [app_z_right]; exact hgt) (le_of_lt hg')
    rw [size_app] at hsz; omega

/-- Natural-number subscripts have only zero components. -/
theorem comps_nT : ∀ (k : Nat) (v : T), ∀ g ∈ comps v (nT k), g = z
  | 0, _, g, hg => by simp [nT, comps] at hg
  | k + 1, v, g, hg => by
    rw [nT_succ, show succ (nT k) = app (nT k) one from rfl, comps_app] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact comps_nT k v g hg
    · simp only [one, comps] at hg
      split at hg <;> simp at hg; exact hg

/-- `Ω_s = ψ_s(0)` is below `ψ_{st}(u)` for `s < st`, with no index components (natural `s`). -/
theorem lhd_om_psi {s st u : T} (hs : lt s st = true) (hsn : ∀ v, ∀ g ∈ comps v s, g = z) :
    Lhd z (psi s z z) (psi st u z) := by
  refine ⟨by rw [psi_lt_psi_z_iff]; exact Or.inl hs, fun v c _ _ x hx => ?_⟩
  have hx0 : x = z := by
    simp only [comps, List.mem_append] at hx
    rcases hx with hx | hx
    · split at hx
      · simp at hx
      · simp only [List.mem_cons, List.mem_append] at hx
        rcases hx with rfl | hx | hx
        · rfl
        · simp [comps] at hx
        · exact hsn v x hx
    · simp [comps] at hx
  subst hx0
  exact ⟨z, List.mem_append_right _ (by simp [Gc]), le_refl _⟩

end Ytosk
