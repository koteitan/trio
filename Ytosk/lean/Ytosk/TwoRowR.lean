/-
**2 行・t = 1・q = r の組み立て。**

q = r では o_M(r) = ψ_μ(b + Ω_{μ+1})（b は x の前の兄弟の状態）。r より上で引き上げが起きると、ζ が鎖の次の項にずれる
（`frame_fsD_shift`）。経路上の各列 h で o_{M[k]}(h) = fsD(o_M(h), Z_j)（j は列ごと、Z は始点 γ_1 = ψ_μ(b) の鎖）。
-/
import Ytosk.TwoRowQ

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {x q : Nat} {μ : T} (hG : Good2 M) (hx : x + 1 = M.length)
  (hq : par M 0 x = some q) (hvx : vr M x = succ μ)
include hG hx hq hvx

theorem pvne1 {d : Nat} (hd : Anc0 M d x) : o2r M d ≠ one := by
  rcases Nat.eq_or_lt_of_le hd.le with h | h
  · subst h
    rw [o2r_leaf hx (isOT_vr hG.f1 _), hvx]
    intro h; simp [one] at h
    exact absurd (app_eq_z h).2 (by simp [one])
  · obtain ⟨w, hw⟩ := o2r_sub hG d
    have hne := argOf_path_ne_z hG hx hd h
    rw [hw] at hne ⊢
    intro h'; simp [one] at h'; exact hne h'.2

theorem isSucc_argOf' {d : Nat} (hd : Anc0 M d x) (hdx : d < x) :
    isSucc (argOf (o2r M d)) = false := by
  obtain ⟨d', hd'A, _, hl, _⟩ := path_last_gen hG hx hq d hd hdx
  unfold isSucc
  rw [hl]
  simpa using pvne1 hG hx hq hvx hd'A

theorem fsD_path_value' {d : Nat} {ζ : T} (hd : Anc0 M d x) (hdx : d < x) :
    fsD (o2r M d) ζ = psi (vr M d) (fsD (argOf (o2r M d)) ζ) z := by
  obtain ⟨w, hw⟩ := o2r_sub hG d
  have hne := argOf_path_ne_z hG hx hd hdx
  have hs := isSucc_argOf' hG hx hq hvx hd hdx
  rw [hw] at hne hs ⊢
  exact fsD_psi hne hs ζ

/-- **Condition (L) away from `q`'s argument** (no assumption on `v(q)`). -/
theorem L_gen {p : Nat} {ζ : T} (hp : Anc0 M p x) {s y : T}
    (hc : o2r M p = psi s y z) (hy : y ≠ z) (hne : y ≠ argOf (o2r M q)) :
    ((split y (psi (succ s) z z)).2 ≠ z → fsD (split y (psi (succ s) z z)).2 ζ ≠ z) ∧
    ((split y (psi (succ s) z z)).2 = z → (split (fsD y ζ) (psi (succ s) z z)).2 = z) := by
  have hpx : p < x := by
    rcases Nat.eq_or_lt_of_le hp.le with h' | h'
    · exfalso; subst h'
      rw [o2r_leaf hx (isOT_vr hG.f1 _)] at hc; cases hc; exact hy rfl
    · exact h'
  obtain ⟨d, hdA, hpd, hl, hdx⟩ := path_last_gen hG hx hq p hp hpx
  rw [hc] at hl hdx
  change last y = o2r M d at hl
  have hdne : d ≠ x := fun hd => hne (hdx hd)
  have hdx' : d < x := by have := hdA.le; omega
  have hfe := fsD_path_value' hG hx hq hvx (ζ := ζ) hdA hdx'
  obtain ⟨w, hw⟩ := o2r_sub hG d
  have hwne : w ≠ z := by have := argOf_path_ne_z hG hx hdA hdx'; rw [hw] at this; exact this
  have hLne : o2r M d ≠ z := by rw [hw]; simp
  have hfne : fsD (o2r M d) ζ ≠ z := by rw [hfe]; simp
  have hbpl := split_app (psi (succ s) z z) y
  have hpge := split_fst_ge (psi (succ s) z z) y
  constructor
  · intro hlo
    generalize hP : split y (psi (succ s) z z) = pr at hbpl hlo ⊢
    obtain ⟨hi, lo⟩ := pr
    simp only at hbpl hlo ⊢
    have hll : last lo = o2r M d := by rw [← hl, ← hbpl, last_app hi hlo]
    rw [← init_app_last lo, hll, fsD_app _ hLne]
    intro h'; exact hfne (app_eq_z h').2
  · intro hlo
    have hyhi : y = (split y (psi (succ s) z z)).1 := by rw [hlo, app_z_right] at hbpl; exact hbpl.symm
    rw [← init_app_last y, hl, fsD_app _ hLne, hfe, hw]
    have hsum : ∀ q ∈ summands y, ¬ q < psi (succ s) z z := by
      intro q hq; rw [hyhi] at hq; exact hpge q hq
    have hB : ∀ q ∈ summands (app (init y) (psi (vr M d) (fsD (argOf (psi (vr M d) w z)) ζ) z)),
        ¬ q < psi (succ s) z z := by
      intro q hq
      rw [summands_app] at hq
      rcases List.mem_append.mp hq with hq | hq
      · apply hsum
        rw [← init_app_last y, summands_app]; exact List.mem_append_left _ hq
      · simp [summands] at hq; subst hq
        have hL := hsum _ (last_mem hy)
        rw [hl, hw, psi_lt_om_iff] at hL
        rw [psi_lt_om_iff]; exact hL
    have := split_app_of (B := app (init y) (psi (vr M d) (fsD (argOf (psi (vr M d) w z)) ζ) z))
      (X := z) hB (Or.inl rfl)
    rw [app_z_right] at this
    rw [this]

end

end Ytosk
