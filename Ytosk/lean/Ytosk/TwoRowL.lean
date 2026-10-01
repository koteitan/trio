/-
**2 行・t = 1・q ≠ r の経路で、低い部分の有無が fsD で変わらない（条件 (L)）。**

経路の列 p の引数の最後の加数は、p より下の経路の列 d の値で、d = x（葉 Ω_{μ+1}）なら p = q。
q ≠ r なら q の添字は μ より大きいので、葉が高い部分に現れることはない。
-/
import Ytosk.TwoRowF

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem last_app : ∀ (B : T) {c : T}, c ≠ z → last (app B c) = last c
  | z, _, _ => by simp
  | psi a b B', c, hc => by
    simp only [app_psi]
    cases hB : app B' c with
    | z => exact absurd (app_eq_z hB).2 hc
    | psi d e f =>
      show last (psi a b (psi d e f)) = last c
      rw [← hB, ← last_app B' hc]
      rw [hB]; rfl

theorem init_app_last : ∀ (t : T), app (init t) (last t) = t
  | z => rfl
  | psi a b z => rfl
  | psi a b (psi c d e) => by
    show app (psi a b (init (psi c d e))) (last (psi c d e)) = psi a b (psi c d e)
    rw [app_psi, init_app_last (psi c d e)]

theorem last_mem : ∀ {t : T}, t ≠ z → last t ∈ summands t
  | z, h => absurd rfl h
  | psi a b z, _ => by simp [last, summands]
  | psi a b (psi c d e), _ => by
    show last (psi c d e) ∈ psi a b z :: summands (psi c d e)
    exact List.mem_cons_of_mem _ (last_mem (by simp))

theorem last_single {t : T} (h : ∃ s y, t = psi s y z) : ∃ s y, last t = psi s y z := by
  obtain ⟨s, y, rfl⟩ := h; exact ⟨s, y, rfl⟩

/-- With no lower part, the last summand is at least the bound. -/
theorem last_ge_of_lo_z {y t : T} (hlo : (split y t).2 = z) (hy : y ≠ z) : ¬ last y < t := by
  have hbpl := split_app t y
  rw [hlo, app_z_right] at hbpl
  have hpge := split_fst_ge t y
  rw [hbpl] at hpge
  exact hpge _ (last_mem hy)

theorem succ_lt_succ' {x y : T} (h : x < y) : succ x < succ y :=
  lt_of_le_of_lt (succ_le_of_lt h) (lt_succ_self y)

theorem omS_lt_omS {x y : T} (h : x < y) : psi (succ x) z z < psi (succ y) z z := by
  rw [psi_lt_psi_z_iff]; exact Or.inl (succ_lt_succ' h)

/-- **Where the last summand of a path argument comes from.** -/
theorem path_last {M : Mat} {x q : Nat} {μ : T} (hG : Good2 M) (hx : x + 1 = M.length)
    (hq : par M 0 x = some q) (hvx : vr M x = succ μ) (hqμ : lt μ (vr M q) = true) :
    ∀ p, Anc0 M p x → p < x → ∃ d, Anc0 M d x ∧ p < d ∧
      last (argOf (o2r M p)) = o2r M d ∧ (d = x → p = q) := by
  have key : ∀ m p, x - p ≤ m → Anc0 M p x → p < x → ∃ d, Anc0 M d x ∧ p < d ∧
      last (argOf (o2r M p)) = o2r M d ∧ (d = x → p = q) := by
    intro m
    induction m with
    | zero => intro p h1 _ h3; omega
    | succ m ih =>
      intro p hm hp hpx
      obtain ⟨c, hc, hcA⟩ := anc0_child hp (by omega)
      have hpc := par_lt M 0 c p hc
      obtain ⟨y, hy⟩ := o2r_sub hG c
      have hcot : isOT (psi (vr M c) y z) = true := by rw [← hy]; exact hG.ot c
      rw [o2r_frame hG hx hcA hc, hy, spArg_single]
      show ∃ d, _ ∧ _ ∧ last (step (vr M p) (bst M p c) (vr M c) y z) = _ ∧ _
      rcases step_cases (a := vr M p) (b := bst M p c) hcot with ⟨B, hB⟩ | ⟨h1, hlo, h3, _⟩
      · refine ⟨c, hcA, hpc, ?_, ?_⟩
        · rw [hB, last_app B (by simp), hy]; rfl
        · intro hcx; subst hcx; rw [hq] at hc; cases hc; rfl
      · rw [h1]
        have hcx : c < x := by
          rcases Nat.eq_or_lt_of_le hcA.le with h' | h'
          · exfalso; subst h'
            rw [o2r_leaf hx (isOT_vr hG.f1 c)] at hy; cases hy; exact h3 rfl
          · exact h'
        obtain ⟨d, hdA, hcd, hld, hdx⟩ := ih c (by omega) hcA hcx
        rw [hy] at hld
        refine ⟨d, hdA, by omega, hld, fun hd => ?_⟩
        exfalso
        have hcq := hdx hd
        subst hd; subst hcq
        have hge := last_ge_of_lo_z hlo h3
        rw [show argOf (psi (vr M c) y z) = y from rfl] at hld
        rw [hld, o2r_leaf hx (isOT_vr hG.f1 _), hvx] at hge
        exact hge (omS_lt_omS hqμ)
  exact fun p => key _ p (Nat.le_refl _)

theorem argOf_path_ne_z {M : Mat} {x : Nat} (hG : Good2 M) (hx : x + 1 = M.length) {d : Nat}
    (hd : Anc0 M d x) (hdx : d < x) : argOf (o2r M d) ≠ z := by
  obtain ⟨c, hc, hcA⟩ := anc0_child hd (by omega)
  obtain ⟨y, hy⟩ := o2r_sub hG c
  have hcot : isOT (psi (vr M c) y z) = true := by rw [← hy]; exact hG.ot c
  rw [o2r_frame hG hx hcA hc, hy, spArg_single]
  show step (vr M d) (bst M d c) (vr M c) y z ≠ z
  rcases step_cases (a := vr M d) (b := bst M d c) hcot with ⟨B, hB⟩ | ⟨h1, _, h3, _⟩
  · rw [hB]; intro h; exact absurd (app_eq_z h).2 (by simp)
  · rw [h1]; exact h3

theorem psi_lt_om_iff {v w u : T} : psi v w z < psi u z z ↔ v < u := by
  rw [psi_lt_psi_z_iff]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact h
    · exact absurd h (by cases w <;> simp)
  · intro h; exact Or.inl h

section
variable {M : Mat} {x q : Nat} {μ : T} (hG : Good2 M) (hx : x + 1 = M.length)
  (hq : par M 0 x = some q) (hvx : vr M x = succ μ) (hqμ : lt μ (vr M q) = true)
include hG hx hq hvx hqμ

theorem path_value_ne_one {d : Nat} (hd : Anc0 M d x) : o2r M d ≠ one := by
  rcases Nat.eq_or_lt_of_le hd.le with h | h
  · subst h
    rw [o2r_leaf hx (isOT_vr hG.f1 _), hvx]
    intro h; simp [one] at h
    exact absurd (app_eq_z h).2 (by simp [one])
  · obtain ⟨w, hw⟩ := o2r_sub hG d
    have hne := argOf_path_ne_z hG hx hd h
    rw [hw] at hne ⊢
    intro h'; simp [one] at h'; exact hne h'.2

theorem isSucc_argOf_path {d : Nat} (hd : Anc0 M d x) (hdx : d < x) :
    isSucc (argOf (o2r M d)) = false := by
  obtain ⟨d', hd'A, _, hl, _⟩ := path_last hG hx hq hvx hqμ d hd hdx
  unfold isSucc
  rw [hl]
  simpa using path_value_ne_one hG hx hq hvx hqμ hd'A

theorem fsD_path_value {d : Nat} {ζ : T} (hd : Anc0 M d x) (hζ : ζ ≠ z) :
    fsD (o2r M d) ζ ≠ z ∧
      (d < x → fsD (o2r M d) ζ = psi (vr M d) (fsD (argOf (o2r M d)) ζ) z) := by
  rcases Nat.eq_or_lt_of_le hd.le with h | h
  · subst h
    refine ⟨?_, fun h' => absurd h' (Nat.lt_irrefl _)⟩
    rw [o2r_leaf hx (isOT_vr hG.f1 _), hvx, fsD_leaf (isSucc_succ μ)
      (by intro h; have := isSucc_succ μ; rw [h] at this; simp [isSucc, last, one] at this)]
    exact hζ
  · obtain ⟨w, hw⟩ := o2r_sub hG d
    have hne := argOf_path_ne_z hG hx hd h
    have hs := isSucc_argOf_path hG hx hq hvx hqμ hd h
    rw [hw] at hne hs ⊢
    have e : fsD (psi (vr M d) w z) ζ = psi (vr M d) (fsD w ζ) z := fsD_psi hne hs ζ
    exact ⟨by rw [e]; simp, fun _ => e⟩

/-- **Condition (L) on the path** (`q ≠ r`, i.e. `v(q) > μ`). -/
theorem L_path {p : Nat} {ζ : T} (hζ : ζ ≠ z) (hp : Anc0 M p x) {s y : T}
    (hc : o2r M p = psi s y z) (hy : y ≠ z) :
    ((split y (psi (succ s) z z)).2 ≠ z → fsD (split y (psi (succ s) z z)).2 ζ ≠ z) ∧
    ((split y (psi (succ s) z z)).2 = z → (split (fsD y ζ) (psi (succ s) z z)).2 = z) := by
  have hpx : p < x := by
    rcases Nat.eq_or_lt_of_le hp.le with h' | h'
    · exfalso; subst h'
      rw [o2r_leaf hx (isOT_vr hG.f1 _)] at hc; cases hc; exact hy rfl
    · exact h'
  obtain ⟨d, hdA, hpd, hl, hdx⟩ := path_last hG hx hq hvx hqμ p hp hpx
  rw [hc] at hl
  change last y = o2r M d at hl
  obtain ⟨hfne, hfeq⟩ := fsD_path_value hG hx hq hvx hqμ hdA hζ
  have hLne : o2r M d ≠ z := by obtain ⟨w, hw⟩ := o2r_sub hG d; rw [hw]; simp
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
    have hdne : d ≠ x := by
      intro hd
      have hpq := hdx hd
      subst hd; subst hpq
      have hge := last_ge_of_lo_z hlo hy
      have hsv : s = vr M p := by
        obtain ⟨w, hw⟩ := o2r_sub hG p; rw [hw] at hc; cases hc; rfl
      rw [hl, o2r_leaf hx (isOT_vr hG.f1 _), hvx, hsv] at hge
      exact hge (omS_lt_omS hqμ)
    have hdx' : d < x := by have := hdA.le; omega
    have hfe := hfeq hdx'
    obtain ⟨w, hw⟩ := o2r_sub hG d
    rw [← init_app_last y, hl, fsD_app _ hLne, hfe]
    rw [hw]
    have hsum : ∀ q ∈ summands y, ¬ q < psi (succ s) z z := by
      intro q hq; rw [hyhi] at hq; exact hpge q hq
    rw [show psi (vr M d) (fsD (argOf (psi (vr M d) w z)) ζ) z = psi (vr M d) (fsD w ζ) z from rfl]
    have hB : ∀ q ∈ summands (app (init y) (psi (vr M d) (fsD w ζ) z)), ¬ q < psi (succ s) z z := by
      intro q hq
      rw [summands_app] at hq
      rcases List.mem_append.mp hq with hq | hq
      · apply hsum
        rw [← init_app_last y, summands_app]; exact List.mem_append_left _ hq
      · simp [summands] at hq; subst hq
        have hL := hsum _ (last_mem hy)
        rw [hl, hw, psi_lt_om_iff] at hL
        rw [psi_lt_om_iff]; exact hL
    have := split_app_of (B := app (init y) (psi (vr M d) (fsD w ζ) z)) (X := z) hB (Or.inl rfl)
    rw [app_z_right] at this
    rw [this]

end

end Ytosk
