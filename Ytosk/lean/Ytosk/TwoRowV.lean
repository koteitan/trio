/-
**1 列落とす補題の枠の段（2 行）。**

経路の節点 p で、M の値 ψ_s(y) と落とした行列の値 ψ_s(y′) の引数は「最後の項だけが違う」（`Shape`）:
y = P + t、y′ = P + t′ で、t′ は 0 か、t と同じ添字の項か、添字の大きい Ω（吸収の連鎖でだけ現れる）。
枠を 1 段上がっても、標準形・引数どうしの ◁・`Shape` が保たれる（`frame_drop`）。PreHi と PreFC を使う。
-/
import Ytosk.TwoRowY

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- The arguments differ only in the last summand. -/
def Shape (a y y' : T) : Prop :=
  ∃ P st u t', y = app P (psi st u z) ∧ y' = app P t' ∧
    (t' = z ∨ (∃ u', t' = psi st u' z) ∨ (∃ s', t' = psi s' z z ∧ lt a s' = true ∧ lt s' st = true))

theorem split_snd_z_of_ge {θ : T} : ∀ {P : T}, (∀ q ∈ summands P, ¬ q < θ) → (split P θ).2 = z
  | z, _ => rfl
  | psi a b c, h => by
    have h1 : ¬ lt (psi a b z) θ = true := h _ (by simp [summands])
    simp only [split, h1, if_false, Bool.false_eq_true]
    exact split_snd_z_of_ge (fun q hq => h q (by simp [summands, hq]))

theorem psi_lt_om_succ {st u s : T} : psi st u z < psi (succ s) z z ↔ st < succ s := by
  rw [psi_lt_psi_z_iff]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact h
    · exact absurd h (T.not_lt_z _)
  · exact Or.inl

/-- With a nonempty low part, the last summand is low. -/
theorem low_of_loP {s P st u : T} (hot : isOT (app P (psi st u z)) = true)
    (hlo : loP s (app P (psi st u z)) ≠ z) : st < succ s := by
  by_contra hst
  have hhigh : ¬ psi st u z < psi (succ s) z z := fun h => hst (psi_lt_om_succ.mp h)
  have hP : (split P (psi (succ s) z z)).2 = z := by
    apply split_snd_z_of_ge
    intro q hq hqlt
    have hle := summand_ge_of_app hot hq
    simp only [head] at hle
    exact hhigh (lt_of_le_of_lt hle hqlt)
  apply hlo
  unfold loP
  rw [split_app_single, if_pos ⟨hP, hhigh⟩]

theorem hiP_app_low {s P st u : T} (h : st < succ s) :
    hiP s (app P (psi st u z)) = (split P (psi (succ s) z z)).1 ∧
      loP s (app P (psi st u z)) ≠ z := by
  have hlow : psi st u z < psi (succ s) z z := psi_lt_om_succ.mpr h
  unfold hiP loP
  rw [split_app_single, if_neg (fun hc => hc.2 hlow)]
  exact ⟨rfl, fun h => by have := (app_eq_z h).2; simp at this⟩

theorem hiP_app_high {s P st u : T} (hP : (split P (psi (succ s) z z)).2 = z) (h : ¬ st < succ s) :
    hiP s (app P (psi st u z)) = app P (psi st u z) ∧ loP s (app P (psi st u z)) = z := by
  have hhigh : ¬ psi st u z < psi (succ s) z z := fun hc => h (psi_lt_om_succ.mp hc)
  unfold hiP loP
  rw [split_app_single, if_pos ⟨hP, hhigh⟩]
  exact ⟨rfl, rfl⟩

theorem hiP_z_right {s P : T} : hiP s (app P z) = (split P (psi (succ s) z z)).1 := by
  rw [app_z_right]; rfl

theorem trig_mono {a B s y y' : T} (hlt : y' < y) (h1 : lt B y' = true)
    (h2 : lt (psi a z z) (psi s y' z) = true) :
    lt B y = true ∧ lt (psi a z z) (psi s y z) = true :=
  ⟨lt_trans (a := B) h1 hlt, lt_trans (a := psi a z z) h2 (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hlt⟩))⟩

theorem notrig_first {a s y y' : T} (htr : lt z y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hn : ¬ (lt z y' = true ∧ lt (psi a z z) (psi s y' z) = true)) : y' = z := by
  by_contra hy'
  have hz : z < y' := lt_of_le_of_ne (z_le y') (Ne.symm hy')
  apply hn
  refine ⟨hz, ?_⟩
  have h2 : psi a z z < psi s y z := htr.2
  rw [psi_lt_psi_z_iff] at h2
  show psi a z z < psi s y' z
  rw [psi_lt_psi_z_iff]
  rcases h2 with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, hz⟩

/-- OT of `ψ_a(Y')` from OT of `ψ_a(Y)` and `Y' ◁ Y`. -/
theorem ot_of_lhd_frame {a Y Y' : T} (han : isOT a = true) (hP : isOT (psi a Y z) = true)
    (hY' : isOT Y' = true) (hl : Lhd z Y' Y) : isOT (psi a Y' z) = true :=
  psi_ot_of_lhd han hY' hl (comps_lt hP) (fun _ g hg => by simp [comps] at hg)

theorem isOT_psi_zz {s : T} (hs : isOT s = true) : isOT (psi s z z) = true := by
  rw [isOT_psi_iff]; exact ⟨hs, rfl, rfl, z_le _, by intro g hg; simp [comps] at hg⟩

/-- **One frame up in the dropped matrix.** -/
theorem frame_drop {a B s y y' : T} (han : isOT a = true)
    (hc : isOT (psi s y z) = true) (hc' : isOT (psi s y' z) = true)
    (hP : isOT (psi a (step a B s y z) z) = true)
    (happ : isOT (app B (psi s y z)) = true)
    (hl : Lhd z y' y) (hsh : Shape s y y')
    (hHi : B ≠ z → lt B y = true → lt (psi a z z) (psi s y z) = true → hiP s y = B ∧ loP s y ≠ z)
    (hFC : B = z → lt z y = true → lt (psi a z z) (psi s y z) = true → a = s →
      hiP s y = z ∧ loP s y ≠ z)
    (hsn : ∀ v, ∀ g ∈ comps v s, g = z) :
    isOT (psi a (step a B s y' z) z) = true ∧ Lhd z (step a B s y' z) (step a B s y z) ∧
      Shape a (step a B s y z) (step a B s y' z) := by
  have hlt : y' < y := hl.1
  have hyot : isOT y = true := isOT_arg hc
  have hBot : isOT B = true := isOT_app_left happ
  have hsot : isOT s = true := isOT_sub hc
  by_cases hB : B = z
  · subst hB
    rw [step_first hc, step_first hc'] at *
    by_cases htr : lt z y = true ∧ lt (psi a z z) (psi s y z) = true
    · rw [if_pos htr] at hP ⊢
      obtain ⟨P, st, u, t', hy, hy', ht'⟩ := hsh
      by_cases hlo : loP s y = z
      · -- absorbed: the parent subscript is smaller
        have has : a < s := by
          have h2 : psi a z z < psi s y z := htr.2
          rw [psi_lt_psi_z_iff] at h2
          rcases h2 with h | ⟨h, _⟩
          · exact h
          · exact absurd hlo (hFC rfl htr.1 htr.2 h).2
        have hyhi : hiP s y = y := by
          have := hiP_loP s y; rw [hlo, app_z_right] at this; exact this
        rw [if_pos hlo, app_z_right, hyhi] at hP ⊢
        have hst : ¬ st < succ s := by
          intro h; exact (hiP_app_low (P := P) (u := u) h).2 (by rw [← hy]; exact hlo)
        have hPs : (split P (psi (succ s) z z)).2 = z := by
          by_contra hne
          have e : loP s (app P (psi st u z)) = app (split P (psi (succ s) z z)).2 (psi st u z) := by
            unfold loP; rw [split_app_single, if_neg (fun hc0 => hne hc0.1)]
          have hne2 : app (split P (psi (succ s) z z)).2 (psi st u z) ≠ z := fun h0 => by
            have := (app_eq_z h0).2; simp at this
          exact hne2 (by rw [← e, ← hy]; exact hlo)
        by_cases htr' : lt z y' = true ∧ lt (psi a z z) (psi s y' z) = true
        · rw [if_pos htr']
          have hlo' : loP s y' = z := by
            rw [hy']
            rcases ht' with rfl | ⟨u', rfl⟩ | ⟨s', rfl, hss', _⟩
            · rw [app_z_right]; exact hPs
            · exact (hiP_app_high hPs hst).2
            · exact (hiP_app_high hPs (fun h => by
                have := succ_le_of_lt hss'
                exact absurd (lt_of_lt_of_le h this) (lt_irrefl' _))).2
          have hyhi' : hiP s y' = y' := by
            have := hiP_loP s y'; rw [hlo', app_z_right] at this; exact this
          rw [if_pos hlo', app_z_right, hyhi']
          refine ⟨ot_of_lhd_frame han hP (isOT_arg hc') hl, hl, P, st, u, t', hy, hy', ?_⟩
          rcases ht' with h | h | ⟨s', h1, h2, h3⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨s', h1, lt_trans (a := a) has h2, h3⟩)
        · rw [if_neg htr']
          have hy0 := notrig_first htr htr'
          rw [hy0] at hy' ⊢
          obtain ⟨hP0, ht0⟩ := app_eq_z hy'.symm
          subst hP0
          rw [app_z] at hy
          have hss : s < st := by
            rcases lt_trichotomy' s st with h | h | h
            · exact h
            · exfalso; subst h; exact hst (lt_succ_self _)
            · exfalso; exact hst (lt_trans (a := st) h (lt_succ_self s))
          have hl0 : Lhd z (psi s z z) y := by rw [hy]; exact lhd_om_psi hss hsn
          refine ⟨ot_of_lhd_frame han hP (isOT_psi_zz hsot) hl0, hl0, z, st, u, psi s z z, by rw [app_z, hy],
            by rw [app_z], Or.inr (Or.inr ⟨s, rfl, has, hss⟩)⟩
      · -- a nonempty low part
        rw [if_neg hlo] at hP ⊢
        have hst : st < succ s := low_of_loP (by rw [← hy]; exact hyot) (by rw [← hy]; exact hlo)
        have hhi : hiP s y = (split P (psi (succ s) z z)).1 := by rw [hy]; exact (hiP_app_low hst).1
        rw [hhi] at hP ⊢
        set C := (split P (psi (succ s) z z)).1 with hCdef
        by_cases htr' : lt z y' = true ∧ lt (psi a z z) (psi s y' z) = true
        · rw [if_pos htr']
          by_cases hlo' : loP s y' = z
          · -- collapse
            have ht0 : t' = z := by
              rcases ht' with h | ⟨u', rfl⟩ | ⟨s', rfl, _, hs'⟩
              · exact h
              · exact absurd (by rw [← hy']; exact hlo') (hiP_app_low (P := P) (u := u') hst).2
              · exact absurd (by rw [← hy']; exact hlo')
                  (hiP_app_low (P := P) (u := z) (lt_trans (a := s') hs' hst)).2
            subst ht0
            rw [app_z_right] at hy'
            have hPs : (split P (psi (succ s) z z)).2 = z := by rw [← hy']; exact hlo'
            have hCP : C = P := by
              have := split_app (psi (succ s) z z) P; rw [hPs, app_z_right] at this; exact this
            have hyhi' : hiP s y' = y' := by
              have := hiP_loP s y'; rw [hlo', app_z_right] at this; exact this
            rw [if_pos hlo', app_z_right, hyhi', hy']
            rw [hCP] at hP ⊢
            refine ⟨ot_prefix hP, lhd_prefix (by simp), P, s, y, z, rfl, by rw [app_z_right], Or.inl rfl⟩
          · rw [if_neg hlo']
            have hhi' : hiP s y' = C := by
              rw [hy']
              rcases ht' with rfl | ⟨u', rfl⟩ | ⟨s', rfl, _, hs'⟩
              · exact hiP_z_right
              · exact (hiP_app_low hst).1
              · exact (hiP_app_low (lt_trans (a := s') hs' hst)).1
            rw [hhi']
            have hCot : isOT C = true := by
              have := hiP_loP s y'; rw [hhi'] at this
              exact isOT_app_left (by rw [this]; exact isOT_arg hc')
            have hY' : isOT (app C (psi s y' z)) = true := by
              apply isOT_app_of hCot hc'
              intro q hq
              have h1 := split_fst_ge (psi (succ s) z z) P q hq
              have h2 : psi s y' z < psi (succ s) z z := psi_lt_om_succ.mpr (lt_succ_self s)
              exact le_of_lt (lt_of_lt_of_le h2 (le_of_not_gt h1))
            have hl' : Lhd z (app C (psi s y' z)) (app C (psi s y z)) := lhd_app C (lhd_psi s hl)
            exact ⟨ot_of_lhd_frame han hP hY' hl', hl', C, s, y, psi s y' z, rfl, rfl,
              Or.inr (Or.inl ⟨y', rfl⟩)⟩
        · rw [if_neg htr']
          have hy0 := notrig_first htr htr'
          rw [hy0] at hy' ⊢
          obtain ⟨hP0, ht0⟩ := app_eq_z hy'.symm
          subst hP0
          have hC0 : C = z := rfl
          rw [hC0, app_z] at hP ⊢
          have hyz : y ≠ z := by rintro rfl; simp [lt] at htr
          have hl0 : Lhd z (psi s z z) (psi s y z) := lhd_psi s (lhd_zero hyz)
          exact ⟨ot_of_lhd_frame han hP (isOT_psi_zz hsot) hl0, hl0, z, s, y, psi s z z, by rw [app_z],
            by rw [app_z], Or.inr (Or.inl ⟨z, rfl⟩)⟩
    · -- no rewriting
      rw [if_neg htr] at hP ⊢
      have htr' : ¬ (lt z y' = true ∧ lt (psi a z z) (psi s y' z) = true) := by
        intro h; exact htr (trig_mono hlt h.1 h.2)
      rw [if_neg htr']
      have hl' : Lhd z (psi s y' z) (psi s y z) := lhd_psi s hl
      exact ⟨ot_of_lhd_frame han hP hc' hl', hl', z, s, y, psi s y' z, by rw [app_z], by rw [app_z],
        Or.inr (Or.inl ⟨y', rfl⟩)⟩
  · -- a nonzero state: both steps append
    have hY := step_append (a := a) hc happ (hHi hB)
    have happ' : isOT (app B (psi s y' z)) = true := by
      apply isOT_app_of hBot hc'
      intro q hq
      have h1 := summand_ge_of_app happ hq
      simp only [head] at h1 ⊢
      exact le_trans (le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hlt⟩))) h1
    have hY' : step a B s y' z = app B (psi s y' z) := by
      apply step_append hc' happ'
      intro h1 h2
      obtain ⟨t1, t2⟩ := trig_mono hlt h1 h2
      obtain ⟨hhi, hlo⟩ := hHi hB t1 t2
      have hyB : y = app B (loP s y) := by have := hiP_loP s y; rw [hhi] at this; exact this.symm
      obtain ⟨c0, hc0, hzc, hcle⟩ := between_app (A := B) (x := z) (y := loP s y) (c := y')
        (by rw [app_z_right]; exact h1) (by rw [← hyB]; exact le_of_lt hlt)
      have hBhi : ∀ q ∈ summands B, ¬ q < psi (succ s) z z := by
        intro q hq; rw [← hhi] at hq; exact split_fst_ge _ y q hq
      have hc0lo : c0 = z ∨ head c0 < psi (succ s) z z := by
        right
        rcases split_snd_head (psi (succ s) z z) y with h | h
        · exact absurd h hlo
        · rcases (le_iff _ _).mp hcle with h' | h'
          · exact lt_of_le_of_lt (head_le_of_lt h') h
          · rw [h']; exact h
      have hsp := split_app_of hBhi hc0lo
      unfold hiP loP
      rw [hc0, hsp]
      exact ⟨rfl, fun h => by subst h; exact T.not_lt_z _ hzc⟩
    rw [hY] at hP
    rw [hY, hY']
    have hl' : Lhd z (app B (psi s y' z)) (app B (psi s y z)) := lhd_app B (lhd_psi s hl)
    exact ⟨ot_of_lhd_frame han hP happ' hl', hl', B, s, y, psi s y' z, rfl, rfl,
      Or.inr (Or.inl ⟨y', rfl⟩)⟩

end Ytosk
