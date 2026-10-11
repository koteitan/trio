/-
**3 行・t = 0: 右端の変化で閾値 Ω_w が保たれる（ThrA・ThrV、2026-10-12、t0-exp）。**

T0CutResGG の場面では切り口 κ はいつも Ω_{v(d)}（d は i の前の数える子で葉、d < c）。
そこで o の列 c の引数の右端の変化 y = P + t ↦ y′ = P + T′ について
「W の w で Ω_w < t なら Ω_w < T′」（`ThrA W y y′`）を運ぶ。
- 子の枠の 1 段（`thr_step`、re_step と同じ場合分け）: 両方書き換え lo(y) = 0 なら子の ThrA から、
  lo(y) ≠ 0 と書き換えなしは尾が ψ_s(y) ↦ ψ_s(y′)（添字が同じ、引数は 0 でない）なので無条件。
- 葉の添字の変化（`thr_leaf`）: 尾 Ω_s ↦ Ω_{s′} は v の閾値 `ThrV W s s′` から。
- κ < T′（`thr_cut`）: B = P + κ < y から κ < t、κ = Ω_w で ThrA。
-/
import Ytosk.V3T0RE
import Ytosk.TwoRowT

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **Thresholds kept at the right end**: `Ω_w` (w ∈ W) below the old last summand stays below the new tail. -/
def ThrA (W : T → Prop) (X X' : T) : Prop :=
  ∀ P a x T', X = app P (psi a x z) → X' = app P T' → ∀ w, W w → psi w z z < psi a x z → psi w z z < T'

/-- **Thresholds kept by a subscript.** -/
def ThrV (W : T → Prop) (v v' : T) : Prop := ∀ w, W w → w < v → w < v'

theorem ThrA.mono {W W' : T → Prop} {X X' : T} (h : ThrA W' X X') (hW : ∀ w, W w → W' w) : ThrA W X X' :=
  fun P a x T' h1 h2 w hw => h P a x T' h1 h2 w (hW w hw)

theorem ThrV.mono {W W' : T → Prop} {v v' : T} (h : ThrV W' v v') (hW : ∀ w, W w → W' w) : ThrV W v v' :=
  fun w hw => h w (hW w hw)

/-- `Ω_w < ψ_a(x)` with `x ≠ 0` is `w ≤ a`. -/
theorem om_lt_psi_iff {w a x : T} (hx : x ≠ z) : psi w z z < psi a x z ↔ w ≤ a := by
  rw [psi_lt_psi_z_iff, le_iff]
  constructor
  · rintro (h | ⟨rfl, _⟩)
    · exact Or.inl h
    · exact Or.inr rfl
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, lt_of_le_of_ne (z_le x) (Ne.symm hx)⟩

/-- Same subscript, nonzero arguments: the thresholds `Ω_w` are the same. -/
theorem om_lt_same {w a x x' : T} (hx : x ≠ z) (hx' : x' ≠ z) (h : psi w z z < psi a x z) :
    psi w z z < psi a x' z := (om_lt_psi_iff hx').mpr ((om_lt_psi_iff hx).mp h)

/-- Below `ψ_a(b) + R`, `Ω_w` stays below `ψ_a(b) + R′` when `R′ ≠ 0` whenever `R ≠ 0`. -/
theorem om_lt_keep {w a b R R' : T} (h : psi w z z < psi a b R) (hR : R ≠ z → R' ≠ z) :
    psi w z z < psi a b R' := by
  rw [T.psi_lt_psi] at h ⊢
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · refine Or.inr (Or.inr ⟨h1, h2, ?_⟩)
    have hR0 : R ≠ z := fun h => by rw [h] at h3; exact T.not_lt_z _ h3
    have := hR hR0
    cases R' with
    | z => exact absurd rfl this
    | psi _ _ _ => exact T.z_lt_psi _ _ _

/-- **The last summand is unique.** -/
theorem app_last_inj : ∀ {P P' a a' x x' : T}, app P (psi a x z) = app P' (psi a' x' z) →
    P = P' ∧ a = a' ∧ x = x'
  | z, z, _, _, _, _, h => by
    simp only [app, psi.injEq] at h; exact ⟨rfl, h.1, h.2.1⟩
  | z, psi b1 b2 b3, _, _, _, _, h => by
    simp only [app, psi.injEq] at h
    exact absurd h.2.2.symm (app_ne_z_right (by simp))
  | psi p1 p2 p3, z, _, _, _, _, h => by
    simp only [app, psi.injEq] at h
    exact absurd h.2.2 (app_ne_z_right (by simp))
  | psi p1 p2 p3, psi q1 q2 q3, _, _, _, _, h => by
    simp only [app, psi.injEq] at h
    obtain ⟨rfl, rfl, h3⟩ := h
    obtain ⟨e, ha, hx⟩ := app_last_inj h3
    exact ⟨by rw [e], ha, hx⟩

/-- ThrA from an explicit split: the old last summand `ψ_a(x)` and the new tail `T₀`. -/
theorem thrA_of_split {W : T → Prop} {X X' P a x T0 : T} (hX : X = app P (psi a x z)) (hX' : X' = app P T0)
    (h : ∀ w, W w → psi w z z < psi a x z → psi w z z < T0) : ThrA W X X' := by
  intro P1 a1 x1 T1 h1 h2 w hw hlt
  rw [hX] at h1
  obtain ⟨rfl, rfl, rfl⟩ := app_last_inj h1
  rw [hX'] at h2
  rw [← app_left_cancel0 h2]
  exact h w hw hlt

/-- **A leaf child changes its subscript.** -/
theorem thr_leaf {W : T → Prop} {a B s s' : T} (hss : s' < s) (hBc : ∀ q ∈ summands B, psi s z z ≤ q)
    (hV : ThrV W s s') : ThrA W (step a B s z z) (step a B s' z z) := by
  have hlt : psi s' z z < psi s z z := psi_lt_psi_z_iff.mpr (Or.inl hss)
  have hBc' : ∀ q ∈ summands B, psi s' z z ≤ q := fun q hq => le_trans (le_of_lt hlt) (hBc q hq)
  have hn : ∀ w, ¬ (lt B z = true ∧ lt (psi a z z) (psi w z z) = true) := fun w h => T.not_lt_z _ h.1
  apply thrA_of_split (P := B) (a := s) (x := z) (T0 := psi s' z z)
  · unfold step; rw [if_neg (hn s)]; exact add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc
  · unfold step; rw [if_neg (hn s')]; exact add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc'
  · intro w hw h
    rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
    · exact psi_lt_psi_z_iff.mpr (Or.inl (hV w hw h))
    · exact absurd h (lt_irrefl' _)

/-- **One frame of the thresholds** (the cases of `re_step`). -/
theorem thr_step {W : T → Prop} {a B s y y' : T} (hc : isOT (psi s y z) = true)
    (hc' : isOT (psi s y' z) = true)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q) (hyy : y' < y) (hRE : REr y y')
    (hagree : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) →
      lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true)
    (hT : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → (split y (psi (succ s) z z)).2 = z →
      ThrA W y y') :
    ThrA W (step a B s y z) (step a B s y' z) := by
  have hlt : psi s y' z < psi s y z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hyy⟩)
  have hBc' : ∀ q ∈ summands B, psi s y' z ≤ q := fun q hq => le_trans (le_of_lt hlt) (hBc q hq)
  obtain ⟨P, a', x, T', hy, hy', hT0⟩ := hRE
  have hyz : y ≠ z := by rw [hy]; exact app_ne_z_right (by simp)
  have hy'z : y' ≠ z := by rw [hy']; exact app_ne_z_right hT0
  by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
  · have ht' := hagree ht
    have hst : step a B s y z = H s y := by unfold step; rw [if_pos ht]
    have hst' : step a B s y' z = H s y' := by unfold step; rw [if_pos ht']
    rw [hst, hst']
    set θ := psi (succ s) z z with hθ
    by_cases hlo : (split y θ).2 = z
    · have hHy : H s y = y := H_of_lo_z hc hlo
      have ehi := split_app θ y
      rw [hlo, app_z_right] at ehi
      have hPhi : ∀ q ∈ summands P, ¬ q < θ := by
        intro q hq
        apply split_fst_ge θ y q
        rw [ehi, hy, summands_app]; exact List.mem_append_left _ hq
      have hsp : split y' θ = (app P (split T' θ).1, (split T' θ).2) := by
        rw [hy']; exact split_app_hi T' hPhi
      apply thrA_of_split (P := P) (a := a') (x := x)
        (T0 := app (split T' θ).1 (if (split T' θ).2 = z then z else psi s y' z))
      · rw [hHy]; exact hy
      · rw [H_eq hc', hsp, app_assoc]
      · intro w hw h
        have h1 := hT ht hlo P a' x T' hy hy' w hw h
        have e2 := split_app θ T'
        by_cases h3 : (split T' θ).2 = z
        · rw [if_pos h3, app_z_right]
          rw [h3, app_z_right] at e2; rw [e2]; exact h1
        · rw [if_neg h3]
          cases hhi : (split T' θ).1 with
          | z =>
            rw [hhi] at e2
            simp only [app] at e2 ⊢
            have hlow : (split T' θ).2 < θ := by
              rcases split_snd_head θ T' with h4 | h4
              · exact absurd h4 h3
              · exact lt_of_head_lt h4
            rw [e2] at hlow
            have hwθ : psi w z z < θ := lt_trans h1 hlow
            have hws : w ≤ s := lt_succ_iff.mp ((psi_lt_psi_z_iff.mp hwθ).elim id
              (fun h => absurd h.2 (lt_irrefl' _)))
            exact (om_lt_psi_iff hy'z).mpr hws
          | psi h1' h2' h3' =>
            rw [hhi] at e2
            rw [← e2] at h1
            simp only [app] at h1 ⊢
            exact om_lt_keep h1 (fun _ => app_ne_z_right (by simp))
    · have e := split_app θ y
      rw [hy] at e
      have hlo' : (split (app P (psi a' x z)) θ).2 ≠ z := by rw [← hy]; exact hlo
      obtain ⟨R0, hR0⟩ := prefix_of_app_single e hlo'
      rw [← hy] at hR0
      have hlo_eq : (split y θ).2 = app R0 (psi a' x z) := by
        apply app_left_cancel0 (p := (split y θ).1)
        rw [← app_assoc, ← hR0, ← hy, split_app]
      have hhead : head (split y θ).2 < θ := by
        rcases split_snd_head θ y with h | h
        · exact absurd h hlo
        · exact h
      have hTt : T' < psi a' x z := by
        have h := hyy
        rw [hy, hy'] at h
        exact (app_lt_app_left_iff P).mp h
      have hhd : head (app R0 T') < θ := by
        cases R0 with
        | z =>
          simp only [app] at hlo_eq ⊢
          rw [hlo_eq] at hhead
          exact lt_of_le_of_lt (head_le_of_lt hTt) hhead
        | psi r1 r2 r3 =>
          rw [hlo_eq] at hhead
          simpa [head, app] using hhead
      have hy'e : y' = app (split y θ).1 (app R0 T') := by rw [hy', hR0, app_assoc]
      have hsp : split y' θ = ((split y θ).1, app R0 T') := by
        rw [hy'e, split_app_hi (app R0 T') (split_fst_ge θ y), split_low (Or.inr hhd), app_z_right]
      have hne : app R0 T' ≠ z := app_ne_z_right hT0
      apply thrA_of_split (P := (split y θ).1) (a := s) (x := y) (T0 := psi s y' z)
      · rw [H_eq hc, if_neg hlo]
      · rw [H_eq hc', hsp, if_neg hne]
      · intro w _ h; exact om_lt_same hyz hy'z h
  · have hnt' : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true) := fun h =>
      ht ⟨lt_trans (show B < y' from h.1) hyy, lt_trans (show psi a z z < psi s y' z from h.2) hlt⟩
    apply thrA_of_split (P := B) (a := s) (x := y) (T0 := psi s y' z)
    · unfold step; rw [if_neg ht]; exact add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc
    · unfold step; rw [if_neg hnt']; exact add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc'
    · intro w _ h; exact om_lt_same hyz hy'z h

/-- **The thresholds of a column** `c` (counted child of `k`): `v` of the counted children of `k` before `c`, and
the thresholds of `k` when the frame `(k, c)` rewrites with no low part (the last summand passes up). -/
inductive ThrSet (M : Mat) (ρ : Valn) : Nat → T → Prop
  | sib {k c d : Nat} {Lc R : List Nat} : CL M k = Lc ++ c :: R → d ∈ Lc → ThrSet M ρ c (ρ.v d)
  | up {k c : Nat} {Lc R : List Nat} {s y w : T} : CL M k = Lc ++ c :: R → ρ.o c = psi s y z →
      lt (spArg (ρ.v k) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v k) z z) (psi s y z) = true →
      (split y (psi (succ s) z z)).2 = z → ThrSet M ρ k w → ThrSet M ρ c w

/-- **The thresholds are `v` of earlier columns.** -/
theorem ThrSet.earlier {M : Mat} {ρ : Valn} : ∀ {c : Nat} {w : T}, ThrSet M ρ c w → ∃ j, j < c ∧ w = ρ.v j
  | _, _, @ThrSet.sib _ _ k c d Lc R h hd => by
    have hs : (CL M k).Pairwise (· < ·) := (children_sorted M k).filter _
    rw [h] at hs
    exact ⟨d, (List.pairwise_append.mp hs).2.2 d hd c List.mem_cons_self, rfl⟩
  | _, _, @ThrSet.up _ _ k c Lc R _ _ _ h _ _ _ hk => by
    obtain ⟨j, hj, rfl⟩ := ThrSet.earlier hk
    have hkc : k < c := (mem_children (cl_mem_children (show c ∈ CL M k by rw [h]; simp))).1
    exact ⟨j, by omega, rfl⟩

/-- **The cut below the new tail**: `B = P + κ < y`, `κ = Ω_w` with `w ∈ W`, and `ThrA W y y′`. -/
theorem thr_cut {W : T → Prop} {B y y' P a x T' κ w : T} (hT : ThrA W y y') (hB : lt B y = true)
    (hy : y = app P (psi a x z)) (hy' : y' = app P T') (hBk : B = app P κ) (hκ : κ = psi w z z)
    (hw : W w) : κ < T' := by
  have h : κ < psi a x z := by
    have := hB; rw [hy, hBk] at this; exact (app_lt_app_left_iff P).mp this
  rw [hκ] at h ⊢
  exact hT P a x T' hy hy' w hw h

end Ytosk
