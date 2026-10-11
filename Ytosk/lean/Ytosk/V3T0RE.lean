/-
**3 行・t = 0: 右端の変化（RE）の枠 1 段の補題。**

D の列の引数 y が新しい y′ と「最後の加数だけ違う」（y = P + t、t は 1 項、y′ = P + T′、T′ ≠ 0）とき:
- `trig_agree`: 古い枠が書き換えるなら新しい枠も（PH3c の種類 eq・pre・cut ごとに。cut が t の中なら CutResG）。
- `re_step`: 親の引数 step(B, ψ_s(y)) と step(B, ψ_s(y′)) も最後の加数だけ違う。
- `re_leaf`: 子が ψ_s(0) から ψ_{s′}(0) に替わるときも同じ。
-/
import Ytosk.V3T0Cut
import Ytosk.V3RelR
import Ytosk.V3T0OT
import Ytosk.V3DropR

namespace Ytosk

open T

/-- The right-end relation of two arguments. -/
def REr (y y' : T) : Prop := ∃ P a x T', y = app P (psi a x z) ∧ y' = app P T' ∧ T' ≠ z

theorem app_left_cancel0 : ∀ {p y y' : T}, app p y = app p y' → y = y'
  | z, _, _, h => h
  | psi a b c, y, y', h => by
    simp only [app_psi, psi.injEq] at h
    exact app_left_cancel0 h.2.2

theorem app_ne_z_right {x y : T} (hy : y ≠ z) : app x y ≠ z := fun h => hy (app_eq_z h).2

/-- **A rewriting frame keeps rewriting** when its argument changes only at the right end. -/
theorem trig_agree {a B s y y' : T} (hRE : REr y y')
    (hK : B ≠ z → PH3cKind B (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s)
    (hcut : (split y (psi (succ s) z z)).2 = z → B ≠ z → ∀ P a' x T', y = app P (psi a' x z) → y' = app P T' →
      ∀ κ ∈ cutsNS s (psi a' x z), B = app P κ → κ < T')
    (htr : lt B y = true ∧ lt (psi a z z) (psi s y z) = true) :
    lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true := by
  obtain ⟨P, a', x, T', rfl, rfl, hT⟩ := hRE
  have hPT : P < app P T' := lt_app_ne hT
  have hBlt : B < app P T' := by
    by_cases hB : B = z
    · rw [hB]; exact lt_of_le_of_lt (z_le P) hPT
    set θ := psi (succ s) z z
    have e := split_app θ (app P (psi a' x z))
    rcases hK hB with ⟨heq, hlo⟩ | ⟨_, (⟨R, hR, hhi⟩ | ⟨_, hc⟩)⟩
    · rw [heq] at e
      obtain ⟨R0, hR0⟩ := prefix_of_app_single e hlo
      rw [hR0, app_assoc]
      exact lt_app_ne (app_ne_z_right hT)
    · rw [hhi, app_assoc] at e
      obtain ⟨R0, hR0⟩ := prefix_of_app_single e (fun h => hR (app_eq_z h).1)
      rw [hR0, app_assoc]
      exact lt_app_ne (app_ne_z_right hT)
    · by_cases hlo : (split (app P (psi a' x z)) θ).2 = z
      · have e' := e
        rw [hlo, app_z_right] at e'
        rw [e'] at hc
        rcases cutsNS_app hc with h | ⟨κ, hκ, hBk⟩
        · exact lt_of_le_of_lt (cutsNS_le h) hPT
        · rw [hBk]; exact app_lt_app_left P (hcut hlo hB P a' x T' rfl rfl κ hκ hBk)
      · obtain ⟨R0, hR0⟩ := prefix_of_app_single e hlo
        have hle : (split (app P (psi a' x z)) θ).1 ≤ P := by
          have := le_app_self (split (app P (psi a' x z)) θ).1 R0; rwa [← hR0] at this
        exact lt_of_le_of_lt (le_trans (cutsNS_le hc) hle) hPT
  refine ⟨hBlt, ?_⟩
  have h2 : psi a z z < psi s (app P (psi a' x z)) z := htr.2
  show psi a z z < psi s (app P T') z
  rcases psi_lt_psi_z_iff.mp h2 with h | ⟨rfl, _⟩
  · exact psi_lt_psi_z_iff.mpr (Or.inl h)
  · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_lt (z_le _) hPT⟩)

/-- **One frame of RE**: the arguments of the parent differ only at the right end. -/
theorem re_step {a B s y y' : T} (hc : isOT (psi s y z) = true) (hc' : isOT (psi s y' z) = true)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q) (hyy : y' < y) (hRE : REr y y')
    (hagree : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) →
      lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true) :
    REr (step a B s y z) (step a B s y' z) := by
  have hlt : psi s y' z < psi s y z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hyy⟩)
  have hBc' : ∀ q ∈ summands B, psi s y' z ≤ q := fun q hq => le_trans (le_of_lt hlt) (hBc q hq)
  by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
  · have ht' := hagree ht
    have hst : step a B s y z = H s y := by unfold step; rw [if_pos ht]
    have hst' : step a B s y' z = H s y' := by unfold step; rw [if_pos ht']
    rw [hst, hst']
    obtain ⟨P, a', x, T', hy, hy', hT⟩ := hRE
    set θ := psi (succ s) z z with hθ
    by_cases hlo : (split y θ).2 = z
    · -- `y` is all high: `H s y = y`, and `H s y′ = P + (hi(T′) + …)`
      have hHy : H s y = y := H_of_lo_z hc hlo
      have ehi := split_app θ y
      rw [hlo, app_z_right] at ehi
      have hPhi : ∀ q ∈ summands P, ¬ q < θ := by
        intro q hq
        apply split_fst_ge θ y q
        rw [ehi, hy, summands_app]; exact List.mem_append_left _ hq
      have hsp : split y' θ = (app P (split T' θ).1, (split T' θ).2) := by rw [hy']; exact split_app_hi T' hPhi
      refine ⟨P, a', x, app (split T' θ).1 (if (split T' θ).2 = z then z else psi s y' z), by rw [hHy]; exact hy,
        ?_, ?_⟩
      · rw [H_eq hc', hsp, app_assoc]
      · intro h
        obtain ⟨h1, h2⟩ := app_eq_z h
        have e2 := split_app θ T'
        rw [h1] at e2
        by_cases h3 : (split T' θ).2 = z
        · rw [h3, app_z_right] at e2; exact hT e2.symm
        · rw [if_neg h3] at h2; simp at h2
    · -- `y` has a low part: `t` is low, and `H s y = hi + ψ_s(y)`, `H s y′ = hi + ψ_s(y′)`
      have e := split_app θ y
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
      have hne : app R0 T' ≠ z := app_ne_z_right hT
      refine ⟨(split y θ).1, s, y, psi s y' z, ?_, ?_, by simp⟩
      · rw [H_eq hc, if_neg hlo]
      · rw [H_eq hc', hsp, if_neg hne]
  · have hnt' : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true) := fun h =>
      ht ⟨lt_trans (show B < y' from h.1) hyy, lt_trans (show psi a z z < psi s y' z from h.2) hlt⟩
    refine ⟨B, s, y, psi s y' z, ?_, ?_, by simp⟩
    · unfold step; rw [if_neg ht]; exact add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc
    · unfold step; rw [if_neg hnt']; exact add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc'

/-- **A leaf child changes its subscript**: `B + Ω_s` against `B + Ω_{s′}`. -/
theorem re_leaf {a B s s' : T} (hss : s' < s) (hBc : ∀ q ∈ summands B, psi s z z ≤ q) :
    REr (step a B s z z) (step a B s' z z) := by
  have hlt : psi s' z z < psi s z z := psi_lt_psi_z_iff.mpr (Or.inl hss)
  have hBc' : ∀ q ∈ summands B, psi s' z z ≤ q := fun q hq => le_trans (le_of_lt hlt) (hBc q hq)
  have hn : ∀ w, ¬ (lt B z = true ∧ lt (psi a z z) (psi w z z) = true) := fun w h => T.not_lt_z _ h.1
  refine ⟨B, s, z, psi s' z z, ?_, ?_, by simp⟩
  · unfold step; rw [if_neg (hn s)]; exact add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc
  · unfold step; rw [if_neg (hn s')]; exact add_eq_app_of_ge ⟨_, _, rfl⟩ B hBc'

/-! ## g の枠 -/

/-- **RE at `g` with no middle copy root counted** (the old frame does not rewrite at `r`). -/
theorem s0_re {a B v Y0 X' : T}
    (hBX : ∀ q ∈ summands B, psi v (app Y0 one) z ≤ q)
    (hX' : Single X') (hl : X' < psi v (app Y0 one) z)
    (hy' : ∀ s' y', X' = psi s' y' z → s' ≠ v → y' = z)
    (hnt : ¬ (lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true)) :
    REr (spArg a B (psi v (app Y0 one) z)) (spArg a (spArg a B (mulT (psi v Y0 z) 0)) X') := by
  obtain ⟨s', y', rfl⟩ := hX'.2
  have hnew : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) := by
    rintro ⟨h1, h2⟩
    by_cases hs : s' = v
    · subst hs
      have hyy : y' < app Y0 one := by
        rcases psi_lt_psi_z_iff.mp hl with h | ⟨_, h⟩
        · exact absurd h (lt_irrefl' _)
        · exact h
      exact hnt ⟨lt_trans (show B < y' from h1) hyy, lt_trans (show psi a z z < psi s' y' z from h2) hl⟩
    · have := hy' s' y' rfl hs
      rw [this] at h1; exact T.not_lt_z _ h1
  refine ⟨B, v, app Y0 one, psi s' y' z, ?_, ?_, by simp⟩
  · rw [spArg_single]; unfold step; rw [if_neg hnt]; exact add_eq_app_of_ge ⟨_, _, rfl⟩ B hBX
  · show spArg a B (psi s' y' z) = _
    rw [spArg_single]; unfold step; rw [if_neg hnew]
    exact add_eq_app_of_ge ⟨_, _, rfl⟩ B (fun q hq => le_trans (le_of_lt hl) (hBX q hq))

/-- **RE at `g` with `m ≥ 1` middle copies** before the last copy root. -/
theorem s1_re {a B v Y0 X' : T} {m : Nat} (hm : 1 ≤ m)
    (hX : isOT (psi v (app Y0 one) z) = true) (hO : isOT (psi v Y0 z) = true)
    (hBX : ∀ q ∈ summands B, psi v (app Y0 one) z ≤ q)
    (hX' : Single X') (hX'O : X' ≤ psi v Y0 z)
    (hy' : ∀ s' y', X' = psi s' y' z → s' ≠ v → y' = z) :
    REr (spArg a B (psi v (app Y0 one) z)) (spArg a (spArg a B (mulT (psi v Y0 z) m)) X') := by
  obtain ⟨s', y', rfl⟩ := hX'.2
  have hOX : psi v Y0 z < psi v (app Y0 one) z := psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_app_one Y0⟩)
  have hBO : ∀ q ∈ summands B, psi v Y0 z ≤ q := fun q hq => le_trans (le_of_lt hOX) (hBX q hq)
  set O := psi v Y0 z with hOdef
  set B' := spArg a B (mulT O m) with hB'
  have hnr := no_rw_after (a := a) (B := B) hO hm
  rw [← hOdef, ← hB'] at hnr
  have hB'O : ∀ q ∈ summands B', O ≤ q :=
    spArg_summands_ge ⟨v, Y0, rfl⟩ (mulT O m) B (isOT_mulT hO ⟨_, _, rfl⟩ m)
      (fun q hq => by rw [summands_mulT ⟨_, _, rfl⟩ m q hq]) hBO
  have hnew : ¬ (lt B' y' = true ∧ lt (psi a z z) (psi s' y' z) = true) := by
    rintro ⟨h1, h2⟩
    by_cases hs : s' = v
    · subst hs
      have hyy : y' ≤ Y0 := by
        rcases (le_iff _ _).mp hX'O with h | h
        · rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact le_of_lt h
        · rw [hOdef] at h; simp only [psi.injEq] at h; rw [h.2.1]
      exact hnr ⟨lt_of_lt_of_le h1 hyy, lt_of_lt_of_le h2 hX'O⟩
    · have := hy' s' y' rfl hs
      rw [this] at h1; exact T.not_lt_z _ h1
  have hN : spArg a B' (psi s' y' z) = app B' (psi s' y' z) := by
    rw [spArg_single]; unfold step; rw [if_neg hnew]
    exact add_eq_app_of_ge ⟨_, _, rfl⟩ _ (fun q hq => le_trans hX'O (hB'O q hq))
  -- the first copy, and the copies after it
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hfirst : B' = app (step a B v Y0 z) (mulT O m') := by
    rw [hB']
    show spArg a B (app (psi v Y0 z) (mulT (psi v Y0 z) m')) = _
    rw [app_psi, app_z, spArg_cons, step_rest a B v Y0 _ z]
    apply spArg_copies hO
    · unfold step
      split_ifs with ht
      · exact Or.inl (le_H hO)
      · by_cases h2 : psi a z z < psi v Y0 z
        · left
          have hBY : Y0 ≤ B := by
            rcases lt_or_ge B Y0 with h | h
            · exact absurd ⟨h, h2⟩ ht
            · exact h
          exact le_trans hBY (le_of_lt (by
            have := add_lt_add_left B (T.z_lt_psi v Y0 z); rwa [add_z_right] at this))
        · exact Or.inr h2
    · exact step_summands_ge hO hBO
  -- a common prefix `P` of the old argument and of the first state
  set θ := psi (succ v) z z with hθ
  have key : ∃ P R, spArg a B (psi v (app Y0 one) z) = app P (psi v (app Y0 one) z) ∧
      step a B v Y0 z = app P R := by
    by_cases ht : lt B (app Y0 one) = true ∧ lt (psi a z z) (psi v (app Y0 one) z) = true
    · have hone : head one < θ := by
        show psi z z z < _; rw [psi_lt_psi_z_iff]; left
        exact lt_of_le_of_lt (z_le v) (lt_succ_self v)
      have hs1 : split (app Y0 one) θ = ((split Y0 θ).1, app (split Y0 θ).2 one) :=
        split_app_low (Or.inr hone)
      have hP : spArg a B (psi v (app Y0 one) z) = app (split Y0 θ).1 (psi v (app Y0 one) z) := by
        rw [spArg_single]; unfold step; rw [if_pos ht, H_eq hX, if_neg (split_succ_lo_ne v Y0), hs1]
      by_cases ht0 : lt B Y0 = true ∧ lt (psi a z z) (psi v Y0 z) = true
      · exact ⟨_, _, hP, by unfold step; rw [if_pos ht0, H_eq hO]⟩
      · have hst : step a B v Y0 z = app B O := by
          unfold step; rw [if_neg ht0]; exact add_eq_app_of_ge ⟨_, _, rfl⟩ B hBO
        have hBle : B ≤ Y0 := lt_succ_iff.mp ht.1
        rcases (le_iff _ _).mp hBle with hBY | hBY
        · -- `B < Y0`: then `a = v` and `Y0 = 0`
          have h2 : ¬ psi a z z < psi v Y0 z := fun h => ht0 ⟨hBY, h⟩
          have hY0 : Y0 = z := by
            rcases psi_lt_psi_z_iff.mp (show psi a z z < psi v (app Y0 one) z from ht.2) with h | ⟨rfl, _⟩
            · exact absurd (psi_lt_psi_z_iff.mpr (Or.inl h)) h2
            · by_contra hne
              exact h2 (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hne)⟩))
          subst hY0
          exact ⟨_, app B O, hP, by rw [hst]; rfl⟩
        · -- `B = Y0`: the high part of `Y0` is a prefix of `B`
          refine ⟨_, app (split Y0 θ).2 O, hP, ?_⟩
          rw [hst, ← app_assoc, split_app, hBY]
    · refine ⟨B, O, ?_, ?_⟩
      · rw [spArg_single]; unfold step; rw [if_neg ht]; exact add_eq_app_of_ge ⟨_, _, rfl⟩ B hBX
      · have hnt0 : ¬ (lt B Y0 = true ∧ lt (psi a z z) (psi v Y0 z) = true) := fun h =>
          ht ⟨lt_trans (show B < Y0 from h.1) (lt_app_one Y0), lt_trans (show psi a z z < O from h.2) hOX⟩
        unfold step; rw [if_neg hnt0]; exact add_eq_app_of_ge ⟨_, _, rfl⟩ B hBO
  obtain ⟨P, R, hP, hR⟩ := key
  refine ⟨P, v, app Y0 one, app R (app (mulT O m') (psi s' y' z)), hP, ?_, ?_⟩
  · rw [hN, hfirst, hR, app_assoc, app_assoc]
  · exact app_ne_z_right (app_ne_z_right (by simp))

end Ytosk
