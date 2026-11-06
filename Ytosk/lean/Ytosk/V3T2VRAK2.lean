/-
**t = 2: the frame condition `KAG2` of the copy frames (2026-11-06).**

`KAG`'s moving-position field `KG` is false on the standard forms (tmp/claude/measure_t2vrak86.py: 2643 failures
on the graft sets, e.g. at `V = 0`, `s = a`: the moving components of `s − V` are those of `a − V`).
`KAG2` adds a third alternative to `KG`: the moving component `g` of `s − V` is below a moving component `d` of
`a − V`.  Then `σ g ≤ σ d`, and `σ d` is a component of `f(a)` (`compsAN_sh_fwdK`), the third alternative of the
transported `QVRAt`.  `KAG2` is weaker than `KAG`; `qVRAshK_KVRA2` is the σ transport.
-/
import Ytosk.V3T2VRAK

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- Components at moving positions survive the shift at every level at most `V` (the copy of
`ClShLGuarded.compsAN_sh_forward`, which sits above this file). -/
theorem compsAN_sh_fwdK {V V' u : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (huV : u ≤ V) :
    ∀ (n : Nat) {t g : T}, isOT t = true → g ∈ compsAN V u n t →
      sh V V' g ∈ comps u (sh V V' t)
  | 0, _, _, _, hg => by simp [compsAN] at hg
  | n + 1, z, _, _, hg => by simp [compsAN] at hg
  | n + 1, psi s y c, g, ht, hg => by
    simp only [compsAN, List.mem_append] at hg
    rcases hg with hg | hg
    · by_cases hc : ¬ lt s u = true ∧ lt V s = true
      · rw [if_pos hc] at hg
        rw [sh_psi_gt hc.2]
        have hfu : ¬ shf V V' s < u := not_lt.mpr
          (le_trans huV (le_trans (le_of_lt hVV)
            (le_of_lt (lt_shf hV hV' (le_of_lt hVV) (isOT_sub ht) hc.2))))
        simp only [List.mem_cons, List.mem_append] at hg
        rcases hg with rfl | hg | hg
        · exact comps_psi_mem_of hfu (Or.inl rfl)
        · exact comps_psi_mem_of hfu (Or.inr (Or.inl
            (compsAN_sh_fwdK hV hV' hVV huV n (isOT_arg ht) hg)))
        · have hd := compsAN_sh_fwdK hV hV' hVV huV n
            (isOT_sub_sfx (isOT_sub ht) V) hg
          obtain ⟨P, hP, _⟩ := add_eq_app_prefix V' (sh V V' (sub s V))
          have hidx : sh V V' g ∈ comps u (shf V V' s) := by
            unfold shf
            rw [hP, comps_app]
            exact List.mem_append.mpr (Or.inr hd)
          exact comps_psi_mem_of hfu (Or.inr (Or.inr (Or.inl hidx)))
      · rw [if_neg hc] at hg
        simp at hg
    · have hd := compsAN_sh_fwdK hV hV' hVV huV n (isOT_rest ht) hg
      rw [sh_psi_app, comps_app]
      exact List.mem_append.mpr (Or.inr hd)

/-- A moving component of `a − V` moves to a component of `f(a)`. -/
theorem compsAN_sub_shf {V V' u a d : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V') (huV : u ≤ V) (ha : isOT a = true)
    {m : Nat} (hd : d ∈ compsAN V u m (sub a V)) : sh V V' d ∈ comps u (shf V V' a) := by
  have hd' := compsAN_sh_fwdK hV hV' hVV huV m (isOT_sub_sfx ha V) hd
  obtain ⟨P, hP, _⟩ := add_eq_app_prefix V' (sh V V' (sub a V))
  unfold shf
  rw [hP, comps_app]
  exact List.mem_append.mpr (Or.inr hd')

/-- **The frame condition `KAG2`**: `KA` as in `KAG`; `KG` with the third alternative "below a moving component of
`a − V`". -/
def KAG2 (V V' a : T) (Lv : List T) (cv u : T) : Prop :=
  (∀ d ∈ comps u a, d ≤ psi (shf V V' a) z z ∨ ∃ d' ∈ comps u (shf V V' a), d ≤ d') ∧
    (∀ s y, cv = psi s y z → V < s → ∀ n, ∀ g ∈ compsAN V u n (sub s V),
      g ≤ psi s z z ∨ g ≤ spArg a z (sumN Lv) ∨ ∃ m, ∃ d ∈ compsAN V u m (sub a V), g ≤ d)

theorem kAG2_of_KAG {V V' a : T} {Lv : List T} {cv u : T} (h : KAG V V' a Lv cv u) : KAG2 V V' a Lv cv u :=
  ⟨h.1, fun s y hcv hVs n g hg => (h.2 s y hcv hVs n g hg).elim Or.inl (fun h => Or.inr (Or.inl h))⟩

def KVRA2 (V V' a : T) (Lv : List T) (cv u : T) : Prop := VDomF V V' a ∧ KAG2 V V' a Lv cv u

/-- **`QVRAt` moves with `σ` under `KVRA2`.** -/
theorem qVRAshK_KVRA2 : QVRAshK KVRA2 := by
  intro V V' a Lv cv u hV hV' hVV ha hVa hs hp hlev huV hK hQ
  obtain ⟨hVD, hKA, hKG⟩ := hK
  have hVV' : V ≤ V' := le_of_lt hVV
  have hLs : ∀ t ∈ Lv, Single t := fun t ht => hs t (List.mem_append_left _ ht)
  have hLp : Lv.Pairwise (fun a b => b ≤ a) := (List.pairwise_append.mp hp).1
  obtain ⟨hSot, hSsum⟩ := sumN_dec Lv hLs hLp
  have hlev' : V < a ∨ ∀ q ∈ summands (sumN Lv), lev q ≠ V := by
    rcases hlev with h | h
    · exact Or.inl h
    · right; rw [hSsum]; intro q hq; exact ne_of_gt (h q (List.mem_append_left _ hq))
  have hBot : isOT (spArg a z (sumN Lv)) = true := isOT_spArg a (sumN Lv) z rfl hSot
  have hB : spArg (shf V V' a) z (sumN (Lv.map (sh V V'))) = sh V V' (spArg a z (sumN Lv)) := by
    rw [← sh_sumN hV hV' hVV (fun t ht => (hLs t ht).1)]
    have hsp := sh_spArg hV hV' hVV ha hVa (b := z) rfl hSot hlev'
    rw [sh_z] at hsp
    exact hsp
  obtain ⟨hcvot, s, y, hcv⟩ := hs cv (by simp)
  subst hcv
  have hsot : isOT s = true := isOT_sub hcvot
  have hyot : isOT y = true := isOT_arg hcvot
  have hfa : isOT (shf V V' a) = true := isOT_shf hV hV' hVV ha
  have hua : ¬ a < u := not_lt.mpr (le_trans huV hVa)
  have hufa : ¬ shf V V' a < u := not_lt.mpr (le_trans (le_trans huV hVa) (le_shf_self hV hV' hVV' ha hVa))
  intro s' y' hcv' ht' hhi' _ g' hg'
  rw [hB] at ht' ⊢
  by_cases hVs : V < s
  · rw [sh_psi_gt hVs, sh_z] at hcv'
    simp only [psi.injEq] at hcv'
    obtain ⟨rfl, rfl, -⟩ := hcv'
    have hsy : isOT (psi s y z) = true := hcvot
    -- the premises of `P`
    have ht1 : lt (spArg a z (sumN Lv)) y = true :=
      (sh_lt_iff hV hV' hVV' hBot hyot).mp ht'.1
    have ht2 : lt (psi a z z) (psi s y z) = true := by
      by_cases hVa' : V < a
      · have e1 : sh V V' (psi a z z) = psi (shf V V' a) z z := by rw [sh_psi_gt hVa', sh_z]
        have e2 : sh V V' (psi s y z) = psi (shf V V' s) (sh V V' y) z := by rw [sh_psi_gt hVs, sh_z]
        have h2 : sh V V' (psi a z z) < sh V V' (psi s y z) := by rw [e1, e2]; exact ht'.2
        exact (sh_lt_iff hV hV' hVV' (isOT_psi_zz ha) hsy).mp h2
      · have hVa2 : a = V := by
          rcases (le_iff _ _).mp hVa with h | h
          · exact absurd h hVa'
          · exact h.symm
        show psi a z z < psi s y z
        rw [T.psi_lt_psi]; left; rw [hVa2]; exact hVs
    have hsplit := sh_split hV hV' hVV (sh_lt_om_succ hV hV' hVV hsot hVs) hyot
    have hhi : (split y (psi (succ s) z z)).1 ≠ z := by
      intro h; apply hhi'; rw [hsplit, h, sh_z]
    have hQ' := hQ s y rfl ⟨ht1, ht2⟩ hhi hua
    -- `a ≤ s`, `Ω_{f a} ≤ Ω_{f s}`, `Ω_s ≤ Ω_{f s}`
    have has : a ≤ s := by
      have h2 : psi a z z < psi s y z := ht2
      rw [T.psi_lt_psi] at h2
      rcases h2 with h | ⟨h, _⟩ | ⟨h, _⟩
      · exact le_of_lt h
      · rw [h]
      · rw [h]
    have hVs' : V ≤ s := le_of_lt hVs
    have hOmA : psi (shf V V' a) z z ≤ psi (shf V V' s) z z := by
      rcases (le_iff _ _).mp has with h | h
      · exact psi_le_psi_of (Or.inl (shf_lt_shf hV hV' hVV' ha hsot hVa h))
      · rw [h]
    have hOmS : psi s z z ≤ psi (shf V V' s) z z := by
      rcases (le_iff _ _).mp (le_shf_self hV hV' hVV' hsot hVs') with h | h
      · exact psi_le_psi_of (Or.inl h)
      · rw [← h]
    have hshOm : sh V V' (psi s z z) = psi (shf V V' s) z z := by rw [sh_psi_gt hVs, sh_z]
    -- the components of `V′`
    have hVpart : g' ∈ comps u V' → g' ≤ psi (shf V V' s) z z ∨
        g' ≤ sh V V' (spArg a z (sumN Lv)) ∨ ∃ d ∈ comps u (shf V V' a), g' ≤ d := by
      intro h
      rcases hVD u hufa g' h with h1 | h1
      · exact Or.inl (le_trans h1 hOmA)
      · exact Or.inr (Or.inr h1)
    unfold shf at hg'
    obtain ⟨P, hP, hPs⟩ := add_eq_app_prefix V' (sh V V' (sub s V))
    rw [hP, comps_app] at hg'
    rcases List.mem_append.mp hg' with hg | hg
    · obtain ⟨q, hq, hgq⟩ := comps_to_summand hg
      exact hVpart (comps_of_mem_summands (hPs q hq) hgq)
    · rcases comps_sh_levA V V' huV (size (sub s V)) (sub s V) g' (Nat.le_refl _) hg with
        ⟨g, hgA, e⟩ | ⟨g, hgB, e⟩ | ⟨q, hq, hgq⟩
      · rw [e]
        have hgs := comps_sub_sub u s V (compsAN_sub V u _ hgA)
        have hgot : isOT g = true := isOT_of_mem_comps u hsot hgs
        rcases hKG s y rfl hVs _ g hgA with h | h | ⟨m, d, hd, h⟩
        · left
          have := sh_le_sh hV hV' hVV' hgot (isOT_psi_zz hsot) h
          rwa [hshOm] at this
        · right; left
          exact sh_le_sh hV hV' hVV' hgot hBot h
        · right; right
          have hdot : isOT d = true :=
            isOT_of_mem_comps u (isOT_sub_sfx ha V) (compsAN_sub V u m hd)
          exact ⟨sh V V' d, compsAN_sub_shf hV hV' hVV huV ha hd, sh_le_sh hV hV' hVV' hgot hdot h⟩
      · rw [e]
        have hgs := comps_sub_sub u s V hgB
        rcases hQ' g hgs with h | h | ⟨d, hd, h⟩
        · exact Or.inl (le_trans h hOmS)
        · exact Or.inr (Or.inl (le_trans h (le_sh hV hV' hVV' hBot)))
        · rcases hKA d hd with hdd | ⟨d', hd', hdd⟩
          · exact Or.inl (le_trans h (le_trans hdd hOmA))
          · exact Or.inr (Or.inr ⟨d', hd', le_trans h hdd⟩)
      · exact hVpart (comps_of_mem_summands hq hgq)
  · exfalso
    rw [sh_psi_le hVs, sh_z] at hcv'
    simp only [psi.injEq] at hcv'
    obtain ⟨rfl, rfl, -⟩ := hcv'
    have h2 : psi (shf V V' a) z z < psi s y z := ht'.2
    rw [T.psi_lt_psi] at h2
    have hfs : shf V V' a ≤ s := by
      rcases h2 with h | ⟨h, _⟩ | ⟨h, _⟩
      · exact le_of_lt h
      · rw [h]
      · rw [h]
    have : V' ≤ V := le_trans (le_shf hV hV' hVV' ha hVa) (le_trans hfs (le_of_not_gt hVs))
    exact absurd hVV (not_lt.mpr this)

/-- **The residual `T2VRAK KVRA2`** from t0's shared `T2CopyK CopyVDomK` and `KAG2`. -/
theorem t2VRAK_KVRA2_of {M : Mat} (hVD : T2CopyK CopyVDomK M) (hAG : T2VRAK KAG2 M) : T2VRAK KVRA2 M :=
  fun r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL u hu huV =>
    ⟨hVD r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL,
      hAG r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL u hu huV⟩

#print axioms qVRAshK_KVRA2

end Ytosk
