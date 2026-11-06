/-
**t = 2: the copy-frame condition `KVRA3` (2026-11-06).**

`KVRA2 = VDomF ∧ KAG2`.  `qVRAshK_KVRA2` reads `VDomF V V′ a` only at the level `u ≤ V` of the frame and only to bound the
components of `V′` in `f(s)` by the transported `QVRAt`, whose second alternative (the shifted state `σ B`) `VDomF` does
not use.  `VDomU` is `VDomF` at the level `u` with that alternative; `KVRA3 = VDomU ∧ KAG2` is weaker than `KVRA2`.
-/
import Ytosk.V3T2VRAK2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The components of `V′` at the level `u` of a copy frame**: below `Ω_{f(a)}`, the shifted state, or a component
of `f(a)`. -/
def VDomU (V V' a : T) (Lv : List T) (u : T) : Prop :=
  ∀ g ∈ comps u V', g ≤ psi (shf V V' a) z z ∨ g ≤ sh V V' (spArg a z (sumN Lv)) ∨
    ∃ d ∈ comps u (shf V V' a), g ≤ d

def KVRA3 (V V' a : T) (Lv : List T) (cv u : T) : Prop := VDomU V V' a Lv u ∧ KAG2 V V' a Lv cv u

theorem vDomU_of_VDomF {V V' a : T} {Lv : List T} {u : T} (h : VDomF V V' a) (hu : ¬ shf V V' a < u) :
    VDomU V V' a Lv u := fun g hg => (h u hu g hg).elim Or.inl (fun h => Or.inr (Or.inr h))

/-- **`QVRAt` moves with `σ` under `KVRA3`.** -/
theorem qVRAshK_KVRA3 : QVRAshK KVRA3 := by
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
  intro s' y' hcv' ht' hhi' _ g' hg'
  rw [hB] at ht' ⊢
  by_cases hVs : V < s
  · rw [sh_psi_gt hVs, sh_z] at hcv'
    simp only [psi.injEq] at hcv'
    obtain ⟨rfl, rfl, -⟩ := hcv'
    have hsy : isOT (psi s y z) = true := hcvot
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
      rcases hVD g' h with h1 | h1 | h1
      · exact Or.inl (le_trans h1 hOmA)
      · exact Or.inr (Or.inl h1)
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

/-- `T2VRAK KVRA3` from the residuals of `KVRA3`. -/
theorem t2VRAK_KVRA3_of {M : Mat} (hVD : T2VRAK (fun V V' a Lv _ u => VDomU V V' a Lv u) M) (hAG : T2VRAK KAG2 M) :
    T2VRAK KVRA3 M :=
  fun r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL u hu huV =>
    ⟨hVD r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL u hu huV,
      hAG r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL u hu huV⟩

#print axioms qVRAshK_KVRA3

end Ytosk
