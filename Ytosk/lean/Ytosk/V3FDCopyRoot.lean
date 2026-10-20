import Ytosk.V3FDCopy

namespace Ytosk.FDCopyRoot
open T FDCopy
set_option linter.unusedVariables false

theorem frameDom_retained_root {V V' a B s y u g C : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a) (hB : isOT B = true)
    (hc : isOT (psi s y z) = true) (hVs : V < s)
    (ht : psi a z z < psi s y z) (hu : u ≤ V)
    (hKA : ∀ d ∈ comps u a, d ≤ psi (shf V V' a) z z ∨ ∃ e ∈ comps u (shf V V' a), d ≤ e)
    (hRoot : ∀ d ∈ comps u V, d ≤ psi (shf V V' a) z z ∨ ∃ e ∈ comps u (shf V V' a), d ≤ e)
    (hFD : FrameDom a B s (H s y))
    (hg : g ∈ comps u B ∨ g ∈ comps u s)
    (hBC : sh V V' B < C) (hSC : psi (shf V V' s) z z < C)
    (hCX : C ≤ H (shf V V' s) (sh V V' y)) :
    ∃ d ∈ C :: (comps u C ++ comps u (shf V V' a)), g ≤ d := by
  have hs := isOT_sub hc
  have has : a ≤ s := by simpa only [lev] using lev_le_of_le (le_of_lt ht)
  have haf := ClShLGuarded.shf_le_right hV hV' hVV ha hVa has
  have hOm : psi (shf V V' a) z z ≤ psi (shf V V' s) z z := psi_le_psi_z haf
  by_cases hParent : ∃ d ∈ comps u a, g ≤ d
  · obtain ⟨d, hd, hgd⟩ := hParent
    rcases hKA d hd with h | ⟨d', hd', hdd'⟩
    · exact ⟨C, List.mem_cons_self, le_trans hgd (le_trans h (le_trans hOm (le_of_lt hSC)))⟩
    · exact ⟨d', List.mem_cons_of_mem _ (List.mem_append_right _ hd'), le_trans hgd hdd'⟩
  · let M : T := if B < psi s z z then psi s z z else B
    have hM : isOT M = true := by
      dsimp [M]
      split
      · exact isOT_psi_zz hs
      · exact hB
    have hBM : B ≤ M := by
      dsimp [M]
      split
      · exact le_of_lt ‹B < psi s z z›
      · exact le_refl _
    have hSM : psi s z z ≤ M := by
      dsimp [M]
      split
      · exact le_refl _
      · exact not_lt.mp ‹¬ B < psi s z z›
    have hM' : sh V V' M < C := by
      dsimp [M]
      split
      · simpa only [sh_psi_gt hVs, sh_z] using hSC
      · exact hBC
    have hP : PersistentArg u g M (H s y) := by
      intro c hMc hcX
      obtain ⟨d, hd, hgd⟩ := hFD u (not_lt.mpr (le_trans hu hVa)) c
        (lt_of_le_of_lt hBM hMc) (lt_of_le_of_lt hSM hMc) hcX g hg
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨d, List.mem_cons_self, hgd⟩
      · rcases List.mem_append.mp hd with hd | hd
        · exact ⟨d, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd), hgd⟩
        · exact False.elim (hParent ⟨d, hd, hgd⟩)
    rcases persistentArg_sh_low hV hV' hVV hu hM
        (isOT_arg (ClShLGuarded.isOT_H_self hc)) hP with h | hP'
    · obtain ⟨e, he, hge⟩ := h
      rcases hRoot e he with he | ⟨d, hd, hed⟩
      · exact ⟨C, List.mem_cons_self, le_trans hge (le_trans he (le_trans hOm (le_of_lt hSC)))⟩
      · exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_right _ hd), le_trans hge hed⟩
    · have hCX' : C ≤ sh V V' (H s y) := by rwa [sh_H hV hV' hVV hc hVs]
      obtain ⟨d, hd, hgd⟩ := hP' C hM' hCX'
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨d, List.mem_cons_self, hgd⟩
      · rcases List.mem_cons.mp hd with rfl | hd
        · exact ⟨C, List.mem_cons_self, le_trans hgd (z_le _)⟩
        · exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_left _ hd), hgd⟩

theorem frameDom_sh_root {V V' a B s y : T} {Lv : List T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a) (hc : isOT (psi s y z) = true)
    (hBeq : B = spArg a z (sumN Lv)) (hFO : isOT (psi a B z) = true)
    (hVs : V < s) (ht : psi a z z < psi s y z)
    (hVD : VDomF V V' a)
    (hRoot : ∀ u, u ≤ V → ∀ d ∈ comps u V,
      d ≤ psi (shf V V' a) z z ∨ ∃ e ∈ comps u (shf V V' a), d ≤ e)
    (hKG : a = V → ∀ n d, d ∈ compsAN V V n (sub s V) →
      d ≤ psi s z z ∨ d ≤ B)
    (hFD : FrameDom a B s (H s y)) :
    FrameDom (shf V V' a) (sh V V' B) (shf V V' s)
      (H (shf V V' s) (sh V V' y)) := by
  have hs := isOT_sub hc
  have hB := isOT_arg hFO
  have hsfx := isOT_sub_sfx hs V
  have has : a ≤ s := by simpa only [lev] using lev_le_of_le (le_of_lt ht)
  have hOm : psi (shf V V' a) z z ≤ psi (shf V V' s) z z :=
    psi_le_psi_z (ClShLGuarded.shf_le_right hV hV' hVV ha hVa has)
  have hshOm : sh V V' (psi s z z) = psi (shf V V' s) z z := by
    rw [sh_psi_gt hVs, sh_z]
  intro u hu C hBC hSC hCX g hg
  have hua : u ≤ shf V V' a := not_lt.mp hu
  have smallB : ∀ d, d ≤ sh V V' B →
      ∃ e ∈ C :: (comps u C ++ comps u (shf V V' a)), d ≤ e :=
    fun d hd => ⟨C, List.mem_cons_self, le_trans hd (le_of_lt hBC)⟩
  have smallS : ∀ d, d ≤ psi (shf V V' s) z z →
      ∃ e ∈ C :: (comps u C ++ comps u (shf V V' a)), d ≤ e :=
    fun d hd => ⟨C, List.mem_cons_self, le_trans hd (le_of_lt hSC)⟩
  have introduced : ∀ d ∈ comps u V',
      ∃ e ∈ C :: (comps u C ++ comps u (shf V V' a)), d ≤ e := by
    intro d hd
    rcases hVD u hu d hd with h | ⟨e, he, hde⟩
    · exact smallS d (le_trans h hOm)
    · exact ⟨e, List.mem_cons_of_mem _ (List.mem_append_right _ he), hde⟩
  have matched : ∀ w d, isOT w = true → V < w → w ≤ a → u ≤ shf V V' w →
      (d ∈ comps w B ∨ d ∈ comps w s) →
      ∃ e ∈ C :: (comps u C ++ comps u (shf V V' a)), sh V V' d ≤ e := by
    intro w d hw hVw hwa huw hd
    exact frameDom_copy_high_component hV hV' hVV ha hB hc hVs hw hVw hwa huw hFD hd hBC hSC hCX
  have hKA : ∀ w, w ≤ V → ∀ d ∈ comps w a,
      d ≤ psi (shf V V' a) z z ∨ ∃ e ∈ comps w (shf V V' a), d ≤ e := by
    intro w hw d hd
    rcases index_component_forward_or_old_root hV hV' hVV ha hVa hd with
        ⟨e, he, hde⟩ | ⟨e, he, hde⟩
    · rcases hRoot w hw e he with he | ⟨f, hf, hef⟩
      · exact Or.inl (le_trans hde he)
      · exact Or.inr ⟨f, hf, le_trans hde hef⟩
    · exact Or.inr ⟨e, he, hde⟩
  have kgImage : ∀ w, w ≤ V → (u ≤ V ∨ a = V) → ∀ n d, d ∈ compsAN V w n (sub s V) →
      ∃ e ∈ C :: (comps u C ++ comps u (shf V V' a)), sh V V' d ≤ e := by
    intro w hw hsmall n d hd
    by_cases haV : a = V
    · have hdV : d ∈ compsAN V V n (sub s V) := by
        rw [← ClShLGuarded.compsAN_level_eq
          (le_trans hw (le_of_lt (lt_succ_self V))) (le_of_lt (lt_succ_self V)) n (sub s V)]
        exact hd
      have hdo := isOT_of_mem_comps w hsfx (compsAN_sub V w n hd)
      rcases hKG haV n d hdV with h | h
      · apply smallS
        rw [← hshOm]
        exact sh_le_sh hV hV' (le_of_lt hVV) hdo (isOT_psi_zz hs) h
      · exact smallB _ (sh_le_sh hV hV' (le_of_lt hVV) hdo hB h)
    · have hVa' : V < a := lt_of_le_of_ne hVa (Ne.symm haV)
      have huV : u ≤ V := hsmall.resolve_right haV
      have hd' : d ∈ comps (succ V) s := by
        apply comps_sub_sub (succ V) s V
        apply compsAN_sub V (succ V) n
        rw [← ClShLGuarded.compsAN_level_eq
          (le_trans hw (le_of_lt (lt_succ_self V))) (le_refl (succ V)) n (sub s V)]
        exact hd
      exact matched (succ V) d (isOT_succ hV) (lt_succ_self V) (succ_le_of_lt hVa')
        (le_trans huV (le_trans (le_of_lt (lt_succ_self V))
          (le_shf_self hV hV' (le_of_lt hVV) (isOT_succ hV) (le_of_lt (lt_succ_self V)))))
        (Or.inr hd')
  by_cases hVu : V < u
  · rcases hg with hg | hg
    · rcases (le_iff _ _).mp hVa with hVa | hVa
      · rcases ClShLGuarded.component_raise_to_matched hV hV' hVV hVu (size B)
            (le_refl _) hB ha hVa hua hg with ⟨w, hw, hVw, hwa, huw, hgw⟩ | hg
        · obtain ⟨d, hd, rfl⟩ := comps_sh hV hV' hVV hw (le_of_lt hVw) hB g hgw
          exact matched w d hw hVw hwa huw (Or.inl hd)
        · exact introduced g hg
      · subst a
        rcases ClShLGuarded.components_above_cut V V' hVu (size B) (le_refl _) hg with
            ⟨d, hd, rfl⟩ | hg
        · have hdV := comps_mono (le_of_lt (lt_succ_self V)) hd
          exact smallB _ (le_of_lt (sh_lt_sh hV hV' (le_of_lt hVV)
            (isOT_of_mem_comps V hB hdV) hB (comps_lt hFO d hdV)))
        · exact introduced g hg
    · unfold shf at hg
      rcases comps_add u V' (sh V V' (sub s V)) g hg with hg | hg
      · exact introduced g hg
      · rcases (le_iff _ _).mp hVa with hVa | hVa
        · rcases ClShLGuarded.component_raise_to_matched hV hV' hVV hVu (size (sub s V))
              (le_refl _) hsfx ha hVa hua hg with ⟨w, hw, hVw, hwa, huw, hgw⟩ | hg
          · obtain ⟨d, hd, rfl⟩ := comps_sh hV hV' hVV hw (le_of_lt hVw) hsfx g hgw
            exact matched w d hw hVw hwa huw (Or.inr (comps_sub_sub w s V hd))
          · exact introduced g hg
        · subst a
          rcases ClShLGuarded.components_above_cut V V' hVu (size (sub s V)) (le_refl _) hg with
              ⟨d, hd, rfl⟩ | hg
          · exact kgImage V (le_refl _) (Or.inr rfl) (size (sub s V)) d
              (comps_above_mem_AN hV _ _ (le_refl _) d hd)
          · exact introduced g hg
  · have huV : u ≤ V := not_lt.mp hVu
    have retained : ∀ d, (d ∈ comps u B ∨ d ∈ comps u s) →
        ∃ e ∈ C :: (comps u C ++ comps u (shf V V' a)), d ≤ e := by
      intro d hd
      exact frameDom_retained_root hV hV' hVV ha hVa hB hc hVs ht huV
        (hKA u huV) (hRoot u huV) hFD hd hBC hSC hCX
    rcases hg with hg | hg
    · rcases comps_sh_levA V V' huV (size B) B g (le_refl _) hg with
          ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ | ⟨q, hq, hgq⟩
      · rcases (le_iff _ _).mp hVa with hVa | hVa
        · have hd' : d ∈ comps (succ V) B := by
            apply compsAN_sub V (succ V) (size B)
            rw [← ClShLGuarded.compsAN_level_eq
              (le_trans huV (le_of_lt (lt_succ_self V))) (le_refl (succ V)) (size B) B]
            exact hd
          exact matched (succ V) d (isOT_succ hV) (lt_succ_self V) (succ_le_of_lt hVa)
            (le_trans huV (le_trans (le_of_lt (lt_succ_self V))
              (le_shf_self hV hV' (le_of_lt hVV) (isOT_succ hV) (le_of_lt (lt_succ_self V)))))
            (Or.inl hd')
        · subst a
          exact smallB _ (le_of_lt (ClShLGuarded.moving_root_bound_of_frameOT
            hV hV' hVV hFO huV hd))
      · exact retained g (Or.inl hd)
      · exact introduced g (comps_of_mem_summands hq hgq)
    · unfold shf at hg
      rcases comps_add u V' (sh V V' (sub s V)) g hg with hg | hg
      · exact introduced g hg
      · rcases comps_sh_levA V V' huV (size (sub s V)) (sub s V) g (le_refl _) hg with
            ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ | ⟨q, hq, hgq⟩
        · exact kgImage u huV (Or.inl huV) (size (sub s V)) d hd
        · exact retained g (Or.inr (comps_sub_sub u s V hd))
        · exact introduced g (comps_of_mem_summands hq hgq)

#print axioms frameDom_sh_root
end Ytosk.FDCopyRoot
