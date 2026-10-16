/-
**G3 の切り口と FrameDom（2026-10-17、t2）。**

状態 B が H の G3 の切り口（`cutsNSG s H`、PH3cG の第 3 の種類）のとき、B < C ≤ H のどの C でも、
B の成分は z か s の成分か、C の成分で押さえられる（`cutsNS_dom`）。切り口は H の道に沿って部分項を Ω_s に
替えて後ろを落としたもので、B と H の間の C は同じ道を持つ（道の上の頭・引数・添字は C の成分）。
PH3cG の 3 つの種類（hi = B、hi = B + R、切り口）のどれでも、B の成分の分は FrameDom を満たす
（`frameDom_of_kind`）。添字 s の成分は別の仮定。
-/
import Ytosk.V3T2SeedFr

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- The conclusion for one component: `0`, a component of `s`, or below a component of `C`. -/
def CutDom (s u C g : T) : Prop := g = z ∨ g ∈ comps u s ∨ ∃ d ∈ comps u C, g ≤ d

theorem mem_comps_rest {u w e f g : T} (h : g ∈ comps u f) : g ∈ comps u (psi w e f) := by
  simp only [comps, List.mem_append]; exact Or.inr h

theorem mem_comps_head {u w e f g : T} (hw : ¬ lt w u = true) (h : g = e ∨ g ∈ comps u e ∨ g ∈ comps u w) :
    g ∈ comps u (psi w e f) := by
  simp only [comps, if_neg hw, List.mem_append, List.mem_cons]
  rcases h with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr h))

theorem comps_psi_cases {u w e f g : T} (h : g ∈ comps u (psi w e f)) :
    (¬ lt w u = true ∧ (g = e ∨ g ∈ comps u e ∨ g ∈ comps u w)) ∨ g ∈ comps u f := by
  simp only [comps, List.mem_append] at h
  rcases h with h | h
  · by_cases hw : lt w u = true
    · rw [if_pos hw] at h; simp at h
    · rw [if_neg hw] at h
      simp only [List.mem_cons, List.mem_append] at h
      exact Or.inl ⟨hw, h⟩
  · exact Or.inr h

/-- The components of `Ω_s`. -/
theorem comps_om {s u g : T} (h : g ∈ comps u (psi s z z)) : g = z ∨ g ∈ comps u s := by
  rcases comps_psi_cases h with ⟨_, h | h | h⟩ | h
  · exact Or.inl h
  · simp [comps] at h
  · exact Or.inr h
  · simp [comps] at h

theorem cutDom_mono {s u C C' g : T} (hsub : ∀ d ∈ comps u C', d ∈ comps u C) (h : CutDom s u C' g) :
    CutDom s u C g := by
  rcases h with h | h | ⟨d, hd, hgd⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨d, hsub d hd, hgd⟩)

/-- **The components of a G3 cut of a term** (the head position). -/
theorem cutsH_dom {s u : T} : ∀ (Y : T) {t C : T}, t ∈ cutsHG s Y → t < C → C ≤ Y →
    ∀ g ∈ comps u t, CutDom s u C g
  | z, _, _, ht, _, _ => by simp [cutsHG] at ht
  | psi a x c, t, C, ht, htC, hCY => by
    intro g hg
    cases C with
    | z => exact absurd htC (T.not_lt_z _)
    | psi w e f =>
    have hCY' : psi w e f < psi a x c ∨ psi w e f = psi a x c := hCY
    simp only [cutsHG, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨t', ht', rfl⟩ | ht
    · -- a cut in the subscript: `t = Ω_{t′}`
      have hwa : w ≤ a := by
        rcases hCY' with h | h
        · rcases T.psi_lt_psi.mp h with h | ⟨h, _⟩ | ⟨h, _, _⟩
          · exact le_of_lt h
          · rw [h]
          · rw [h]
        · simp only [psi.injEq] at h; rw [h.1]
      have htw : t' < w ∨ t' = w := by
        rcases T.psi_lt_psi.mp htC with h | ⟨h, _⟩ | ⟨h, _, _⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inr h
      rcases comps_psi_cases hg with ⟨hu, h | h | h⟩ | h
      · exact Or.inl h
      · simp [comps] at h
      · rcases htw with htw | htw
        · have hw : ¬ lt w u = true := fun h' => hu (T.lt_trans' htw h')
          exact cutDom_mono (fun d hd => mem_comps_head hw (Or.inr (Or.inr hd)))
            (cutsH_dom a ht' htw hwa g h)
        · subst htw
          exact Or.inr (Or.inr ⟨g, mem_comps_head hu (Or.inr (Or.inr h)), le_refl _⟩)
      · simp [comps] at h
    · split at ht
      · rename_i hsa
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at ht
        rcases ht with (rfl | ⟨t'', ht'', rfl⟩) | ⟨t''', ht''', rfl⟩
        · -- the cut `Ω_s`
          rcases comps_om hg with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · -- a cut in the argument: `t = ψ_a(t″)`
          have hwa : w = a := by
            rcases hCY' with h | h
            · rcases T.psi_lt_psi.mp htC with h' | ⟨h', _⟩ | ⟨h', _, _⟩
              · rcases T.psi_lt_psi.mp h with h2 | ⟨h2, _⟩ | ⟨h2, _, _⟩
                · exact absurd (T.lt_trans' h' h2) (lt_irrefl' _)
                · exact absurd (h2 ▸ h') (lt_irrefl' _)
                · exact absurd (h2 ▸ h') (lt_irrefl' _)
              · exact h'.symm
              · exact h'.symm
            · simp only [psi.injEq] at h; exact h.1
          subst hwa
          have hex : t'' < e ∨ t'' = e := by
            rcases T.psi_lt_psi.mp htC with h | ⟨_, h⟩ | ⟨_, h, _⟩
            · exact absurd h (lt_irrefl' _)
            · exact Or.inl h
            · exact Or.inr h
          have hex' : e ≤ x := by
            rcases hCY' with h | h
            · rcases T.psi_lt_psi.mp h with h | ⟨_, h⟩ | ⟨_, h, _⟩
              · exact absurd h (lt_irrefl' _)
              · exact le_of_lt h
              · rw [h]
            · simp only [psi.injEq] at h; rw [h.2.1]
          rcases comps_psi_cases hg with ⟨hu, h | h | h⟩ | h
          · subst h
            refine Or.inr (Or.inr ⟨e, mem_comps_head hu (Or.inl rfl), ?_⟩)
            rcases hex with h | h
            · exact le_of_lt h
            · rw [h]
          · rcases hex with hex | hex
            · exact cutDom_mono (fun d hd => mem_comps_head hu (Or.inr (Or.inl hd)))
                (cutsH_dom x ht'' hex hex' g h)
            · subst hex
              exact Or.inr (Or.inr ⟨g, mem_comps_head hu (Or.inr (Or.inl h)), le_refl _⟩)
          · exact Or.inr (Or.inr ⟨g, mem_comps_head hu (Or.inr (Or.inr h)), le_refl _⟩)
          · simp [comps] at h
        · -- a cut in the rest: `t = ψ_a(x) + t‴`
          have hwe : w = a ∧ e = x := by
            rcases hCY' with h | h
            · rcases T.psi_lt_psi.mp htC with h' | ⟨h', h''⟩ | ⟨h', h'', _⟩
              · rcases T.psi_lt_psi.mp h with h2 | ⟨h2, _⟩ | ⟨h2, _, _⟩
                · exact absurd (T.lt_trans' h' h2) (lt_irrefl' _)
                · exact absurd (h2 ▸ h') (lt_irrefl' _)
                · exact absurd (h2 ▸ h') (lt_irrefl' _)
              · subst h'
                rcases T.psi_lt_psi.mp h with h2 | ⟨_, h2⟩ | ⟨_, h2, _⟩
                · exact absurd h2 (lt_irrefl' _)
                · exact absurd (T.lt_trans' h'' h2) (lt_irrefl' _)
                · exact absurd (h2 ▸ h'') (lt_irrefl' _)
              · exact ⟨h'.symm, h''.symm⟩
            · simp only [psi.injEq] at h; exact ⟨h.1, h.2.1⟩
          obtain ⟨rfl, rfl⟩ := hwe
          have htf : t''' < f := by
            rcases T.psi_lt_psi.mp htC with h | ⟨_, h⟩ | ⟨_, _, h⟩
            · exact absurd h (lt_irrefl' _)
            · exact absurd h (lt_irrefl' _)
            · exact h
          have hfc : f ≤ c := by
            rcases hCY' with h | h
            · rcases T.psi_lt_psi.mp h with h | ⟨_, h⟩ | ⟨_, _, h⟩
              · exact absurd h (lt_irrefl' _)
              · exact absurd h (lt_irrefl' _)
              · exact le_of_lt h
            · simp only [psi.injEq] at h; rw [h.2.2]
          rcases comps_psi_cases hg with ⟨hu, hh⟩ | h
          · exact Or.inr (Or.inr ⟨g, mem_comps_head hu hh, le_refl _⟩)
          · exact cutDom_mono (fun d hd => mem_comps_rest hd) (cutsH_dom c ht''' htf hfc g h)
      · simp at ht

/-- **The components of a G3 cut at the level of the state** (`cutsNSG`). -/
theorem cutsNS_dom {s u : T} : ∀ (Y : T) {t C : T}, t ∈ cutsNSG s Y → t < C → C ≤ Y →
    ∀ g ∈ comps u t, CutDom s u C g
  | z, _, _, ht, _, _ => by simp [cutsNSG] at ht
  | psi a x c, t, C, ht, htC, hCY => by
    intro g hg
    cases C with
    | z => exact absurd htC (T.not_lt_z _)
    | psi w e f =>
    have hCY' : psi w e f < psi a x c ∨ psi w e f = psi a x c := hCY
    simp only [cutsNSG, List.mem_append, List.mem_map] at ht
    rcases ht with (⟨t', ht', rfl⟩ | ⟨t2, ht2, rfl⟩) | ⟨t3, ht3, rfl⟩
    · -- a cut in the subscript
      have hwa : w ≤ a := by
        rcases hCY' with h | h
        · rcases T.psi_lt_psi.mp h with h | ⟨h, _⟩ | ⟨h, _, _⟩
          · exact le_of_lt h
          · rw [h]
          · rw [h]
        · simp only [psi.injEq] at h; rw [h.1]
      have htw : t' < w ∨ t' = w := by
        rcases T.psi_lt_psi.mp htC with h | ⟨h, _⟩ | ⟨h, _, _⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inr h
      rcases comps_psi_cases hg with ⟨hu, h | h | h⟩ | h
      · exact Or.inl h
      · simp [comps] at h
      · rcases htw with htw | htw
        · have hw : ¬ lt w u = true := fun h' => hu (T.lt_trans' htw h')
          exact cutDom_mono (fun d hd => mem_comps_head hw (Or.inr (Or.inr hd)))
            (cutsH_dom a ht' htw hwa g h)
        · subst htw
          exact Or.inr (Or.inr ⟨g, mem_comps_head hu (Or.inr (Or.inr h)), le_refl _⟩)
      · simp [comps] at h
    · -- a cut in the argument
      have hwa : w = a := by
        rcases hCY' with h | h
        · rcases T.psi_lt_psi.mp htC with h' | ⟨h', _⟩ | ⟨h', _, _⟩
          · rcases T.psi_lt_psi.mp h with h2 | ⟨h2, _⟩ | ⟨h2, _, _⟩
            · exact absurd (T.lt_trans' h' h2) (lt_irrefl' _)
            · exact absurd (h2 ▸ h') (lt_irrefl' _)
            · exact absurd (h2 ▸ h') (lt_irrefl' _)
          · exact h'.symm
          · exact h'.symm
        · simp only [psi.injEq] at h; exact h.1
      subst hwa
      have hex : t2 < e ∨ t2 = e := by
        rcases T.psi_lt_psi.mp htC with h | ⟨_, h⟩ | ⟨_, h, _⟩
        · exact absurd h (lt_irrefl' _)
        · exact Or.inl h
        · exact Or.inr h
      have hex' : e ≤ x := by
        rcases hCY' with h | h
        · rcases T.psi_lt_psi.mp h with h | ⟨_, h⟩ | ⟨_, h, _⟩
          · exact absurd h (lt_irrefl' _)
          · exact le_of_lt h
          · rw [h]
        · simp only [psi.injEq] at h; rw [h.2.1]
      rcases comps_psi_cases hg with ⟨hu, h | h | h⟩ | h
      · subst h
        refine Or.inr (Or.inr ⟨e, mem_comps_head hu (Or.inl rfl), ?_⟩)
        rcases hex with h | h
        · exact le_of_lt h
        · rw [h]
      · rcases hex with hex | hex
        · exact cutDom_mono (fun d hd => mem_comps_head hu (Or.inr (Or.inl hd)))
            (cutsH_dom x ht2 hex hex' g h)
        · subst hex
          exact Or.inr (Or.inr ⟨g, mem_comps_head hu (Or.inr (Or.inl h)), le_refl _⟩)
      · exact Or.inr (Or.inr ⟨g, mem_comps_head hu (Or.inr (Or.inr h)), le_refl _⟩)
      · simp [comps] at h
    · -- a cut in the rest
      have hwe : w = a ∧ e = x := by
        rcases hCY' with h | h
        · rcases T.psi_lt_psi.mp htC with h' | ⟨h', h''⟩ | ⟨h', h'', _⟩
          · rcases T.psi_lt_psi.mp h with h2 | ⟨h2, _⟩ | ⟨h2, _, _⟩
            · exact absurd (T.lt_trans' h' h2) (lt_irrefl' _)
            · exact absurd (h2 ▸ h') (lt_irrefl' _)
            · exact absurd (h2 ▸ h') (lt_irrefl' _)
          · subst h'
            rcases T.psi_lt_psi.mp h with h2 | ⟨_, h2⟩ | ⟨_, h2, _⟩
            · exact absurd h2 (lt_irrefl' _)
            · exact absurd (T.lt_trans' h'' h2) (lt_irrefl' _)
            · exact absurd (h2 ▸ h'') (lt_irrefl' _)
          · exact ⟨h'.symm, h''.symm⟩
        · simp only [psi.injEq] at h; exact ⟨h.1, h.2.1⟩
      obtain ⟨rfl, rfl⟩ := hwe
      have htf : t3 < f := by
        rcases T.psi_lt_psi.mp htC with h | ⟨_, h⟩ | ⟨_, _, h⟩
        · exact absurd h (lt_irrefl' _)
        · exact absurd h (lt_irrefl' _)
        · exact h
      have hfc : f ≤ c := by
        rcases hCY' with h | h
        · rcases T.psi_lt_psi.mp h with h | ⟨_, h⟩ | ⟨_, _, h⟩
          · exact absurd h (lt_irrefl' _)
          · exact absurd h (lt_irrefl' _)
          · exact le_of_lt h
        · simp only [psi.injEq] at h; rw [h.2.2]
      rcases comps_psi_cases hg with ⟨hu, hh⟩ | h
      · exact Or.inr (Or.inr ⟨g, mem_comps_head hu hh, le_refl _⟩)
      · exact cutDom_mono (fun d hd => mem_comps_rest hd) (cutsNS_dom c ht3 htf hfc g h)

/-- **FrameDom from the kind of the frame** (PH3cG): the components of `B` are taken care of by the kind;
the components of `s` by the hypothesis `hs`. -/
theorem frameDom_of_kind {a B s y : T} (hot : isOT (psi s y z) = true)
    (hK : PH3cKindG B (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s)
    (hs : ∀ u, ¬ lt a u = true → ∀ g ∈ comps u s, g = z ∨ g ≤ B ∨ g ≤ psi s z z ∨ ∃ d ∈ comps u a, g ≤ d) :
    FrameDom a B s (H s y) := by
  rw [H_eq hot]
  rcases hK with ⟨hhi, _⟩ | ⟨hne, ⟨R, _, hR⟩ | ⟨_, hc⟩⟩
  · rw [hhi]; exact frameDom_prefix hs
  · rw [hR, app_assoc]; exact frameDom_prefix hs
  · intro u hu C hBC hOC hCX g hg
    have hsdom : ∀ g ∈ comps u s, ∃ d ∈ C :: (comps u C ++ comps u a), g ≤ d := by
      intro g' hg'
      rcases hs u hu g' hg' with h | h | h | ⟨d, hd, hgd⟩
      · subst h; exact ⟨C, List.mem_cons_self .., z_le _⟩
      · exact ⟨C, List.mem_cons_self .., le_trans h (le_of_lt hBC)⟩
      · exact ⟨C, List.mem_cons_self .., le_trans h (le_of_lt hOC)⟩
      · exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_right _ hd), hgd⟩
    rcases hg with hg | hg
    · have hD : CutDom s u C g ∨ ((∃ c0, C = app (split y (psi (succ s) z z)).1 c0) ∧
          CutDom s u (split y (psi (succ s) z z)).1 g) := by
        by_cases hCh : C ≤ (split y (psi (succ s) z z)).1
        · exact Or.inl (cutsNS_dom _ hc hBC hCh g hg)
        · right
          have hhiC : (split y (psi (succ s) z z)).1 < C := lt_of_not_ge hCh
          obtain ⟨c0, hc0, _, _⟩ := between_app (x := z) (c := C) (by rw [app_z_right]; exact hhiC) hCX
          refine ⟨⟨c0, hc0⟩, cutsNS_dom _ hc ?_ (le_refl _) g hg⟩
          rcases (le_iff _ _).mp (cutsNSG_le hc) with h | h
          · exact h
          · exact absurd h.symm hne
      rcases hD with h | ⟨⟨c0, hc0⟩, h⟩
      · rcases h with h | h | ⟨d, hd, hgd⟩
        · subst h; exact ⟨C, List.mem_cons_self .., z_le _⟩
        · exact hsdom g h
        · exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_left _ hd), hgd⟩
      · rcases h with h | h | ⟨d, hd, hgd⟩
        · subst h; exact ⟨C, List.mem_cons_self .., z_le _⟩
        · exact hsdom g h
        · refine ⟨d, List.mem_cons_of_mem _ (List.mem_append_left _ ?_), hgd⟩
          rw [hc0, comps_app]; exact List.mem_append_left _ hd
    · exact hsdom g hg

end Ytosk
