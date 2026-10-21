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

/-! ## s から始まる位置で切る形（2026-10-21、lead）

C の種の枠は切る場合で、切る位置の添字は s′ から始まる（s′ ≤ a なら a = s′ ++ δ）。そのとき (B, hi] のどの C も、
B の成分を C の成分で押さえ、s の成分を C の成分として持つ（`frameDom_of_cutP`）。s の成分の条件 `hs` は要らない。 -/

/-- `s` is a summand prefix of `w`. -/
def prefB : T → T → Bool
  | z, _ => true
  | psi _ _ _, z => false
  | psi a b c, psi a' b' c' => decide (a = a') && decide (b = b') && prefB c c'

theorem prefB_app : ∀ {s w : T}, prefB s w = true → ∃ δ, w = app s δ
  | z, w, _ => ⟨w, by rw [app_z]⟩
  | psi a b c, z, h => by simp [prefB] at h
  | psi a b c, psi a' b' c', h => by
    simp only [prefB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    obtain ⟨δ, rfl⟩ := prefB_app h
    exact ⟨δ, by rw [app_psi]⟩

/-- **Between `s` and `s ++ δ`** every term starts with `s`. -/
theorem app_prefix_between : ∀ {s w δ : T}, s ≤ w → w ≤ app s δ → ∃ δ', w = app s δ'
  | z, w, _, _, _ => ⟨w, by rw [app_z]⟩
  | psi a b c, w, δ, h1, h2 => by
    rw [app_psi] at h2
    cases w with
    | z =>
      rcases (le_iff _ _).mp h1 with h | h
      · exact absurd h (T.not_lt_z _)
      · exact absurd h (by simp)
    | psi a' b' c' =>
      rcases (le_iff _ _).mp h1 with h1 | h1
      · rcases (le_iff _ _).mp h2 with h2 | h2
        · rcases T.psi_lt_psi.mp h1 with ha | ⟨e1, hb⟩ | ⟨e1, e2, hc⟩
          · rcases T.psi_lt_psi.mp h2 with ha2 | ⟨e, _⟩ | ⟨e, _, _⟩
            · exact absurd (T.lt_trans' ha ha2) (lt_irrefl' _)
            · rw [e] at ha; exact absurd ha (lt_irrefl' _)
            · rw [e] at ha; exact absurd ha (lt_irrefl' _)
          · subst e1
            rcases T.psi_lt_psi.mp h2 with ha2 | ⟨_, hb2⟩ | ⟨_, e, _⟩
            · exact absurd ha2 (lt_irrefl' _)
            · exact absurd (T.lt_trans' hb hb2) (lt_irrefl' _)
            · rw [e] at hb; exact absurd hb (lt_irrefl' _)
          · subst e1; subst e2
            rcases T.psi_lt_psi.mp h2 with ha2 | ⟨_, hb2⟩ | ⟨_, _, hc2⟩
            · exact absurd ha2 (lt_irrefl' _)
            · exact absurd hb2 (lt_irrefl' _)
            · obtain ⟨δ', e⟩ := app_prefix_between (Or.inl hc) (Or.inl hc2)
              exact ⟨δ', by rw [e, app_psi]⟩
        · simp only [psi.injEq] at h2
          obtain ⟨rfl, rfl, rfl⟩ := h2
          exact ⟨δ, by rw [app_psi]⟩
      · rw [← h1]; exact ⟨z, by rw [app_z_right]⟩

/-- The cuts of `cutsHG` whose replaced subterm's subscript starts with `s`. -/
def cutsPHG (s : T) : T → List T
  | z => []
  | psi a x c =>
      (cutsPHG s a).map (fun t => psi t z z) ++
        (if le s a then (if prefB s a then [psi s z z] else []) ++ (cutsPHG s x).map (fun t => psi a t z) ++
          (cutsPHG s c).map (fun t => psi a x t) else [])

/-- The cuts of `cutsNSG` whose replaced subterm's subscript starts with `s`. -/
def cutsPNSG (s : T) : T → List T
  | z => []
  | psi a x c =>
      (cutsPHG s a).map (fun t => psi t z z) ++ (cutsPHG s x).map (fun t => psi a t z) ++
        (cutsPNSG s c).map (fun t => psi a x t)

theorem mem_cutsPHG_psi {s a x c t : T} : t ∈ cutsPHG s (psi a x c) ↔
    (le s a = true ∧ prefB s a = true ∧ t = psi s z z) ∨ (∃ u ∈ cutsPHG s a, t = psi u z z) ∨
      (le s a = true ∧ ∃ u ∈ cutsPHG s x, t = psi a u z) ∨ (le s a = true ∧ ∃ u ∈ cutsPHG s c, t = psi a x u) := by
  show t ∈ (cutsPHG s a).map (fun t => psi t z z) ++
    (if le s a then (if prefB s a then [psi s z z] else []) ++ (cutsPHG s x).map (fun t => psi a t z) ++
      (cutsPHG s c).map (fun t => psi a x t) else []) ↔ _
  by_cases h : le s a = true
  · by_cases hp : prefB s a = true
    · simp only [h, hp, if_true, List.mem_append, List.mem_singleton, List.mem_map, true_and]
      constructor
      · rintro (⟨u, hu, rfl⟩ | ((rfl | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩))
        · exact Or.inr (Or.inl ⟨u, hu, rfl⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl ⟨u, hu, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨u, hu, rfl⟩))
      · rintro (rfl | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
        · exact Or.inr (Or.inl (Or.inl rfl))
        · exact Or.inl ⟨u, hu, rfl⟩
        · exact Or.inr (Or.inl (Or.inr ⟨u, hu, rfl⟩))
        · exact Or.inr (Or.inr ⟨u, hu, rfl⟩)
    · have hp' : prefB s a = false := by simpa using hp
      simp only [h, hp', if_true, Bool.false_eq_true, if_false, List.nil_append, List.mem_append, List.mem_map,
        true_and, false_and, false_or]
      constructor
      · rintro (⟨u, hu, rfl⟩ | (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩))
        · exact Or.inl ⟨u, hu, rfl⟩
        · exact Or.inr (Or.inl ⟨u, hu, rfl⟩)
        · exact Or.inr (Or.inr ⟨u, hu, rfl⟩)
      · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
        · exact Or.inl ⟨u, hu, rfl⟩
        · exact Or.inr (Or.inl ⟨u, hu, rfl⟩)
        · exact Or.inr (Or.inr ⟨u, hu, rfl⟩)
  · have h' : le s a = false := by simpa using h
    rw [h']
    simp only [Bool.false_eq_true, if_false, List.mem_append, List.mem_map, List.not_mem_nil, or_false,
      false_and, false_or]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩

theorem mem_cutsPNSG_psi {s a x c t : T} : t ∈ cutsPNSG s (psi a x c) ↔
    (∃ u ∈ cutsPHG s a, t = psi u z z) ∨ (∃ u ∈ cutsPHG s x, t = psi a u z) ∨
      (∃ u ∈ cutsPNSG s c, t = psi a x u) := by
  show t ∈ (cutsPHG s a).map (fun t => psi t z z) ++ (cutsPHG s x).map (fun t => psi a t z) ++
    (cutsPNSG s c).map (fun t => psi a x t) ↔ _
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro ((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
    · exact Or.inl ⟨u, hu, rfl⟩
    · exact Or.inr (Or.inl ⟨u, hu, rfl⟩)
    · exact Or.inr (Or.inr ⟨u, hu, rfl⟩)
  · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact Or.inl (Or.inl ⟨u, hu, rfl⟩)
    · exact Or.inl (Or.inr ⟨u, hu, rfl⟩)
    · exact Or.inr ⟨u, hu, rfl⟩

theorem cutsPHG_sub {s : T} : ∀ {h t : T}, t ∈ cutsPHG s h → t ∈ cutsHG s h
  | z, _, ht => by simp [cutsPHG] at ht
  | psi a x c, t, ht => by
    rcases mem_cutsPHG_psi.mp ht with ⟨hsa, _, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨hsa, u, hu, rfl⟩ | ⟨hsa, u, hu, rfl⟩
    · exact mem_cutsHG_psi.mpr (Or.inl ⟨hsa, rfl⟩)
    · exact mem_cutsHG_psi.mpr (Or.inr (Or.inl ⟨u, cutsPHG_sub hu, rfl⟩))
    · exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨hsa, u, cutsPHG_sub hu, rfl⟩)))
    · exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inr ⟨hsa, u, cutsPHG_sub hu, rfl⟩)))

theorem cutsPNSG_sub {s : T} : ∀ {h t : T}, t ∈ cutsPNSG s h → t ∈ cutsNSG s h
  | z, _, ht => by simp [cutsPNSG] at ht
  | psi a x c, t, ht => by
    rcases mem_cutsPNSG_psi.mp ht with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact mem_cutsNSG_psi.mpr (Or.inl ⟨u, cutsPHG_sub hu, rfl⟩)
    · exact mem_cutsNSG_psi.mpr (Or.inr (Or.inl ⟨u, cutsPHG_sub hu, rfl⟩))
    · exact mem_cutsNSG_psi.mpr (Or.inr (Or.inr ⟨u, cutsPNSG_sub hu, rfl⟩))

/-- **The components of `s` are components of a prefix cut** (at a level `u ≤ s`). -/
theorem cutsPHG_comps {s u : T} (hsu : ¬ lt s u = true) : ∀ {h t : T}, t ∈ cutsPHG s h →
    ∀ g ∈ comps u s, g ∈ comps u t
  | z, _, ht => by simp [cutsPHG] at ht
  | psi a x c, t, ht => by
    intro g hg
    rcases mem_cutsPHG_psi.mp ht with ⟨_, _, rfl⟩ | ⟨v, hv, rfl⟩ | ⟨hsa, v, hv, rfl⟩ | ⟨_, v, hv, rfl⟩
    · exact mem_comps_head hsu (Or.inr (Or.inr hg))
    · have hsv : s < v := cutsHG_gt (cutsPHG_sub hv)
      have hvu : ¬ lt v u = true := fun h' => hsu (T.lt_trans' hsv h')
      exact mem_comps_head hvu (Or.inr (Or.inr (cutsPHG_comps hsu hv g hg)))
    · have hau : ¬ lt a u = true := fun h' => hsu (show s < u from lt_of_le_of_lt ((le_bool_iff s a).mp hsa) (show a < u from h'))
      exact mem_comps_head hau (Or.inr (Or.inl (cutsPHG_comps hsu hv g hg)))
    · exact mem_comps_rest (cutsPHG_comps hsu hv g hg)

theorem cutsPNSG_comps {s u : T} (hsu : ¬ lt s u = true) : ∀ {h t : T}, (∀ q ∈ summands h, ¬ q < psi s z z) →
    t ∈ cutsPNSG s h → ∀ g ∈ comps u s, g ∈ comps u t
  | z, _, _, ht => by simp [cutsPNSG] at ht
  | psi a x c, t, hge, ht => by
    intro g hg
    rcases mem_cutsPNSG_psi.mp ht with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · have hsv : s < v := cutsHG_gt (cutsPHG_sub hv)
      have hvu : ¬ lt v u = true := fun h' => hsu (T.lt_trans' hsv h')
      exact mem_comps_head hvu (Or.inr (Or.inr (cutsPHG_comps hsu hv g hg)))
    · have hsa : s ≤ a := by
        have h0 : ¬ psi a x z < psi s z z := hge _ (by simp [summands])
        rcases lt_or_ge a s with h | h
        · exact absurd (psi_lt_psi_z_iff.mpr (Or.inl h)) h0
        · exact h
      have hau : ¬ lt a u = true := fun h' => hsu (show s < u from lt_of_le_of_lt hsa (show a < u from h'))
      exact mem_comps_head hau (Or.inr (Or.inl (cutsPHG_comps hsu hv g hg)))
    · exact mem_comps_rest (cutsPNSG_comps hsu (fun q hq => hge q (by simp [summands, hq])) hv g hg)

/-- `g` is `0` or below a component of `C`. -/
def CutDomP (u C g : T) : Prop := g = z ∨ ∃ d ∈ comps u C, g ≤ d

theorem cutDomP_mono {u C C' g : T} (hsub : ∀ d ∈ comps u C', d ∈ comps u C) (h : CutDomP u C' g) :
    CutDomP u C g := by
  rcases h with h | ⟨d, hd, hgd⟩
  · exact Or.inl h
  · exact Or.inr ⟨d, hsub d hd, hgd⟩

theorem psi_le_sub {w e f a x c : T} (h : psi w e f ≤ psi a x c) : w ≤ a := by
  rcases (le_iff _ _).mp h with h | h
  · rcases T.psi_lt_psi.mp h with h | ⟨h, _⟩ | ⟨h, _, _⟩
    · exact le_of_lt h
    · rw [h]
    · rw [h]
  · simp only [psi.injEq] at h; rw [h.1]

theorem lt_psi_sub_cases {t w e f : T} (h : psi t z z < psi w e f) : t < w ∨ t = w := by
  rcases T.psi_lt_psi.mp h with h | ⟨h, _⟩ | ⟨h, _, _⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inr h

theorem arg_cases {a t w e f x c : T} (htC : psi a t z < psi w e f) (hCY : psi w e f ≤ psi a x c) :
    w = a ∧ (t < e ∨ t = e) ∧ e ≤ x := by
  have hwa : w = a := by
    rcases (le_iff _ _).mp hCY with h | h
    · rcases T.psi_lt_psi.mp htC with h' | ⟨h', _⟩ | ⟨h', _, _⟩
      · rcases T.psi_lt_psi.mp h with h2 | ⟨h2, _⟩ | ⟨h2, _, _⟩
        · exact absurd (T.lt_trans' h' h2) (lt_irrefl' _)
        · exact absurd (h2 ▸ h') (lt_irrefl' _)
        · exact absurd (h2 ▸ h') (lt_irrefl' _)
      · exact h'.symm
      · exact h'.symm
    · simp only [psi.injEq] at h; exact h.1
  subst hwa
  refine ⟨rfl, ?_, ?_⟩
  · rcases T.psi_lt_psi.mp htC with h | ⟨_, h⟩ | ⟨_, h, _⟩
    · exact absurd h (lt_irrefl' _)
    · exact Or.inl h
    · exact Or.inr h
  · rcases (le_iff _ _).mp hCY with h | h
    · rcases T.psi_lt_psi.mp h with h | ⟨_, h⟩ | ⟨_, h, _⟩
      · exact absurd h (lt_irrefl' _)
      · exact le_of_lt h
      · rw [h]
    · simp only [psi.injEq] at h; rw [h.2.1]

theorem rest_cases {a x t w e f c : T} (htC : psi a x t < psi w e f) (hCY : psi w e f ≤ psi a x c) :
    w = a ∧ e = x ∧ t < f ∧ f ≤ c := by
  have hwe : w = a ∧ e = x := by
    rcases (le_iff _ _).mp hCY with h | h
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
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rcases T.psi_lt_psi.mp htC with h | ⟨_, h⟩ | ⟨_, _, h⟩
    · exact absurd h (lt_irrefl' _)
    · exact absurd h (lt_irrefl' _)
    · exact h
  · rcases (le_iff _ _).mp hCY with h | h
    · rcases T.psi_lt_psi.mp h with h | ⟨_, h⟩ | ⟨_, _, h⟩
      · exact absurd h (lt_irrefl' _)
      · exact absurd h (lt_irrefl' _)
      · exact le_of_lt h
    · simp only [psi.injEq] at h; rw [h.2.2]

/-- The subscript and argument cases shared by `cutsPH_dom` and `cutsPNS_dom`. -/
theorem cutDomP_sub {u t' w e f a g : T} (hrec : t' < w → w ≤ a → ∀ g ∈ comps u t', CutDomP u w g)
    (htw : t' < w ∨ t' = w) (hwa : w ≤ a) (hg : g ∈ comps u (psi t' z z)) : CutDomP u (psi w e f) g := by
  rcases comps_psi_cases hg with ⟨hu, h | h | h⟩ | h
  · exact Or.inl h
  · simp [comps] at h
  · rcases htw with htw | htw
    · have hw : ¬ lt w u = true := fun h' => hu (T.lt_trans' htw h')
      exact cutDomP_mono (fun d hd => mem_comps_head hw (Or.inr (Or.inr hd))) (hrec htw hwa g h)
    · subst htw
      exact Or.inr ⟨g, mem_comps_head hu (Or.inr (Or.inr h)), le_refl _⟩
  · simp [comps] at h

theorem cutDomP_arg {u a t e f x g : T} (hrec : t < e → e ≤ x → ∀ g ∈ comps u t, CutDomP u e g)
    (hex : t < e ∨ t = e) (hex' : e ≤ x) (hg : g ∈ comps u (psi a t z)) : CutDomP u (psi a e f) g := by
  rcases comps_psi_cases hg with ⟨hu, h | h | h⟩ | h
  · subst h
    refine Or.inr ⟨e, mem_comps_head hu (Or.inl rfl), ?_⟩
    rcases hex with h | h
    · exact le_of_lt h
    · rw [h]
  · rcases hex with hex | hex
    · exact cutDomP_mono (fun d hd => mem_comps_head hu (Or.inr (Or.inl hd))) (hrec hex hex' g h)
    · subst hex
      exact Or.inr ⟨g, mem_comps_head hu (Or.inr (Or.inl h)), le_refl _⟩
  · exact Or.inr ⟨g, mem_comps_head hu (Or.inr (Or.inr h)), le_refl _⟩
  · simp [comps] at h

theorem cutDomP_rest {u a x t f g : T} (hrec : ∀ g ∈ comps u t, CutDomP u f g) (hg : g ∈ comps u (psi a x t)) :
    CutDomP u (psi a x f) g := by
  rcases comps_psi_cases hg with ⟨hu, hh⟩ | h
  · exact Or.inr ⟨g, mem_comps_head hu hh, le_refl _⟩
  · exact cutDomP_mono (fun d hd => mem_comps_rest hd) (hrec g h)

/-- **`cutsH_dom` for prefix cuts**: the components of `s` at the cut `Ω_s` are components of `C`. -/
theorem cutsPH_dom {s u : T} : ∀ (Y : T) {t C : T}, t ∈ cutsPHG s Y → t < C → C ≤ Y →
    ∀ g ∈ comps u t, CutDomP u C g
  | z, _, _, ht, _, _ => by simp [cutsPHG] at ht
  | psi a x c, t, C, ht, htC, hCY => by
    intro g hg
    cases C with
    | z => exact absurd htC (T.not_lt_z _)
    | psi w e f =>
    have hwa : w ≤ a := psi_le_sub hCY
    rcases mem_cutsPHG_psi.mp ht with ⟨_, hp, rfl⟩ | ⟨t', ht', rfl⟩ | ⟨_, t2, ht2, rfl⟩ | ⟨_, t3, ht3, rfl⟩
    · -- the cut `Ω_s` at a subscript starting with `s`
      rcases comps_psi_cases hg with ⟨hu, h | h | h⟩ | h
      · exact Or.inl h
      · simp [comps] at h
      · refine Or.inr ⟨g, ?_, le_refl _⟩
        rcases lt_psi_sub_cases htC with hsw | hsw
        · obtain ⟨δ, hδ⟩ := prefB_app hp
          obtain ⟨δ', hδ'⟩ := app_prefix_between (le_of_lt hsw) (by rw [← hδ]; exact hwa)
          have hwu : ¬ lt w u = true := fun h' => hu (T.lt_trans' hsw h')
          refine mem_comps_head hwu (Or.inr (Or.inr ?_))
          rw [hδ', comps_app]; exact List.mem_append_left _ h
        · subst hsw; exact mem_comps_head hu (Or.inr (Or.inr h))
      · simp [comps] at h
    · exact cutDomP_sub (fun h1 h2 => cutsPH_dom a ht' h1 h2) (lt_psi_sub_cases htC) hwa hg
    · obtain ⟨rfl, hex, hex'⟩ := arg_cases htC hCY
      exact cutDomP_arg (fun h1 h2 => cutsPH_dom x ht2 h1 h2) hex hex' hg
    · obtain ⟨rfl, rfl, htf, hfc⟩ := rest_cases htC hCY
      exact cutDomP_rest (cutsPH_dom c ht3 htf hfc) hg

/-- **`cutsNS_dom` for prefix cuts.** -/
theorem cutsPNS_dom {s u : T} : ∀ (Y : T) {t C : T}, t ∈ cutsPNSG s Y → t < C → C ≤ Y →
    ∀ g ∈ comps u t, CutDomP u C g
  | z, _, _, ht, _, _ => by simp [cutsPNSG] at ht
  | psi a x c, t, C, ht, htC, hCY => by
    intro g hg
    cases C with
    | z => exact absurd htC (T.not_lt_z _)
    | psi w e f =>
    rcases mem_cutsPNSG_psi.mp ht with ⟨t', ht', rfl⟩ | ⟨t2, ht2, rfl⟩ | ⟨t3, ht3, rfl⟩
    · exact cutDomP_sub (fun h1 h2 => cutsPH_dom a ht' h1 h2) (lt_psi_sub_cases htC) (psi_le_sub hCY) hg
    · obtain ⟨rfl, hex, hex'⟩ := arg_cases htC hCY
      exact cutDomP_arg (fun h1 h2 => cutsPH_dom x ht2 h1 h2) hex hex' hg
    · obtain ⟨rfl, rfl, htf, hfc⟩ := rest_cases htC hCY
      exact cutDomP_rest (cutsPNS_dom c ht3 htf hfc) hg

/-- **FrameDom at a prefix cut**: no condition on the components of `s` is needed. -/
theorem frameDom_of_cutP {a B s y : T} (hot : isOT (psi s y z) = true)
    (has : ∀ u, ¬ lt a u = true → ¬ lt s u = true)
    (hc : B ∈ cutsPNSG s (split y (psi (succ s) z z)).1)
    (hge : ∀ q ∈ summands (split y (psi (succ s) z z)).1, ¬ q < psi s z z) :
    FrameDom a B s (H s y) := by
  rw [H_eq hot]
  generalize (split y (psi (succ s) z z)).1 = hi at hc hge ⊢
  intro u hu C hBC _ hCX g hg
  have hsu := has u hu
  have hgB : g ∈ comps u B := hg.elim id (fun h => cutsPNSG_comps hsu hge hc g h)
  have hBhi : B ≤ hi := cutsNSG_le (cutsPNSG_sub hc)
  by_cases hCh : C ≤ hi
  · rcases cutsPNS_dom hi hc hBC hCh g hgB with h | ⟨d, hd, hgd⟩
    · subst h; exact ⟨C, List.mem_cons_self .., z_le _⟩
    · exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_left _ hd), hgd⟩
  · have hhiC : hi < C := lt_of_not_ge hCh
    obtain ⟨c0, hc0, _, _⟩ := between_app (x := z) (c := C) (by rw [app_z_right]; exact hhiC) hCX
    have hsub : ∀ d ∈ comps u hi, d ∈ comps u C := fun d hd => by
      rw [hc0, comps_app]; exact List.mem_append_left _ hd
    rcases (le_iff _ _).mp hBhi with hlt | heq
    · rcases cutsPNS_dom hi hc hlt (le_refl _) g hgB with h | ⟨d, hd, hgd⟩
      · subst h; exact ⟨C, List.mem_cons_self .., z_le _⟩
      · exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_left _ (hsub d hd)), hgd⟩
    · rw [heq] at hgB
      exact ⟨g, List.mem_cons_of_mem _ (List.mem_append_left _ (hsub g hgB)), le_refl _⟩

end Ytosk
