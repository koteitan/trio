/-
**RelR を段の集合 U に制限した版（2026-10-12、t0-exp）。** V3RelR の RelR に関わる補題を、段 u を U u のものに限って写したもの。
Buchholz の補題 3.4（closed_of_relRU）は段 q だけを使うので、U = {q} でよい。
-/
import Ytosk.V3RelR
import Ytosk.V3DropR

namespace Ytosk

open T

variable {U : T → Prop}

/-- **`◁` with the components below `b` exempted**, at the levels `u ≤ q`; the components of `q` also
dominate. -/
def RelRU (U : T → Prop) (q b A : T) : Prop :=
  ∀ u, U u → ¬ lt q u = true → ∀ c, b < c → c ≤ A →
    ∀ g ∈ comps u b, g < b ∨ ∃ d ∈ Gc u c ++ comps u q, g ≤ d


/-- **Buchholz's Lemma 3.4 for `RelRU U`.** -/
theorem closed_of_relRU {q b A : T} (hUq : U q) (hbA : b ≤ A) (hR : RelRU U q b A)
    (hA : ∀ g ∈ comps q A, g < A) (hq : ∀ d ∈ comps q q, d < b) :
    ∀ g ∈ comps q b, g < b := by
  rcases (le_iff _ _).mp hbA with hbA | rfl
  swap
  · exact hA
  have hq0 : ¬ lt q q = true := lt_irrefl' q
  -- strong induction on the size of the component
  have key : ∀ n, ∀ g ∈ comps q b, size g < n → g < b := by
    intro n
    induction n with
    | zero => intro g _ h; omega
    | succ n ih =>
      intro g hg hn
      by_contra hgb
      have hbg : b ≤ g := not_lt.mp hgb
      have hbg' : b < g := by
        rcases (le_iff _ _).mp hbg with h | h
        · exact h
        · exfalso; have := size_comps hg; rw [← h] at this; omega
      have hz : ∀ d, g ≤ d → d = z → False := by
        intro d hgd hd; subst hd
        exact absurd (lt_of_lt_of_le hbg' hgd) (T.not_lt_z _)
      -- the test `A`: `g < A`
      have hgA : g < A := by
        rcases hR q hUq hq0 A hbA (le_refl _) g hg with h | ⟨d, hd, hgd⟩
        · exact absurd h hgb
        · simp only [Gc, List.mem_append, List.mem_cons] at hd
          rcases hd with (rfl | hd) | hd
          · exact (hz _ hgd rfl).elim
          · exact lt_of_le_of_lt hgd (hA d hd)
          · exact absurd (lt_of_le_of_lt hgd (hq d hd)) hgb
      -- the test `g` itself
      rcases hR q hUq hq0 g hbg' (le_of_lt hgA) g hg with h | ⟨d, hd, hgd⟩
      · exact hgb h
      · simp only [Gc, List.mem_append, List.mem_cons] at hd
        rcases hd with (rfl | hd) | hd
        · exact hz _ hgd rfl
        · have hdb : d < b := ih d (comps_trans hg d hd) (by have := size_comps hd; omega)
          exact hgb (lt_of_le_of_lt hgd hdb)
        · exact hgb (lt_of_le_of_lt hgd (hq d hd))
  exact fun g hg => key _ g hg (Nat.lt_succ_self _)


/-- **The hard case from `RelRU U`**: if the new state `H s y′` is in the relation `RelRU U a` with the old state
`H s y` and `ψ_a(H(s, y))` is standard, then the components of `y′` at the level `a` are at most `H s y′`. -/
theorem hard_of_relRU {a s y y' : T} (hc' : isOT (psi s y' z) = true) (has : lt a s = true)
    (haot : isOT a = true) (hot : isOT (psi a (H s y) z) = true) (hle : H s y' ≤ H s y)
    (hR : RelRU U a (H s y') (H s y)) (hUa : U a) :
    ∀ g ∈ comps a y', g ≤ H s y' := by
  have hA : ∀ g ∈ comps a (H s y), g < H s y := ((isOT_psi_iff).mp hot).2.2.2.2
  have hq : ∀ d ∈ comps a a, d < H s y' := by rw [comps_self_nil haot]; simp
  have hcl := closed_of_relRU hUa hle hR hA hq
  have hsa : ¬ lt s a = true := fun h => lt_irrefl' _ (lt_trans (show a < s from has) h)
  intro g hg
  rcases comps_y_sub_H hc' hsa g hg with h | h
  · exact le_of_lt (hcl g h)
  · rw [← h] at hg; exact le_of_lt (hcl g hg)


theorem relR_reflU (q b : T) : RelRU U q b b :=
  fun _ _ _ c h1 h2 => absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)


/-- **Changing the parent subscript**: a relation with the components of `p` as extra dominators gives one
with those of `q ≤ p`, when the components of `p` are below `b` or dominated by those of `q`. -/
theorem relR_of_le_qU {p q b A : T} (hqp : ¬ lt p q = true) (hR : RelRU U p b A)
    (hconv : ∀ u, U u → ¬ lt q u = true → ∀ d ∈ comps u p, d < b ∨ ∃ d' ∈ comps u q, d ≤ d') : RelRU U q b A := by
  intro u hU hu c h1 h2 g hg
  have hpu : ¬ lt p u = true := by
    intro h
    have hq : q ≤ p := not_lt.mp hqp
    exact hu (lt_of_le_of_lt hq h)
  rcases hR u hU hpu c h1 h2 g hg with h | ⟨d, hd, hgd⟩
  · exact Or.inl h
  · rcases List.mem_append.mp hd with hd | hd
    · exact Or.inr ⟨d, List.mem_append_left _ hd, hgd⟩
    · rcases hconv u hU hu d hd with h | ⟨d', hd', hdd'⟩
      · exact Or.inl (lt_of_le_of_lt hgd h)
      · exact Or.inr ⟨d', List.mem_append_right _ hd', le_trans hgd hdd'⟩


/-- **`◁` after a common prefix gives `RelRU U`** (no exemption needed). -/
theorem relR_prefix_lhdU {q P b0 A0 : T} (h : Lhd z b0 A0) : RelRU U q (app P b0) (app P A0) := by
  intro u hU _ c h1 h2 g hg
  obtain ⟨c0, rfl, hc1, hc2⟩ := between_app h1 h2
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩
  · obtain ⟨d, hd, hgd⟩ := h.2 u c0 hc1 hc2 g hg
    right
    refine ⟨d, List.mem_append_left _ ?_, hgd⟩
    rcases List.mem_append.mp hd with hd | hd
    · exact gc_app_right d (List.mem_cons_of_mem _ hd)
    · simp [Gc, comps] at hd; subst hd; exact gc_app_right _ List.mem_cons_self


theorem relR_prefix_lhdEU {q P b0 A0 : T} (h : LhdE b0 A0) : RelRU U q (app P b0) (app P A0) := by
  rcases h with rfl | h
  · exact relR_reflU _ _
  · exact relR_prefix_lhdU h


/-- **Extending the top**: tests above `A` start with some `P ∈ (b, A]`. -/
theorem relR_ext_prefixU {q b A P A' : T} (hR : RelRU U q b A) (hbP : b < P) (hPA : P ≤ A)
    (hA' : ∀ c, A < c → c ≤ A' → ∃ c0, c = app P c0) : RelRU U q b A' := by
  intro u hU hu c h1 h2 g hg
  by_cases hcA : c ≤ A
  · exact hR u hU hu c h1 hcA g hg
  · obtain ⟨c0, rfl⟩ := hA' c (lt_of_not_ge hcA) h2
    rcases hR u hU hu P hbP hPA g hg with h | ⟨d, hd, hgd⟩
    · exact Or.inl h
    · rcases List.mem_append.mp hd with hd | hd
      · refine Or.inr ⟨d, List.mem_append_left _ ?_, hgd⟩
        unfold Gc at hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact List.mem_cons_self
        · exact gc_app_left d hd
      · exact Or.inr ⟨d, List.mem_append_right _ hd, hgd⟩


/-- **Extending the top by domination**: every test above `A` dominates the components of `A`. -/
theorem relR_ext_domU {q b A A' : T} (hR : RelRU U q b A) (hb : b ≤ A)
    (hdom : ∀ u c, A < c → c ≤ A' → ∀ d ∈ Gc u A, ∃ d' ∈ Gc u c, d ≤ d') : RelRU U q b A' := by
  intro u hU hu c h1 h2 g hg
  by_cases hcA : c ≤ A
  · exact hR u hU hu c h1 hcA g hg
  have hAc : A < c := lt_of_not_ge hcA
  rcases (le_iff _ _).mp hb with hbA | rfl
  · rcases hR u hU hu A hbA (le_refl _) g hg with h | ⟨d, hd, hgd⟩
    · exact Or.inl h
    · rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨d', hd', hdd'⟩ := hdom u c hAc h2 d hd
        exact Or.inr ⟨d', List.mem_append_left _ hd', le_trans hgd hdd'⟩
      · exact Or.inr ⟨d, List.mem_append_right _ hd, hgd⟩
  · obtain ⟨d', hd', hgd'⟩ := hdom u c hAc h2 g (List.mem_cons_of_mem _ hg)
    exact Or.inr ⟨d', List.mem_append_left _ hd', hgd'⟩


/-- **Raising the bottom**: the new components are below `b`, components of `b0`, or dominated by `q`. -/
theorem relR_of_subU {q b0 b A : T} (hR : RelRU U q b0 A) (hle : b0 ≤ b)
    (hsub : ∀ u, U u → ¬ lt q u = true → ∀ g ∈ comps u b, g < b ∨ g ∈ comps u b0 ∨ ∃ d ∈ comps u q, g ≤ d) :
    RelRU U q b A := by
  intro u hU hu c h1 h2 g hg
  rcases hsub u hU hu g hg with h | h | ⟨d, hd, hgd⟩
  · exact Or.inl h
  · rcases hR u hU hu c (lt_of_le_of_lt hle h1) h2 g h with h' | h'
    · exact Or.inl (lt_of_lt_of_le h' hle)
    · exact Or.inr h'
  · exact Or.inr ⟨d, List.mem_append_right _ hd, hgd⟩


/-- **The removed last child `x` (`o(x) = Ω_w`) only raises the top.** -/
theorem relR_tlU {q p b Y0 w : T} (hR : RelRU U q b (H p Y0)) (hb : b ≤ H p Y0)
    (hY0 : isOT (psi p Y0 z) = true) (hY : isOT (psi p (app Y0 (psi w z z)) z) = true)
    (hge : ∀ q' ∈ summands Y0, psi w z z ≤ q') :
    RelRU U q b (H p (app Y0 (psi w z z))) := by
  apply relR_ext_domU hR hb
  intro u c h1 h2 d hd
  set θ := psi (succ p) z z with hθ
  by_cases hw : psi w z z < θ
  · set P := (split Y0 θ).1 with hPdef
    set L := (split Y0 θ).2 with hLdef
    have eY0 : app P L = Y0 := split_app θ Y0
    have hP : ∀ q ∈ summands P, ¬ q < θ := split_fst_ge θ Y0
    have hL : L = z ∨ head L < θ := split_snd_head θ Y0
    have eY : app Y0 (psi w z z) = app P (app L (psi w z z)) := by rw [← eY0, app_assoc]
    obtain ⟨hr0, hrl⟩ := head_app_low (r := psi w z z) hL (by simpa [head] using hw) (by simp)
    have hHY : H p (app Y0 (psi w z z)) = app P (psi p (app Y0 (psi w z z)) z) := by
      rw [eY] at hY ⊢; exact H_hi_low hY hP hr0 hrl
    rw [hHY] at h2
    have hHY0 := H_eq hY0
    rw [← hPdef, ← hLdef] at hHY0
    by_cases hL0 : L = z
    · rw [if_pos hL0] at hHY0
      rw [hHY0] at h1 hd
      obtain ⟨c0, rfl, _, _⟩ := between_app h1 h2
      unfold Gc at hd
      rw [app_z_right] at hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨z, List.mem_cons_self, le_refl _⟩
      · exact ⟨d, gc_app_left d hd, le_refl _⟩
    · rw [if_neg hL0] at hHY0
      rw [hHY0] at h1 hd
      obtain ⟨c0, rfl, hc1, hc2⟩ := between_app h1 h2
      obtain ⟨W, c1, rfl, hW1, hW2⟩ := between_psi hc1 hc2
      unfold Gc at hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨z, List.mem_cons_self, le_refl _⟩
      rw [comps_app] at hd
      rcases List.mem_append.mp hd with hd | hd
      · exact ⟨d, gc_app_left d hd, le_refl _⟩
      simp only [comps, List.mem_append] at hd
      rcases hd with hd | hd
      swap
      · simp at hd
      split at hd
      · simp at hd
      rename_i hpu
      have hmem : ∀ e ∈ W :: (comps u W ++ comps u p), e ∈ Gc u (app P (psi p W c1)) := by
        intro e he
        apply gc_app_right
        unfold Gc; apply List.mem_cons_of_mem
        simp only [comps]; rw [if_neg hpu]
        exact List.mem_append_left _ he
      simp only [List.mem_cons, List.mem_append] at hd
      rcases hd with rfl | hd | hd
      · exact ⟨W, hmem W List.mem_cons_self, hW1⟩
      · rcases (le_iff _ _).mp hW1 with hlt | rfl
        · obtain ⟨W0, rfl, _, _⟩ := between_app (A := Y0) (x := z) (by rw [app_z_right]; exact hlt) hW2
          refine ⟨d, hmem d (List.mem_cons_of_mem _ (List.mem_append_left _ ?_)), le_refl _⟩
          rw [comps_app]; exact List.mem_append_left _ hd
        · exact ⟨d, hmem d (List.mem_cons_of_mem _ (List.mem_append_left _ hd)), le_refl _⟩
      · exact ⟨d, hmem d (List.mem_cons_of_mem _ (List.mem_append_right _ hd)), le_refl _⟩
  · have hall : ∀ q' ∈ summands Y0, ¬ q' < θ :=
      fun q' hq' => not_lt.mpr (le_trans (not_lt.mp hw) (hge q' hq'))
    have hHY0 : H p Y0 = Y0 := H_all_hi hY0 hall
    have hallY : ∀ q' ∈ summands (app Y0 (psi w z z)), ¬ q' < θ := by
      intro q' hq'
      rw [summands_app, List.mem_append] at hq'
      rcases hq' with hq' | hq'
      · exact hall q' hq'
      · simp [summands] at hq'; subst hq'; exact hw
    rw [H_all_hi hY hallY] at h2
    rw [hHY0] at h1 hd
    obtain ⟨c0, rfl, _, _⟩ := between_app (A := Y0) (x := z) (by rw [app_z_right]; exact h1) h2
    unfold Gc at hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨z, List.mem_cons_self, le_refl _⟩
    · exact ⟨d, gc_app_left d hd, le_refl _⟩


/-- A term starting with `P` is in the relation with every longer term starting with `P`. -/
theorem relR_self_prefixU {q P A : T} (hA : ∀ c, P < c → c ≤ A → ∃ c0, c = app P c0) : RelRU U q P A := by
  intro u hU _ c h1 h2 g hg
  obtain ⟨c0, rfl⟩ := hA c h1 h2
  exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩


/-- **Both rewrite, `p < s`**: the new and old states are all high, so the claim at the child (taken at the
parent level `p`) passes up; the components of `p` are converted by the hypothesis on `q`. -/
theorem rc_tt_gtU {q p s y y' : T} (hps : lt p s = true) (hc' : isOT (psi s y' z) = true)
    (hc : isOT (psi s y z) = true) (hy' : y' ≠ z)
    (hX' : isOT (psi p (H s y') z) = true) (hY : isOT (psi p (H s y) z) = true)
    (hRcs : RelRU U p (H s y') (H s y)) (hqp : ¬ lt p q = true)
    (hyp : ∀ u, U u → ¬ lt q u = true → ∀ d ∈ comps u p, d ≤ psi p z z ∨ d < H p (H s y') ∨ ∃ d' ∈ comps u q, d ≤ d') :
    RelRU U q (H p (H s y')) (H p (H s y)) := by
  have hθ : psi (succ p) z z ≤ psi s z z := by
    rcases (le_iff _ _).mp (succ_le_of_lt (show p < s from hps)) with h | h
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h))
    · rw [h]
  have hall : ∀ {w : T}, isOT (psi s w z) = true → ∀ q' ∈ summands (H s w), ¬ q' < psi (succ p) z z := by
    intro w hw q' hq'
    exact not_lt.mpr (le_trans hθ (le_trans (psi_le_psi_arg (z_le _)) (H_summands_ge hw q' hq')))
  rw [H_all_hi hX' (hall hc'), H_all_hi hY (hall hc)]
  rw [H_all_hi hX' (hall hc')] at hyp
  apply relR_of_le_qU hqp hRcs
  intro u hU hu d hd
  rcases hyp u hU hu d hd with h | h | h
  · left
    refine lt_of_le_of_lt h (lt_of_lt_of_le ?_ (om_le_H hc' hy'))
    exact psi_lt_psi_z_iff.mpr (Or.inl hps)
  · exact Or.inl h
  · exact Or.inr h


/-- Raising the bottom from `H p y′` to `hi′ + ψ_p(H p y′)` (a low part present). -/
theorem relR_HH_subU {p y' A : T} (hc' : isOT (psi p y' z) = true)
    (hlo : (split y' (psi (succ p) z z)).2 ≠ z) (hR : RelRU U p (H p y') A) :
    RelRU U p (app (split y' (psi (succ p) z z)).1 (psi p (H p y') z)) A := by
  have e := H_eq hc'
  rw [if_neg hlo] at e
  have hlt := y_lt_H hc' hlo
  have hb0 : H p y' < app (split y' (psi (succ p) z z)).1 (psi p (H p y') z) := by
    conv => lhs; rw [e]
    exact app_lt_app_left _ (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hlt⟩))
  apply relR_of_subU hR (le_of_lt hb0)
  intro u hU hu g hg
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · right; left; rw [e, comps_app]; exact List.mem_append_left _ hg
  · simp only [comps, List.mem_append] at hg
    rcases hg with hg | hg
    · rw [if_neg hu] at hg
      simp only [List.mem_cons, List.mem_append] at hg
      rcases hg with rfl | hg | hg
      · exact Or.inl hb0
      · exact Or.inr (Or.inl hg)
      · exact Or.inr (Or.inr ⟨g, hg, le_refl _⟩)
    · simp at hg


/-- **Both rewrite, `s = p`**: the double `H` keeps the relation (at the level `p`). -/
theorem relR_HHU {p y y' : T} (hc' : isOT (psi p y' z) = true) (hc : isOT (psi p y z) = true)
    (hX' : isOT (psi p (H p y') z) = true) (hY : isOT (psi p (H p y) z) = true) (hyy : y' < y)
    (hR : RelRU U p (H p y') (H p y)) (hL : LhdE (psi p (H p y') z) (psi p (H p y) z)) :
    RelRU U p (H p (H p y')) (H p (H p y)) := by
  rw [HH_form hc' hX', HH_form hc hY]
  set θ := psi (succ p) z z with hθ
  have ey' := H_eq hc'
  have ey := H_eq hc
  rcases split_mono θ hyy with hhi | ⟨hhi, hlo⟩
  · split_ifs with h1 h2 h2
    · exact hR
    · rw [if_pos h1, app_z_right] at ey'
      rw [if_neg h2] at ey
      refine relR_ext_prefixU hR (P := (split y θ).1) (by rw [ey']; exact hhi)
        (by rw [ey]; exact le_app_self _ _) ?_
      intro c hc1 hc2
      rw [ey] at hc1
      exact prefix_tests c hc1 hc2
    · rw [if_pos h2, app_z_right] at ey
      rw [ey]; rw [ey] at hR
      exact relR_HH_subU hc' h1 hR
    · rw [if_neg h2] at ey
      have h1' := relR_HH_subU hc' h1 hR
      refine relR_ext_prefixU h1' (P := (split y θ).1) ?_ (by rw [ey]; exact le_app_self _ _) ?_
      · exact app_lt_of_lt_hi hhi (split_fst_ge θ y) (Or.inr (head_psi_lt_succ p _))
      · intro c hc1 hc2
        rw [ey] at hc1
        exact prefix_tests c hc1 hc2
  · have hloz : (split y θ).2 ≠ z := by intro h; rw [h] at hlo; exact T.not_lt_z _ hlo
    rw [if_neg hloz]
    by_cases h1 : (split y' θ).2 = z
    · rw [if_pos h1]
      rw [if_pos h1, app_z_right] at ey'
      rw [ey', hhi]
      apply relR_self_prefixU
      intro c hc1 hc2
      exact prefix_tests (e := z) c (by rw [app_z_right]; exact hc1) hc2
    · rw [if_neg h1, hhi]
      exact relR_prefix_lhdEU hL


/-- **Only the old child rewrites, `B` a prefix of `hi(y)`.** The tests start with `B`; the components of
the new child are dominated through the test `ψ_s(B + 1)` of `ψ_s(y′) ◁ ψ_s(y)`, and the components of the
subscripts `s` and `p` are bounded by hypothesis. -/
theorem rc_tn_prefixU {q p B s y s' y' R : T}
    (hc : isOT (psi s y z) = true)
    (hl : Lhd z (psi s' y' z) (psi s y z))
    (hss : y' ≠ z → s' = s)
    (hn' : ¬ (lt B y' = true ∧ lt (psi p z z) (psi s' y' z) = true))
    (ht : lt B y = true ∧ lt (psi p z z) (psi s y z) = true)
    (hpre : (split y (psi (succ s) z z)).1 = app B R)
    (hX' : isOT (psi p (app B (psi s' y' z)) z) = true) (hY0 : isOT (psi p (H s y) z) = true)
    (hsubS : ∀ u, U u → ¬ lt q u = true → ∀ g ∈ comps u s,
      g < H p (app B (psi s' y' z)) ∨ ∃ d ∈ comps u q, g ≤ d)
    (hyp : ∀ u, U u → ¬ lt q u = true → ∀ d ∈ comps u p,
      d < H p (app B (psi s' y' z)) ∨ ∃ d' ∈ comps u q, d ≤ d') :
    RelRU U q (H p (app B (psi s' y' z))) (H p (H s y)) := by
  have has : p ≤ s := le_of_trig ht.2
  set c' := psi s' y' z with hc'def
  have hBhi : ∀ r ∈ summands B, ¬ r < psi (succ p) z z := by
    intro r hr h
    have h1 : ¬ r < psi (succ s) z z :=
      split_fst_ge _ y r (by rw [hpre, summands_app]; exact List.mem_append_left _ hr)
    have hθ : psi (succ p) z z ≤ psi (succ s) z z := psi_le_psi_z (succ_le_succ' has)
    exact h1 (lt_of_lt_of_le h hθ)
  -- `y′ = 0` or `y′ ≤ B`
  have hy'B : y' = z ∨ y' ≤ B := by
    by_cases hy : y' = z
    · exact Or.inl hy
    · right
      obtain rfl := hss hy
      have htr : lt (psi p z z) (psi s' y' z) = true := by
        show psi p z z < psi s' y' z
        rcases (le_iff _ _).mp has with h | rfl
        · exact psi_lt_psi_z_iff.mpr (Or.inl h)
        · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hy)⟩)
      exact not_lt.mp (fun h => hn' ⟨h, htr⟩)
  have hc'z : c' ≠ z := by simp [hc'def]
  have hy'lt : y' < app B c' := by
    rcases hy'B with rfl | h
    · cases B <;> simp [app, hc'def]
    · exact lt_of_le_of_lt h (lt_app_of hc'z)
  -- the form of the new state
  obtain ⟨e, hb, he⟩ : ∃ e, H p (app B c') = app B e ∧
      ((e = c' ∧ ¬ c' < psi (succ p) z z) ∨ (e = psi p (app B c') z ∧ c' < psi (succ p) z z)) := by
    by_cases hcθ : c' < psi (succ p) z z
    · exact ⟨_, H_hi_low hX' hBhi hc'z (by simpa [hc'def, head] using hcθ), Or.inr ⟨rfl, hcθ⟩⟩
    · refine ⟨c', H_all_hi hX' ?_, Or.inl ⟨rfl, hcθ⟩⟩
      intro r hr; rw [summands_app] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hBhi r hr
      · simp [summands, hc'def] at hr; rw [hr]; exact hcθ
  -- the form of the old state
  have eH := H_eq hc
  have ey : y = app B (app R (split y (psi (succ s) z z)).2) := by
    rw [← app_assoc, ← hpre]; exact (split_app _ y).symm
  obtain ⟨E, hA⟩ : ∃ E, H p (H s y) = app B E := by
    rcases (le_iff _ _).mp has with hps | rfl
    · have hθ : psi (succ p) z z ≤ psi s z z := by
        rcases (le_iff _ _).mp (succ_le_of_lt hps) with h | h
        · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h))
        · rw [h]
      have hall : ∀ r ∈ summands (H s y), ¬ r < psi (succ p) z z := fun r hr =>
        not_lt.mpr (le_trans hθ (le_trans (psi_le_psi_arg (z_le _)) (H_summands_ge hc r hr)))
      rw [H_all_hi hY0 hall, eH, hpre, app_assoc]; exact ⟨_, rfl⟩
    · rw [HH_form hc hY0]
      split_ifs
      · rw [eH, hpre, app_assoc]; exact ⟨_, rfl⟩
      · rw [hpre, app_assoc]; exact ⟨_, rfl⟩
  rw [hb, hA]
  rw [hb] at hsubS hyp
  -- the test `ψ_s(B + 1)`
  have hRne : app R (split y (psi (succ s) z z)).2 ≠ z := by
    intro h; rw [h, app_z_right] at ey
    have := ht.1; rw [← ey] at this; exact lt_irrefl' _ this
  have hone : app B one ≤ y := by
    rw [ey]; exact app_le_app_left B (one_le_of_ne_z hRne)
  have htest : c' < psi s (app B one) z := by
    rcases psi_lt_psi_z_iff.mp hl.1 with h | ⟨rfl, _⟩
    · exact psi_lt_psi_z_iff.mpr (Or.inl h)
    · rcases hy'B with rfl | h
      · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, by cases B <;> simp [app, one]⟩)
      · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_lt h (lt_app_of (by simp [one]))⟩)
  have htest2 : psi s (app B one) z ≤ psi s y z := psi_le_psi_arg hone
  have hone_e : one < e := by
    rcases he with ⟨rfl, hcθ⟩ | ⟨rfl, _⟩
    · exact lt_of_lt_of_le (one_lt_om_succ p) (not_lt.mp hcθ)
    · unfold one
      rcases lt_trichotomy' z p with h | rfl | h
      · exact psi_lt_psi_z_iff.mpr (Or.inl h)
      · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_lt (z_le _) (lt_app_of hc'z)⟩)
      · exact absurd h (T.not_lt_z _)
  have hb1 : app B one < app B e := app_lt_app_left B hone_e
  intro u hU hu cst h1 h2 g hg
  obtain ⟨c0, rfl, _, _⟩ := between_app h1 h2
  have hz : ∀ g, g ≤ z → ∃ d ∈ Gc u (app B c0) ++ comps u q, g ≤ d :=
    fun g h => ⟨z, List.mem_append_left _ List.mem_cons_self, h⟩
  have key : ∀ g ∈ comps u c', g < app B e ∨ ∃ d ∈ Gc u (app B c0) ++ comps u q, g ≤ d := by
    intro g hg
    obtain ⟨d, hd, hgd⟩ := hl.2 u _ htest htest2 g hg
    rcases List.mem_append.mp hd with hd | hd
    · simp only [comps, List.mem_append] at hd
      rcases hd with hd | hd
      · split at hd
        · simp at hd
        simp only [List.mem_cons, List.mem_append] at hd
        rcases hd with rfl | hd | hd
        · exact Or.inl (lt_of_le_of_lt hgd hb1)
        · rw [comps_app] at hd
          rcases List.mem_append.mp hd with hd | hd
          · exact Or.inr ⟨d, List.mem_append_left _ (gc_app_left d hd), hgd⟩
          · rw [mem_comps_one hd] at hgd; exact Or.inr (hz g hgd)
        · rcases hsubS u hU hu d hd with h | ⟨d', hd', hdd'⟩
          · exact Or.inl (lt_of_le_of_lt hgd h)
          · exact Or.inr ⟨d', List.mem_append_right _ hd', le_trans hgd hdd'⟩
      · simp at hd
    · simp [Gc, comps] at hd; subst hd; exact Or.inr (hz g hgd)
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩
  rcases he with ⟨rfl, _⟩ | ⟨rfl, hcθ⟩
  · exact key g hg
  · simp only [comps, List.mem_append] at hg
    rcases hg with hg | hg
    · split at hg
      · simp at hg
      simp only [List.mem_cons, List.mem_append] at hg
      rcases hg with rfl | hg | hg
      · left
        apply app_lt_app_left
        have hs'p : s' ≤ p := by
          have := lt_om_iff.mp hcθ
          rcases this with h | h
          · simp [hc'def] at h
          · simpa [lev, hc'def] using lt_succ_iff.mp h
        rcases (le_iff _ _).mp hs'p with h | rfl
        · exact psi_lt_psi_z_iff.mpr (Or.inl h)
        · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hy'lt⟩)
      · rw [comps_app] at hg
        rcases List.mem_append.mp hg with hg | hg
        · exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩
        · exact key g hg
      · rcases hyp u hU hu g hg with h | ⟨d', hd', hdd'⟩
        · exact Or.inl h
        · exact Or.inr ⟨d', List.mem_append_right _ hd', hdd'⟩
    · simp at hg


/-- **Only the old child rewrites, `B` a prefix of `hi(y)`** (core): the tests start with `B`, so the claim
holds when every component of the new child is below the new state, at most `0` or a component of `B`, or
dominated by `q` (`hkey`). -/
theorem rc_tn_coreU {q p B s y s' y' R : T}
    (hc : isOT (psi s y z) = true)
    (hc'c : psi s' y' z < psi s y z)
    (hc'p : psi s' y' z < psi (succ p) z z → psi s' y' z < psi p (app B (psi s' y' z)) z)
    (ht : lt B y = true ∧ lt (psi p z z) (psi s y z) = true)
    (hpre : (split y (psi (succ s) z z)).1 = app B R)
    (hX' : isOT (psi p (app B (psi s' y' z)) z) = true) (hY0 : isOT (psi p (H s y) z) = true)
    (hkey : ∀ u, U u → ¬ lt q u = true → ∀ g ∈ comps u (psi s' y' z),
      g < H p (app B (psi s' y' z)) ∨ g ≤ z ∨ (∃ d ∈ comps u B, g ≤ d) ∨ ∃ d ∈ comps u q, g ≤ d)
    (hyp : ∀ u, U u → ¬ lt q u = true → ∀ d ∈ comps u p,
      d < H p (app B (psi s' y' z)) ∨ ∃ d' ∈ comps u q, d ≤ d') :
    RelRU U q (H p (app B (psi s' y' z))) (H p (H s y)) := by
  have has : p ≤ s := le_of_trig ht.2
  set c' := psi s' y' z with hc'def
  have hBhi : ∀ r ∈ summands B, ¬ r < psi (succ p) z z := by
    intro r hr h
    have h1 : ¬ r < psi (succ s) z z :=
      split_fst_ge _ y r (by rw [hpre, summands_app]; exact List.mem_append_left _ hr)
    have hθ : psi (succ p) z z ≤ psi (succ s) z z := psi_le_psi_z (succ_le_succ' has)
    exact h1 (lt_of_lt_of_le h hθ)
  have hc'z : c' ≠ z := by simp [hc'def]
  -- the form of the new state
  obtain ⟨e, hb, he⟩ : ∃ e, H p (app B c') = app B e ∧
      ((e = c' ∧ ¬ c' < psi (succ p) z z) ∨ (e = psi p (app B c') z ∧ c' < psi (succ p) z z)) := by
    by_cases hcθ : c' < psi (succ p) z z
    · exact ⟨_, H_hi_low hX' hBhi hc'z (by simpa [hc'def, head] using hcθ), Or.inr ⟨rfl, hcθ⟩⟩
    · refine ⟨c', H_all_hi hX' ?_, Or.inl ⟨rfl, hcθ⟩⟩
      intro r hr; rw [summands_app] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hBhi r hr
      · simp [summands, hc'def] at hr; rw [hr]; exact hcθ
  -- the form of the old state
  have eH := H_eq hc
  have ey : y = app B (app R (split y (psi (succ s) z z)).2) := by
    rw [← app_assoc, ← hpre]; exact (split_app _ y).symm
  obtain ⟨E, hA⟩ : ∃ E, H p (H s y) = app B E := by
    rcases (le_iff _ _).mp has with hps | rfl
    · have hθ : psi (succ p) z z ≤ psi s z z := by
        rcases (le_iff _ _).mp (succ_le_of_lt hps) with h | h
        · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h))
        · rw [h]
      have hall : ∀ r ∈ summands (H s y), ¬ r < psi (succ p) z z := fun r hr =>
        not_lt.mpr (le_trans hθ (le_trans (psi_le_psi_arg (z_le _)) (H_summands_ge hc r hr)))
      rw [H_all_hi hY0 hall, eH, hpre, app_assoc]; exact ⟨_, rfl⟩
    · rw [HH_form hc hY0]
      split_ifs
      · rw [eH, hpre, app_assoc]; exact ⟨_, rfl⟩
      · rw [hpre, app_assoc]; exact ⟨_, rfl⟩
  rw [hb, hA]
  rw [hb] at hkey hyp
  have hone_e : one < e := by
    rcases he with ⟨rfl, hcθ⟩ | ⟨rfl, _⟩
    · exact lt_of_lt_of_le (one_lt_om_succ p) (not_lt.mp hcθ)
    · unfold one
      rcases lt_trichotomy' z p with h | rfl | h
      · exact psi_lt_psi_z_iff.mpr (Or.inl h)
      · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_lt (z_le _) (lt_app_of hc'z)⟩)
      · exact absurd h (T.not_lt_z _)
  have hb1 : app B one < app B e := app_lt_app_left B hone_e
  intro u hU hu cst h1 h2 g hg
  obtain ⟨c0, rfl, _, _⟩ := between_app h1 h2
  have hz : ∀ g, g ≤ z → ∃ d ∈ Gc u (app B c0) ++ comps u q, g ≤ d :=
    fun g h => ⟨z, List.mem_append_left _ List.mem_cons_self, h⟩
  have key : ∀ g ∈ comps u c', g < app B e ∨ ∃ d ∈ Gc u (app B c0) ++ comps u q, g ≤ d := by
    intro g hg
    rcases hkey u hU hu g hg with h | h | ⟨d, hd, hgd⟩ | ⟨d, hd, hgd⟩
    · exact Or.inl h
    · exact Or.inr (hz g h)
    · exact Or.inr ⟨d, List.mem_append_left _ (gc_app_left d hd), hgd⟩
    · exact Or.inr ⟨d, List.mem_append_right _ hd, hgd⟩
  rw [comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩
  rcases he with ⟨rfl, _⟩ | ⟨rfl, hcθ⟩
  · exact key g hg
  · simp only [comps, List.mem_append] at hg
    rcases hg with hg | hg
    · split at hg
      · simp at hg
      simp only [List.mem_cons, List.mem_append] at hg
      rcases hg with rfl | hg | hg
      · exact Or.inl (app_lt_app_left B (hc'p hcθ))
      · rw [comps_app] at hg
        rcases List.mem_append.mp hg with hg | hg
        · exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩
        · exact key g hg
      · rcases hyp u hU hu g hg with h | ⟨d', hd', hdd'⟩
        · exact Or.inl h
        · exact Or.inr ⟨d', List.mem_append_right _ hd', hdd'⟩
    · simp at hg


/-- **Neither child rewrites.** `X′ = B + c′`, `Y₀ = B + c`. Below `Ω_{p+1}` the parent relation `hN` gives
the claim after the high part of `B`; above, the tests start with `B` and the child relation `hchild`
dominates the components of `c′`. -/
theorem rc_nnU {q p B s y s' y' : T}
    (hc'c : psi s' y' z < psi s y z) (hBc : ∀ r ∈ summands B, psi s y z ≤ r)
    (hX' : isOT (psi p (app B (psi s' y' z)) z) = true) (hY0 : isOT (psi p (app B (psi s y z)) z) = true)
    (hN : LhdE (psi p (app B (psi s' y' z)) z) (psi p (app B (psi s y z)) z))
    (hchild : ∀ c0, psi s' y' z < c0 → c0 ≤ psi s y z → ∀ u, U u → ¬ lt q u = true → ∀ g ∈ comps u (psi s' y' z),
      g < app B (psi s' y' z) ∨ (∃ d ∈ Gc u c0, g ≤ d) ∨ ∃ d ∈ comps u p, g ≤ d)
    (hc'p : psi s' y' z < psi (succ p) z z → psi s' y' z < psi p (app B (psi s' y' z)) z)
    (hyp : ∀ u, U u → ¬ lt q u = true → ∀ d ∈ comps u p,
      d < H p (app B (psi s' y' z)) ∨ ∃ d' ∈ comps u q, d ≤ d') :
    RelRU U q (H p (app B (psi s' y' z))) (H p (app B (psi s y z))) := by
  set θ := psi (succ p) z z with hθ
  set c := psi s y z with hcdef
  set c' := psi s' y' z with hc'def
  by_cases hcθ : c < θ
  · -- below `Ω_{p+1}`: after the high part of `B`
    have hc'θ : c' < θ := lt_trans hc'c hcθ
    set P := (split B θ).1
    set L := (split B θ).2
    have eB : app P L = B := split_app θ B
    have hP : ∀ r ∈ summands P, ¬ r < θ := split_fst_ge θ B
    have hL : L = z ∨ head L < θ := split_snd_head θ B
    have hform : ∀ {t : T}, t = psi s' y' z ∨ t = psi s y z → t < θ → isOT (psi p (app B t) z) = true →
        H p (app B t) = app P (psi p (app B t) z) := by
      intro t ht htθ hot
      have ht0 : t ≠ z := by rcases ht with rfl | rfl <;> simp
      have htl : head t < θ := by rcases ht with rfl | rfl <;> simpa [head] using htθ
      obtain ⟨hr0, hrl⟩ := head_app_low hL htl ht0
      have e : app B t = app P (app L t) := by rw [← eB, app_assoc]
      rw [e] at hot ⊢
      exact H_hi_low hot hP hr0 hrl
    rw [hform (Or.inl rfl) hc'θ hX', hform (Or.inr rfl) hcθ hY0]
    exact relR_prefix_lhdEU hN
  · -- above: `B` is all high and `H p (B + c) = B + c`
    have hcθ' : θ ≤ c := not_lt.mp hcθ
    have hBhi : ∀ r ∈ summands B, ¬ r < θ := fun r hr => not_lt.mpr (le_trans hcθ' (hBc r hr))
    have hallY : ∀ r ∈ summands (app B c), ¬ r < θ := by
      intro r hr; rw [summands_app] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hBhi r hr
      · simp [summands, hcdef] at hr; rw [hr]; exact hcθ
    rw [H_all_hi hY0 hallY]
    -- the tests start with `B` and their tail is above `c′`
    have hdomc' : ∀ u (c0 : T), U u → ¬ lt q u = true → c' < c0 → c0 ≤ c → ∀ g ∈ comps u c',
        g < H p (app B c') ∨ ∃ d ∈ Gc u (app B c0) ++ comps u q, g ≤ d := by
      intro u c0 hU hu h1 h2 g hg
      rcases hchild c0 h1 h2 u hU hu g hg with h | ⟨d, hd, hgd⟩ | ⟨d, hd, hgd⟩
      · exact Or.inl (lt_of_lt_of_le h (le_H hX'))
      · exact Or.inr ⟨d, List.mem_append_left _ (gc_app_right d hd), hgd⟩
      · rcases hyp u hU hu d hd with h | ⟨d', hd', hdd'⟩
        · exact Or.inl (lt_of_le_of_lt hgd h)
        · exact Or.inr ⟨d', List.mem_append_right _ hd', le_trans hgd hdd'⟩
    by_cases hc'θ : c' < θ
    · have hc'z : c' ≠ z := by simp [hc'def]
      have hb : H p (app B c') = app B (psi p (app B c') z) :=
        H_hi_low hX' hBhi hc'z (by simpa [hc'def, head] using hc'θ)
      rw [hb]; rw [hb] at hyp
      have hc'p' := hc'p hc'θ
      have hXb : app B c' < app B (psi p (app B c') z) := app_lt_app_left B hc'p'
      intro u hU hu cst h1 h2 g hg
      obtain ⟨c0, rfl, hc1, hc2⟩ := between_app h1 h2
      have hc0 : c' < c0 := lt_trans hc'p' hc1
      rw [comps_app] at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩
      simp only [comps, List.mem_append] at hg
      rcases hg with hg | hg
      · split at hg
        · simp at hg
        simp only [List.mem_cons, List.mem_append] at hg
        rcases hg with rfl | hg | hg
        · exact Or.inl hXb
        · rw [comps_app] at hg
          rcases List.mem_append.mp hg with hg | hg
          · exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩
          · rcases hdomc' u c0 hU hu hc0 hc2 g hg with h | h
            · rw [hb] at h; exact Or.inl h
            · exact Or.inr h
        · rcases hyp u hU hu g hg with h | ⟨d', hd', hdd'⟩
          · exact Or.inl h
          · exact Or.inr ⟨d', List.mem_append_right _ hd', hdd'⟩
      · simp at hg
    · have hallX : ∀ r ∈ summands (app B c'), ¬ r < θ := by
        intro r hr; rw [summands_app] at hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hBhi r hr
        · simp [summands, hc'def] at hr; rw [hr]; exact hc'θ
      rw [H_all_hi hX' hallX]
      intro u hU hu cst h1 h2 g hg
      obtain ⟨c0, rfl, hc1, hc2⟩ := between_app h1 h2
      rw [comps_app] at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact Or.inr ⟨g, List.mem_append_left _ (gc_app_left g hg), le_refl _⟩
      · rcases hdomc' u c0 hU hu hc1 hc2 g hg with h | h
        · rw [H_all_hi hX' hallX] at h; exact Or.inl h
        · exact Or.inr h


/-- **A closed new state** (up to the components of `a`) is in the relation with anything. -/
theorem relR_of_closedU {q a X A : T} (hX : isOT (psi a X z) = true) (hqa : ¬ lt a q = true)
    (hcl : ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u X, g < X ∨ ∃ d ∈ comps u a, g ≤ d)
    (hyp : ∀ u, U u → ¬ lt q u = true → ∀ d ∈ comps u a, d < H a X ∨ ∃ d' ∈ comps u q, d ≤ d') :
    RelRU U q (H a X) A := by
  intro u hU hu c _ _ g hg
  have hau : ¬ lt a u = true := fun h => hu (lt_of_le_of_lt (not_lt.mp hqa) (show a < u from h))
  have hXH : X ≤ H a X := le_H hX
  have hsub : ∀ g ∈ comps u X, g < H a X ∨ ∃ d ∈ Gc u c ++ comps u q, g ≤ d := by
    intro g hg
    rcases hcl u hU hau g hg with h | ⟨d, hd, hgd⟩
    · exact Or.inl (lt_of_lt_of_le h hXH)
    · rcases hyp u hU hu d hd with h | ⟨d', hd', hdd'⟩
      · exact Or.inl (lt_of_le_of_lt hgd h)
      · exact Or.inr ⟨d', List.mem_append_right _ hd', le_trans hgd hdd'⟩
  rw [H_eq hX, comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · apply hsub; rw [← split_app (psi (succ a) z z) X, comps_app]; exact List.mem_append_left _ hg
  · split at hg
    · simp [comps] at hg
    · rename_i hlo
      have hXlt : X < H a X := y_lt_H hX hlo
      rw [comps_psi_z_of_ge hau] at hg
      simp only [List.mem_cons, List.mem_append] at hg
      rcases hg with rfl | hg | hg
      · exact Or.inl hXlt
      · exact hsub g hg
      · rcases hyp u hU hu g hg with h | ⟨d', hd', hdd'⟩
        · exact Or.inl h
        · exact Or.inr ⟨d', List.mem_append_right _ hd', hdd'⟩


/-- **Both rewrite, same high part**: the claim follows from `ψ_s(y′) ◁ ψ_s(y)` after the common high part. -/
theorem relR_H_samehiU {q s y y' : T} (hc' : isOT (psi s y' z) = true) (hc : isOT (psi s y z) = true)
    (hl : LhdE (psi s y' z) (psi s y z))
    (hhi : (split y' (psi (succ s) z z)).1 = (split y (psi (succ s) z z)).1)
    (hlo : (split y' (psi (succ s) z z)).2 < (split y (psi (succ s) z z)).2) :
    RelRU U q (H s y') (H s y) := by
  have hloz : (split y (psi (succ s) z z)).2 ≠ z := by
    intro h; rw [h] at hlo; exact T.not_lt_z _ hlo
  rw [H_eq hc', H_eq hc, if_neg hloz, hhi]
  by_cases h' : (split y' (psi (succ s) z z)).2 = z
  · rw [if_pos h', app_z_right]
    apply relR_self_prefixU
    intro c hc1 hc2
    exact prefix_tests (e := z) c (by rw [app_z_right]; exact hc1) hc2
  · rw [if_neg h']; exact relR_prefix_lhdEU hl


/-- **Only the old child rewrites, `B = hi(y)`**: the claim follows from the frame relation `hN` or the child
relation, after `B`. -/
theorem rc_tn_hiU {q p B s y y' : T}
    (hc : isOT (psi s y z) = true) (hl : Lhd z (psi s y' z) (psi s y z))
    (ht : lt B y = true ∧ lt (psi p z z) (psi s y z) = true)
    (hpre : (split y (psi (succ s) z z)).1 = B)
    (hX' : isOT (psi p (app B (psi s y' z)) z) = true) (hY0 : isOT (psi p (H s y) z) = true)
    (hN : LhdE (psi p (app B (psi s y' z)) z) (psi p (H s y) z)) :
    RelRU U q (H p (app B (psi s y' z))) (H p (H s y)) := by
  have has : p ≤ s := le_of_trig ht.2
  have hlo : (split y (psi (succ s) z z)).2 ≠ z := by
    intro h
    have e := split_app (psi (succ s) z z) y
    rw [h, app_z_right, hpre] at e
    have := ht.1; rw [e] at this; exact lt_irrefl' _ this
  have eH : H s y = app B (psi s y z) := by rw [H_eq hc, if_neg hlo, hpre]
  have hBhs : ∀ r ∈ summands B, ¬ r < psi (succ s) z z := by
    rw [← hpre]; exact split_fst_ge _ y
  have hBhp : ∀ r ∈ summands B, ¬ r < psi (succ p) z z := fun r hr h =>
    hBhs r hr (lt_of_lt_of_le h (psi_le_psi_z (succ_le_succ' has)))
  rw [eH] at hY0 hN ⊢
  rcases (le_iff _ _).mp has with hps | rfl
  · -- `p < s`: both states are all high
    have hθ : psi (succ p) z z ≤ psi s z z := by
      rcases (le_iff _ _).mp (succ_le_of_lt hps) with h | h
      · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h))
      · rw [h]
    have hall : ∀ w, ∀ r ∈ summands (app B (psi s w z)), ¬ r < psi (succ p) z z := by
      intro w r hr
      rw [summands_app] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hBhp r hr
      · simp [summands] at hr; rw [hr]
        exact not_lt.mpr (le_trans hθ (psi_le_psi_arg (z_le _)))
    rw [H_all_hi hX' (hall y'), H_all_hi hY0 (hall y)]
    exact relR_prefix_lhdU hl
  · -- `s = p`
    rw [H_hi_low hX' hBhp (by simp) (head_psi_lt_succ p y'),
      H_hi_low hY0 hBhp (by simp) (head_psi_lt_succ p y)]
    exact relR_prefix_lhdEU hN


/-- **Only the old child rewrites, `B = hi(y)`, a new subscript `s′ > p`**: both states are all high
(`Ω_{p+1} ≤ ψ_{s′}(y′)`), so the claim is the child's `◁` after `B`. -/
theorem rc_tn_hi_upU {q p B s y s' y' : T}
    (hc : isOT (psi s y z) = true) (hl : Lhd z (psi s' y' z) (psi s y z))
    (ht : lt B y = true ∧ lt (psi p z z) (psi s y z) = true)
    (hpre : (split y (psi (succ s) z z)).1 = B) (hps' : p < s')
    (hX' : isOT (psi p (app B (psi s' y' z)) z) = true) (hY0 : isOT (psi p (H s y) z) = true) :
    RelRU U q (H p (app B (psi s' y' z))) (H p (H s y)) := by
  have has : p ≤ s := le_of_trig ht.2
  have hlo : (split y (psi (succ s) z z)).2 ≠ z := by
    intro h
    have e := split_app (psi (succ s) z z) y
    rw [h, app_z_right, hpre] at e
    have := ht.1; rw [e] at this; exact lt_irrefl' _ this
  have eH : H s y = app B (psi s y z) := by rw [H_eq hc, if_neg hlo, hpre]
  have hBhs : ∀ r ∈ summands B, ¬ r < psi (succ s) z z := by
    rw [← hpre]; exact split_fst_ge _ y
  have hBhp : ∀ r ∈ summands B, ¬ r < psi (succ p) z z := fun r hr h =>
    hBhs r hr (lt_of_lt_of_le h (psi_le_psi_z (succ_le_succ' has)))
  have hθ' : ∀ w, psi (succ p) z z ≤ psi w z z → ∀ v, psi (succ p) z z ≤ psi w v z := fun w h v =>
    le_trans h (psi_le_psi_arg (z_le _))
  have hs'le : psi (succ p) z z ≤ psi s' z z := by
    rcases (le_iff _ _).mp (succ_le_of_lt hps') with h | h
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h))
    · rw [h]
  have hs's : s' ≤ s := by
    rcases psi_lt_psi_z_iff.mp hl.1 with h | ⟨h, _⟩
    · exact le_of_lt h
    · rw [h]
  have hsle : psi (succ p) z z ≤ psi s z z := by
    have hps : p < s := lt_of_lt_of_le hps' hs's
    rcases (le_iff _ _).mp (succ_le_of_lt hps) with h | h
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl h))
    · rw [h]
  have hall : ∀ w v, psi (succ p) z z ≤ psi w z z →
      ∀ r ∈ summands (app B (psi w v z)), ¬ r < psi (succ p) z z := by
    intro w v hw r hr
    rw [summands_app] at hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hBhp r hr
    · simp [summands] at hr; rw [hr]
      exact not_lt.mpr (hθ' w hw v)
  rw [eH] at hY0 ⊢
  rw [H_all_hi hX' (hall s' y' hs'le), H_all_hi hY0 (hall s y hsle)]
  exact relR_prefix_lhdU hl


/-- **One frame step of the claim `RelRU U`** for the parent `ψ_a` of the last counted child (old `ψ_s(y)`,
new `ψ_{s′}(y′)`): both rewrite (from the child's claim `hRC`), neither (from the frame relation `hN`), only
the old (prefix of `hi(y)` from the child's `◁`, else the closedness `hSh`), a weak child. The subscript
bounds `hVR` (old child) and `hVNR` (a changed subscript) are needed only when the old child rewrites. -/
theorem relR_frameU {q a B s y s' y' : T}
    (hc : isOT (psi s y z) = true) (hc' : isOT (psi s' y' z) = true)
    (hBc : ∀ r ∈ summands B, psi s y z ≤ r)
    (hrel : (LhdE (psi s' y' z) (psi s y z) ∧ (y' ≠ z → s' = s)) ∨ (y' = z ∧ y = z ∧ WkVA s' s ∧ WCS a s'))
    (hX' : isOT (psi a (step a B s' y' z) z) = true) (hY0 : isOT (psi a (step a B s y z) z) = true)
    (hN : LhdE (psi a (step a B s' y' z) z) (psi a (step a B s y z) z))
    (hRC : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → s' = s → ∀ q', ¬ lt s q' = true →
      (∀ u, U u → ¬ lt q' u = true → ∀ g ∈ comps u s, g ≤ psi s z z ∨ g < H s y' ∨ ∃ d ∈ comps u q', g ≤ d) →
      RelRU U q' (H s y') (H s y))
    (hVR : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → (split y (psi (succ s) z z)).1 ≠ z →
      ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u s, g ≤ psi s z z ∨ g ≤ B ∨ ∃ d ∈ comps u a, g ≤ d)
    (hVNR : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) → s' ≠ s →
      ¬ ((split y (psi (succ s) z z)).1 = B ∧ a < s') → ∀ u, U u → ¬ lt a u = true →
      ∀ g ∈ comps u s', g ≤ psi s' z z ∨ g ≤ B ∨ ∃ d ∈ comps u a, g ≤ d)
    (hSh : (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) →
      ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) →
      (¬ ∃ R, (split y (psi (succ s) z z)).1 = app B R) →
      ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u (app B (psi s' y' z)),
        g < app B (psi s' y' z) ∨ ∃ d ∈ comps u a, g ≤ d)
    (hqa : ¬ lt a q = true)
    (hyp : ∀ u, U u → ¬ lt q u = true → ∀ g ∈ comps u a,
      g ≤ psi a z z ∨ g < H a (step a B s' y' z) ∨ ∃ d ∈ comps u q, g ≤ d) :
    RelRU U q (H a (step a B s' y' z)) (H a (step a B s y z)) := by
  have hXz : step a B s' y' z ≠ z := step_ne_z hc'
  have hyp' : ∀ u, U u → ¬ lt q u = true → ∀ d ∈ comps u a,
      d < H a (step a B s' y' z) ∨ ∃ d' ∈ comps u q, d ≤ d' := by
    intro u hU hu d hd
    rcases hyp u hU hu d hd with h | h | h
    · exact Or.inl (lt_of_le_of_lt h (om_lt_H hX' hXz))
    · exact Or.inl h
    · exact Or.inr h
  have hau : ∀ u, U u → ¬ lt q u = true → ¬ lt a u = true :=
    fun u hU hu h => hu (lt_of_le_of_lt (not_lt.mp hqa) (show a < u from h))
  have hc'z : psi s' y' z ≠ z := by simp
  have hc'c : psi s' y' z ≤ psi s y z := by
    rcases hrel with ⟨h, _⟩ | ⟨rfl, rfl, hw⟩
    · exact h.le
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inl hw.1.1))
  have hBc' : ∀ r ∈ summands B, psi s' y' z ≤ r := fun r hr => le_trans hc'c (hBc r hr)
  have happ' : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true) →
      step a B s' y' z = app B (psi s' y' z) := by
    intro hn; unfold step; rw [if_neg hn]; exact add_eq_app_of_ge ⟨s', y', rfl⟩ B hBc'
  have happ : ¬ (lt B y = true ∧ lt (psi a z z) (psi s y z) = true) →
      step a B s y z = app B (psi s y z) := by
    intro hn; unfold step; rw [if_neg hn]; exact add_eq_app_of_ge ⟨s, y, rfl⟩ B hBc
  rcases hrel with ⟨hle, hss⟩ | ⟨rfl, rfl, hwk⟩
  · rcases hle with heq | hl
    · simp only [psi.injEq] at heq; obtain ⟨rfl, rfl, -⟩ := heq; exact relR_reflU _ _
    by_cases ht' : lt B y' = true ∧ lt (psi a z z) (psi s' y' z) = true
    · -- both rewrite
      obtain rfl := hss (ne_z_of_lt ht'.1)
      have hyy : y' < y := by
        rcases psi_lt_psi_z_iff.mp hl.1 with h | ⟨_, h⟩
        · exact absurd h (lt_irrefl' _)
        · exact h
      have ht : lt B y = true ∧ lt (psi a z z) (psi s' y z) = true :=
        ⟨lt_trans (show B < y' from ht'.1) hyy, lt_trans (show psi a z z < psi s' y' z from ht'.2) hl.1⟩
      have e' : step a B s' y' z = H s' y' := by unfold step; rw [if_pos ht']
      have e : step a B s' y z = H s' y := by unfold step; rw [if_pos ht]
      rw [e'] at hX' hyp hyp'
      rw [e] at hY0
      rw [e', e] at hN ⊢
      rcases (le_iff _ _).mp (le_of_trig ht.2) with hlt | rfl
      · apply rc_tt_gtU hlt hc' hc (ne_z_of_lt ht'.1) hX' hY0 _ hqa hyp
        rcases split_mono (psi (succ s') z z) hyy with hhi | ⟨hhi, hlo⟩
        · apply hRC ht rfl a (fun h => lt_irrefl' _ (lt_trans (show a < s' from hlt) h))
          have hhz : (split y (psi (succ s') z z)).1 ≠ z := by
            intro h; rw [h] at hhi; exact T.not_lt_z _ hhi
          intro u hU hu g hg
          rcases hVR ht hhz u hU hu g hg with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (lt_of_le_of_lt h (lt_of_lt_of_le ht'.1 (le_H hc'))))
          · exact Or.inr (Or.inr h)
        · exact relR_H_samehiU hc' hc (Or.inr hl) hhi hlo
      · have hR := hRC ht rfl a (lt_irrefl' _) (fun u _ _ g hg => Or.inr (Or.inr ⟨g, hg, le_refl _⟩))
        exact relR_of_le_qU hqa (relR_HHU hc' hc hX' hY0 hyy hR hN) hyp'
    by_cases ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true
    · -- only the old child rewrites
      have e : step a B s y z = H s y := by unfold step; rw [if_pos ht]
      rw [happ' ht'] at hX' hyp' ⊢
      rw [e] at hY0
      rw [e]
      rw [happ' ht', e] at hN
      by_cases hpre : ∃ R, (split y (psi (succ s) z z)).1 = app B R
      · obtain ⟨R, hR⟩ := hpre
        have hH : app B (psi s' y' z) ≤ H a (app B (psi s' y' z)) := le_H hX'
        by_cases hs : s' = s
        · subst hs
          by_cases hR0 : R = z
          · rw [hR0, app_z_right] at hR
            exact rc_tn_hiU hc hl ht hR hX' hY0 hN
          have hhz : (split y (psi (succ s') z z)).1 ≠ z := by
            rw [hR]; intro h; exact hR0 (app_eq_z h).2
          refine rc_tn_prefixU hc hl hss ht' ht hR hX' hY0 ?_ hyp'
          intro u hU hu g hg
          rcases hVR ht hhz u hU (hau u hU hu) g hg with h | h | ⟨d, hd, hgd⟩
          · left
            refine lt_of_lt_of_le (lt_of_le_of_ne h (size_ne_om hg)) (le_trans ?_ hH)
            exact le_trans (psi_le_psi_arg (z_le _)) (le_app_psi hBc')
          · exact Or.inl (lt_of_le_of_lt h (lt_of_lt_of_le (lt_app_of hc'z) hH))
          · rcases hyp' u hU hu d hd with h' | h'
            · exact Or.inl (lt_of_le_of_lt hgd h')
            · obtain ⟨d', hd', hdd'⟩ := h'
              exact Or.inr ⟨d', hd', le_trans hgd hdd'⟩
        · have hy0 : y' = z := by by_contra h; exact hs (hss h)
          subst hy0
          by_cases hup : (split y (psi (succ s) z z)).1 = B ∧ a < s'
          · exact rc_tn_hi_upU hc hl ht hup.1 hup.2 hX' hY0
          refine rc_tn_coreU hc hl.1 (fun hθ => psi_lt_psi_app hθ (z_lt_app_psi _ _ _)) ht hR hX' hY0 ?_ hyp'
          intro u hU hu g hg
          simp only [comps, List.mem_append] at hg
          rcases hg with hg | hg
          · split at hg
            · simp at hg
            simp only [List.mem_cons, List.mem_append] at hg
            rcases hg with rfl | hg | hg
            · exact Or.inr (Or.inl (le_refl _))
            · simp [comps] at hg
            · rcases hVNR ht hs hup u hU (hau u hU hu) g hg with h | h | ⟨d, hd, hgd⟩
              · left
                refine lt_of_lt_of_le (lt_of_le_of_ne h (size_ne_om hg)) (le_trans ?_ hH)
                exact le_app_psi hBc'
              · exact Or.inl (lt_of_le_of_lt h (lt_of_lt_of_le (lt_app_of hc'z) hH))
              · rcases hyp' u hU hu d hd with h' | h'
                · exact Or.inl (lt_of_le_of_lt hgd h')
                · obtain ⟨d', hd', hdd'⟩ := h'
                  exact Or.inr (Or.inr (Or.inr ⟨d', hd', le_trans hgd hdd'⟩))
          · simp [comps] at hg
      · exact relR_of_closedU hX' hqa (hSh ht ht' hpre) hyp'
    · -- neither rewrites
      rw [happ' ht'] at hX' hyp'
      rw [happ ht] at hY0
      rw [happ' ht', happ ht] at hN ⊢
      have hc'lt : psi s' y' z < psi s y z := hl.1
      refine rc_nnU hc'lt hBc hX' hY0 hN ?_ ?_ hyp'
      · intro c0 h1 h2 u _ _ g hg
        obtain ⟨d, hd, hgd⟩ := hl.2 u c0 h1 h2 g hg
        right; left
        rcases List.mem_append.mp hd with hd | hd
        · exact ⟨d, List.mem_cons_of_mem _ hd, hgd⟩
        · simp [Gc, comps] at hd; subst hd; exact ⟨z, List.mem_cons_self, hgd⟩
      · intro hθ
        rcases (le_iff _ _).mp (sub_le_of_lt_om hθ) with h | rfl
        · exact psi_lt_psi_z_iff.mpr (Or.inl h)
        · apply psi_lt_psi_z_iff.mpr; right; refine ⟨rfl, ?_⟩
          by_cases hy : y' = z
          · rw [hy]; exact z_lt_app_psi _ _ _
          · have hs'a : lt (psi s' z z) (psi s' y' z) = true :=
              psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hy)⟩)
            have hyB : y' ≤ B := not_lt.mp (fun h => ht' ⟨h, hs'a⟩)
            exact lt_of_le_of_lt hyB (lt_app_of hc'z)
  · -- weak child
    have hn' : ¬ (lt B z = true ∧ lt (psi a z z) (psi s' z z) = true) := fun h => T.not_lt_z _ h.1
    have hn : ¬ (lt B z = true ∧ lt (psi a z z) (psi s z z) = true) := fun h => T.not_lt_z _ h.1
    rw [happ' hn'] at hX' hyp'
    rw [happ hn] at hY0
    rw [happ' hn', happ hn] at hN ⊢
    refine rc_nnU (psi_lt_psi_z_iff.mpr (Or.inl hwk.1.1)) hBc hX' hY0 hN ?_ ?_ hyp'
    · intro c0 _ _ u hU hu g hg
      rcases self_small_weakA hwk.2 hwk.1.2.1 u (hau u hU hu) g hg with h1 | h1
      · left
        have hne : g ≠ psi s' z z := by
          intro h; have := size_comps hg; rw [h] at this; omega
        exact lt_of_lt_of_le (lt_of_le_of_ne h1 hne) (le_app_psi hBc')
      · right; right; exact h1
    · intro hθ; exact psi_lt_psi_app hθ (z_lt_app_psi _ _ _)


/-- **A non-rewriting tail `T` only raises the top** (general form of `relR_tlU`). -/
theorem relR_tailU {q p b Y0 T0 : T} (hR : RelRU U q b (H p Y0)) (hb : b ≤ H p Y0)
    (hY0 : isOT (psi p Y0 z) = true) (hY : isOT (psi p (app Y0 T0) z) = true) (hT0 : T0 ≠ z)
    (hge : ∀ q' ∈ summands Y0, head T0 ≤ q') :
    RelRU U q b (H p (app Y0 T0)) := by
  apply relR_ext_domU hR hb
  intro u c h1 h2 d hd
  set θ := psi (succ p) z z with hθ
  set P := (split Y0 θ).1 with hPdef
  set L := (split Y0 θ).2 with hLdef
  have eY0 : app P L = Y0 := split_app θ Y0
  have hP : ∀ r ∈ summands P, ¬ r < θ := split_fst_ge θ Y0
  have hL : L = z ∨ head L < θ := split_snd_head θ Y0
  have hHY0 := H_eq hY0
  rw [← hPdef, ← hLdef] at hHY0
  by_cases hL0 : L = z
  · -- `Y0` is all high: the tests start with `Y0`
    rw [if_pos hL0, app_z_right] at hHY0
    have hY0P : Y0 = P := by rw [← eY0, hL0, app_z_right]
    have hallY0 : ∀ r ∈ summands Y0, ¬ r < θ := by rw [hY0P]; exact hP
    have hHY := H_eq hY
    have hs := split_app_hi (θ := θ) (B := Y0) T0 hallY0
    rw [hs] at hHY
    rw [hHY, app_assoc] at h2
    rw [hHY0, ← hY0P] at h1 hd
    obtain ⟨c0, rfl, _, _⟩ := between_app (A := Y0) (x := z) (by rw [app_z_right]; exact h1) h2
    unfold Gc at hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨z, List.mem_cons_self, le_refl _⟩
    · exact ⟨d, gc_app_left d hd, le_refl _⟩
  · -- `Y0` has a low part, so `T0` is low
    have hlast : ∃ r ∈ summands Y0, r < θ := by
      rcases hL with h | h
      · exact absurd h hL0
      · exact ⟨head L, split_snd_suffix Y0 _ (head_mem_summands hL0), h⟩
    obtain ⟨r, hr, hrθ⟩ := hlast
    have hT0θ : head T0 < θ := lt_of_le_of_lt (hge r hr) hrθ
    have eY : app Y0 T0 = app P (app L T0) := by rw [← eY0, app_assoc]
    obtain ⟨hr0, hrl⟩ := head_app_low hL hT0θ hT0
    have hHY : H p (app Y0 T0) = app P (psi p (app Y0 T0) z) := by
      rw [eY] at hY ⊢; exact H_hi_low hY hP hr0 hrl
    rw [hHY] at h2
    rw [if_neg hL0] at hHY0
    rw [hHY0] at h1 hd
    obtain ⟨c0, rfl, hc1, hc2⟩ := between_app h1 h2
    obtain ⟨W, c1, rfl, hW1, hW2⟩ := between_psi hc1 hc2
    unfold Gc at hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨z, List.mem_cons_self, le_refl _⟩
    rw [comps_app] at hd
    rcases List.mem_append.mp hd with hd | hd
    · exact ⟨d, gc_app_left d hd, le_refl _⟩
    simp only [comps, List.mem_append] at hd
    rcases hd with hd | hd
    swap
    · simp [comps] at hd
    split at hd
    · simp at hd
    rename_i hpu
    have hmem : ∀ e ∈ W :: (comps u W ++ comps u p), e ∈ Gc u (app P (psi p W c1)) := by
      intro e he
      apply gc_app_right
      unfold Gc; apply List.mem_cons_of_mem
      simp only [comps]; rw [if_neg hpu]
      exact List.mem_append_left _ he
    simp only [List.mem_cons, List.mem_append] at hd
    rcases hd with rfl | hd | hd
    · exact ⟨W, hmem W List.mem_cons_self, hW1⟩
    · rcases (le_iff _ _).mp hW1 with hlt | rfl
      · obtain ⟨W0, rfl, _, _⟩ := between_app (A := Y0) (x := z) (by rw [app_z_right]; exact hlt) hW2
        refine ⟨d, hmem d (List.mem_cons_of_mem _ (List.mem_append_left _ ?_)), le_refl _⟩
        rw [comps_app]; exact List.mem_append_left _ hd
      · exact ⟨d, hmem d (List.mem_cons_of_mem _ (List.mem_append_left _ hd)), le_refl _⟩
    · exact ⟨d, hmem d (List.mem_cons_of_mem _ (List.mem_append_right _ hd)), le_refl _⟩



/-! ## 列での主張（t0-exp・t2 で共通） -/

/-- **The claim at a column, at the levels `U`.** -/
def RClaimU (U : T → Prop) (ρ ρ' : Valn) (i : Nat) : Prop :=
  ∀ p y y' q, ρ.o i = psi p y z → ρ'.o i = psi p y' z → ¬ lt p q = true →
    (∀ u, U u → ¬ lt q u = true → ∀ g ∈ comps u p, g ≤ psi p z z ∨ g < H p y' ∨ ∃ d ∈ comps u q, g ≤ d) →
    RelRU U q (H p y') (H p y)

theorem rclaim_zeroU {ρ ρ' : Valn} {i : Nat} {p' : T} (h : ρ'.o i = psi p' z z) :
    RClaimU U ρ ρ' i := by
  intro p y y' q _ hy' _ _
  rw [h] at hy'; simp only [psi.injEq] at hy'; rw [← hy'.2.1, H_z]
  intro u _ _ c _ _ g hg; simp [comps] at hg

end Ytosk
