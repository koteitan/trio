/-
**Closedness of G3 cuts, below the invariant files (2026-10-18, lead / trio-codex).**

Copies of the pieces of V3ClShLV and V3RwClCut that the shadow consumers need, placed low enough that
V3T0DepS and V3DepRWU can import them (V3Inv2 imports V3DepRWU). `shadow_hShL_from_kind`: at a nonprefix
shadow frame, the G3 cut kind (PH3cKindG) and the level-restricted seed bound hVR give the hShL conclusion
that RwClosedL used to give. No RwClosedL is needed.
-/
import Ytosk.V3ShadowL
import Ytosk.V3PDef
import Ytosk.V3PShG
import Ytosk.V3T2SeedRec
import Ytosk.V3SubstLev

namespace Ytosk.CutClosed

open T

/-- The interval alternative, separated from the two component bounds. -/
def Persistent (u g B A : T) : Prop :=
  ∀ c, B < c → c ≤ A → ∃ d ∈ Gc u c, g ≤ d

/-- Every term between two terms with the same leading index retains
that index, even when the intermediate term is not a standard term. -/
theorem persistent_of_shared_level {u g p x r y t : T}
    (hup : u ≤ p) (hg : g ∈ comps u p) :
    Persistent u g (psi p x r) (psi p y t) := by
  intro c hc1 hc2
  cases c with
  | z => exact False.elim (T.not_lt_z _ hc1)
  | psi q e f =>
    have hpq : p ≤ q := by simpa only [lev] using lev_le_of_le (le_of_lt hc1)
    have hqp : q ≤ p := by simpa only [lev] using lev_le_of_le hc2
    have hqp' : q = p := le_antisymm hqp hpq
    subst q
    refine ⟨g, List.mem_cons_of_mem _ ?_, le_refl _⟩
    exact comps_psi_mem_of (not_lt.mpr hup) (Or.inr (Or.inr (Or.inl hg)))

/-- A lower argument bound persists between endpoints with the same index.
The bound may vary from term to term; no literally shared component is needed. -/
theorem persistent_of_argument_bound {u g p x r y t : T}
    (hup : u ≤ p) (hg : g ≤ x) :
    Persistent u g (psi p x r) (psi p y t) := by
  intro c hc1 hc2
  cases c with
  | z => exact False.elim (T.not_lt_z _ hc1)
  | psi q e f =>
    have hpq : p ≤ q := by simpa only [lev] using lev_le_of_le (le_of_lt hc1)
    have hqp : q ≤ p := by simpa only [lev] using lev_le_of_le hc2
    have heq : q = p := le_antisymm hqp hpq
    subst q
    have hxe : x ≤ e := by
      rcases T.psi_lt_psi.mp hc1 with h | ⟨_, h⟩ | ⟨_, h, _⟩
      · exact False.elim (lt_irrefl' p h)
      · exact le_of_lt h
      · exact le_of_eq h
    exact ⟨e, List.mem_cons_of_mem _ (comps_psi_mem_of (not_lt.mpr hup) (Or.inl rfl)),
      le_trans hg hxe⟩

/-- A fixed prefix preserves an interval-persistent bound. -/
theorem persistent_app {u g B A : T} (P : T) (hp : Persistent u g B A) :
    Persistent u g (app P B) (app P A) := by
  intro c hc1 hc2
  obtain ⟨c0, rfl, hBc, hcA⟩ := between_app hc1 hc2
  obtain ⟨d, hd, hgd⟩ := hp c0 hBc hcA
  refine ⟨d, ?_, hgd⟩
  rcases List.mem_cons.mp hd with rfl | hd
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (by rw [comps_app]; exact List.mem_append.mpr (Or.inr hd))

private theorem psi_mono_coords {p x r q y t : T}
    (hp : p ≤ q) (hx : x ≤ y) (hr : r ≤ t) : psi p x r ≤ psi q y t := by
  rcases (le_iff _ _).mp hp with hp | rfl
  · exact psi_le_psi_of (Or.inl hp)
  · rcases (le_iff _ _).mp hx with hx | rfl
    · exact psi_le_psi_of (Or.inr ⟨rfl, Or.inl hx⟩)
    · exact psi_le_psi_of (Or.inr ⟨rfl, Or.inr ⟨rfl, hr⟩⟩)

private theorem gc_tail {u p x c d : T} (hd : d ∈ Gc u c) :
    d ∈ Gc u (psi p x c) := by
  rcases List.mem_cons.mp hd with rfl | hd
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (mem_comps_tail hd)

private theorem gc_arg {u p x c d : T} (hp : ¬ p < u) (hd : d ∈ Gc u x) :
    d ∈ Gc u (psi p x c) := by
  rcases List.mem_cons.mp hd with rfl | hd
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (comps_psi_mem_of hp (Or.inr (Or.inl hd)))

private theorem gc_index {u p x c d : T} (hp : ¬ p < u) (hd : d ∈ Gc u p) :
    d ∈ Gc u (psi p x c) := by
  rcases List.mem_cons.mp hd with rfl | hd
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (comps_psi_mem_of hp (Or.inr (Or.inr (Or.inl hd))))

/-- Persistence in an index interval lifts through a principal term.
The left index itself also supplies its components at the equality boundary. -/
theorem persistent_psi_index {u g p q x r y t : T}
    (hup : u ≤ p) (hg : g ∈ Gc u p) (hp : Persistent u g p q) :
    Persistent u g (psi p x r) (psi q y t) := by
  intro c hc1 hc2
  cases c with
  | z => exact False.elim (T.not_lt_z _ hc1)
  | psi v e f =>
    have hpv : p ≤ v := by simpa only [lev] using lev_le_of_le (le_of_lt hc1)
    have hvq : v ≤ q := by simpa only [lev] using lev_le_of_le hc2
    have huv : ¬ v < u := not_lt.mpr (le_trans hup hpv)
    rcases (le_iff _ _).mp hpv with hpv | rfl
    · obtain ⟨d, hd, hgd⟩ := hp v hpv hvq
      exact ⟨d, gc_index huv hd, hgd⟩
    · exact ⟨g, gc_index huv hg, le_refl _⟩

/-- Persistence in an argument interval lifts through a fixed index. -/
theorem persistent_psi_argument {u g p x r y t : T}
    (hup : u ≤ p) (hg : g ∈ Gc u x) (hp : Persistent u g x y) :
    Persistent u g (psi p x r) (psi p y t) := by
  intro c hc1 hc2
  cases c with
  | z => exact False.elim (T.not_lt_z _ hc1)
  | psi q e f =>
    have hpq : p ≤ q := by simpa only [lev] using lev_le_of_le (le_of_lt hc1)
    have hqp : q ≤ p := by simpa only [lev] using lev_le_of_le hc2
    have heq : q = p := le_antisymm hqp hpq
    subst q
    have hxe : x ≤ e := by
      rcases T.psi_lt_psi.mp hc1 with h | ⟨_, h⟩ | ⟨_, h, _⟩
      · exact False.elim (lt_irrefl' p h)
      · exact le_of_lt h
      · exact le_of_eq h
    have hey : e ≤ y := by
      rcases (le_iff _ _).mp hc2 with h | h
      · rcases T.psi_lt_psi.mp h with h | ⟨_, h⟩ | ⟨_, h, _⟩
        · exact False.elim (lt_irrefl' p h)
        · exact le_of_lt h
        · exact le_of_eq h
      · exact le_of_eq (T.psi.inj h).2.1
    rcases (le_iff _ _).mp hxe with hxe | rfl
    · obtain ⟨d, hd, hgd⟩ := hp e hxe hey
      exact ⟨d, gc_arg (not_lt.mpr hup) hd, hgd⟩
    · exact ⟨g, gc_arg (not_lt.mpr hup) hg, le_refl _⟩

/-- A G3 cut is closed relative to any right extension of its source,
apart from the components of the cut's seed index s. -/
theorem cutsHG_closed {s u : T} : ∀ {h B : T}, B ∈ cutsHG s h →
    isOT B = true → ∀ R g, g ∈ comps u B →
      g ≤ B ∨ (∃ d ∈ comps u s, g ≤ d) ∨ Persistent u g B (app h R) := by
  intro h
  induction h with
  | z => intro B hB; simp [cutsHG] at hB
  | psi a x c iha ihx ihc =>
    intro B hB hBot R g hg
    rcases mem_cutsHG_psi.mp hB with ⟨hsa, rfl⟩ | ⟨v, hv, rfl⟩ |
        ⟨hsa, v, hv, rfl⟩ | ⟨hsa, v, hv, rfl⟩
    · by_cases hsu : s < u
      · simp [comps, show lt s u = true from hsu] at hg
      · rw [comps_psi_z_of_ge hsu] at hg
        simp only [comps, List.mem_cons, List.mem_append, List.not_mem_nil, false_or] at hg
        rcases hg with rfl | hg
        · exact Or.inl (z_le _)
        · exact Or.inr (Or.inl ⟨g, hg, le_refl _⟩)
    · by_cases hvu : v < u
      · simp [comps, show lt v u = true from hvu] at hg
      · rw [comps_psi_z_of_ge hvu] at hg
        simp only [comps, List.mem_cons, List.mem_append, List.not_mem_nil, false_or] at hg
        rcases hg with rfl | hg
        · exact Or.inl (z_le _)
        · rcases iha hv (isOT_sub hBot) z g hg with h | h | hp
          · exact Or.inl (le_trans h (le_of_lt (lt_Om_self v)))
          · exact Or.inr (Or.inl h)
          · right; right
            apply persistent_psi_index (not_lt.mp hvu) (List.mem_cons_of_mem _ hg)
            simpa using hp
    · by_cases hau : a < u
      · simp [comps, show lt a u = true from hau] at hg
      · rw [comps_psi_z_of_ge hau] at hg
        simp only [List.mem_cons, List.mem_append] at hg
        rcases hg with rfl | hg | hg
        · exact Or.inr (Or.inr (persistent_of_argument_bound (not_lt.mp hau) (le_refl _)))
        · rcases ihx hv (isOT_arg hBot) z g hg with h | h | hp
          · exact Or.inr (Or.inr (persistent_of_argument_bound (not_lt.mp hau) h))
          · exact Or.inr (Or.inl h)
          · right; right
            apply persistent_psi_argument (not_lt.mp hau) (List.mem_cons_of_mem _ hg)
            simpa using hp
        · exact Or.inr (Or.inr (persistent_of_shared_level (not_lt.mp hau) hg))
    · simp only [comps, List.mem_append] at hg
      rcases hg with hg | hg
      · by_cases hau : a < u
        · simp [show lt a u = true from hau] at hg
        · rw [if_neg (show ¬ lt a u = true from hau)] at hg
          simp only [List.mem_cons, List.mem_append] at hg
          rcases hg with rfl | hg | hg
          · exact Or.inr (Or.inr (persistent_of_argument_bound (not_lt.mp hau) (le_refl _)))
          · exact Or.inr (Or.inr (persistent_psi_argument (not_lt.mp hau)
              (List.mem_cons_of_mem _ hg) (by intro e he1 he2; exact False.elim (not_lt_of_ge he2 he1))))
          · exact Or.inr (Or.inr (persistent_of_shared_level (not_lt.mp hau) hg))
      · rcases ihc hv (isOT_rest hBot) R g hg with h | h | hp
        · left
          exact le_trans h (le_of_lt (rest_lt hBot))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (persistent_app (psi a x z) hp))

/-- At a high source, state-level cuts are also G3 cuts inside the term. -/
theorem cutsNSG_mem_cutsHG {s : T} : ∀ {h B : T},
    (∀ q ∈ summands h, s ≤ lev q) → B ∈ cutsNSG s h → B ∈ cutsHG s h := by
  intro h
  induction h with
  | z => intro B _ hB; simp [cutsNSG] at hB
  | psi a x c _ _ ihc =>
    intro B hge hB
    have hsa : le s a = true := by
      have h : s ≤ a := hge (psi a x z) (by simp [summands])
      rcases (le_iff _ _).mp h with h | rfl
      · simp [le, show lt s a = true from h]
      · simp [le]
    rcases mem_cutsNSG_psi.mp hB with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · exact mem_cutsHG_psi.mpr (Or.inr (Or.inl ⟨v, hv, rfl⟩))
    · exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inl ⟨hsa, v, hv, rfl⟩)))
    · exact mem_cutsHG_psi.mpr (Or.inr (Or.inr (Or.inr ⟨hsa, v,
        ihc (fun q hq => hge q (by simp [summands, hq])) hv, rfl⟩)))

/-- Applying H preserves standardness even at its own parent index. -/
theorem isOT_H_self {s y : T} (hc : isOT (psi s y z) = true) :
    isOT (psi s (H s y) z) = true := by
  have ey := split_app (psi (succ s) z z) y
  have hhi : isOT (split y (psi (succ s) z z)).1 = true := by
    have hy := isOT_arg hc
    rw [← ey] at hy
    exact isOT_app_left hy
  have hHs : isOT (H s y) = true := by
    rw [H_eq hc]
    split
    · simpa using hhi
    · apply isOT_app_of hhi hc
      intro q hq
      exact le_of_lt (lt_of_lt_of_le
        (psi_lt_psi_z_iff.mpr (Or.inl (lt_succ_self s)))
        (not_lt.mp (split_fst_ge _ y q hq)))
  rw [isOT_psi_iff]
  refine ⟨isOT_sub hc, hHs, rfl, z_le _, ?_⟩
  intro g hg
  by_cases hlo : (split y (psi (succ s) z z)).2 = z
  · rw [H_of_lo_z hc hlo] at hg ⊢
    exact comps_lt hc g hg
  · have hyl : y < H s y := y_lt_H hc hlo
    rw [H_eq hc, if_neg hlo, comps_app] at hg
    rcases List.mem_append.mp hg with hg | hg
    · have hgy : g ∈ comps s y := by
        rw [← ey, comps_app]
        exact List.mem_append.mpr (Or.inl hg)
      exact lt_trans (comps_lt hc g hgy) hyl
    · rw [comps_psi_z_of_ge (lt_irrefl' s)] at hg
      simp only [List.mem_cons, List.mem_append] at hg
      rcases hg with rfl | hg | hg
      · exact hyl
      · exact lt_trans (comps_lt hc g hg) hyl
      · rw [comps_self (isOT_sub hc)] at hg
        simp at hg

/-- A smaller parent index sees only the high part of H. -/
theorem H_H_of_lt {a s y : T} (ha : isOT a = true)
    (hc : isOT (psi s y z) = true) (has : a < s) : H a (H s y) = H s y := by
  apply H_of_high ha
  intro q hq
  apply not_lt.mpr
  apply le_trans _ (H_summands_ge hc q hq)
  exact psi_mono_coords (succ_le_of_lt has) (z_le _) (le_refl _)

/-- The nested endpoint always retains the original high part as a prefix. -/
theorem H_H_prefix {a s y : T} (ha : isOT a = true)
    (hc : isOT (psi s y z) = true) (has : a ≤ s) :
    ∃ R, H a (H s y) = app (split y (psi (succ s) z z)).1 R := by
  rcases (le_iff _ _).mp has with has | rfl
  · rw [H_H_of_lt ha hc has, H_eq hc]
    exact ⟨_, rfl⟩
  · rw [HH_form hc (isOT_H_self hc)]
    split
    · rw [H_eq hc]
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- A state-level cut of the high part is a G3 cut inside that high part. -/
theorem shadow_cut_mem_HG {B s y : T}
    (hcut : B ∈ cutsNSG s (split y (psi (succ s) z z)).1) :
    B ∈ cutsHG s (split y (psi (succ s) z z)).1 := by
  apply cutsNSG_mem_cutsHG _ hcut
  intro q hq
  have hqge := not_lt.mp (split_fst_ge (psi (succ s) z z) y q hq)
  exact le_trans (le_of_lt (lt_succ_self s)) (by simpa [lev] using lev_le_of_le hqge)

/-- The seed Omega bound is a state bound, at every level. -/
theorem omega_le_of_shadow_cut {B s y : T}
    (hcut : B ∈ cutsNSG s (split y (psi (succ s) z z)).1) :
    psi s z z ≤ B := by
  have hHG := shadow_cut_mem_HG hcut
  have hl := cutsHG_lev_cut hHG
  cases B with
  | z => exact False.elim (T.not_lt_z _ (cutsHG_gt hHG))
  | psi p x c => exact psi_le_psi_anyG hl

/-- The cut proof needs a seed bound only at the single level being checked. -/
theorem closed_at_of_shadow_cut {a B s y u : T}
    (ha : isOT a = true) (hB : isOT B = true)
    (hc : isOT (psi s y z) = true) (has : a ≤ s)
    (hcut : B ∈ cutsNSG s (split y (psi (succ s) z z)).1)
    (hseed : ∀ d ∈ comps u s,
      d ≤ psi s z z ∨ d ≤ B ∨ ∃ e ∈ comps u a, d ≤ e) :
    ∀ g ∈ comps u B, g ≤ B ∨ (∃ d ∈ comps u a, g ≤ d) ∨
      Persistent u g B (H a (H s y)) := by
  obtain ⟨R, hR⟩ := H_H_prefix ha hc has
  have hOm := omega_le_of_shadow_cut hcut
  intro g hg
  rcases cutsHG_closed (shadow_cut_mem_HG hcut) hB R g hg with h | ⟨d, hd, hgd⟩ | hp
  · exact Or.inl h
  · rcases hseed d hd with h | h | ⟨e, he, hde⟩
    · exact Or.inl (le_trans hgd (le_trans h hOm))
    · exact Or.inl (le_trans hgd h)
    · exact Or.inr (Or.inl ⟨e, he, le_trans hgd hde⟩)
  · right; right
    rw [hR]
    exact hp

/-- The actual shadow consumer only needs closure at the levels it uses.
This local form avoids extending VSmallRAll to unused lower levels. -/
theorem shadow_hShL_on_levels {U : T → Prop} {a B s y y' A : T}
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hnt : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true))
    (hy'z : y' ≠ z)
    (hl : Lhd z (psi s y' z) (psi s y z))
    (hX'ot : isOT (psi a (app B (psi s y' z)) z) = true)
    (hB : ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u B,
      g ≤ B ∨ (∃ d ∈ comps u a, g ≤ d) ∨ Persistent u g B A)
    (hVR : ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u s,
      g ≤ psi s z z ∨ g ≤ B ∨ ∃ d ∈ comps u a, g ≤ d) :
    ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u (app B (psi s y' z)),
      g < app B (psi s y' z) ∨ (∃ d ∈ comps u a, g ≤ d) ∨
        ∀ c, H a (app B (psi s y' z)) < c → c ≤ A → ∃ d ∈ Gc u c, g ≤ d := by
  intro u hU hu g hg
  have has : a ≤ s := by
    rcases psi_lt_psi_z_iff.mp (show psi a z z < psi s y z from ht.2) with h | ⟨h, _⟩
    · exact le_of_lt h
    · rw [h]
  have hy'pos : z < y' := lt_of_le_of_ne (z_le y') (Ne.symm hy'z)
  have h2' : psi a z z < psi s y' z := by
    rcases (le_iff _ _).mp has with h | h
    · exact psi_lt_psi_z_iff.mpr (Or.inl h)
    · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨h, hy'pos⟩)
  have hy'B : y' ≤ B := by
    by_contra hn
    exact hnt ⟨lt_of_not_ge hn, h2'⟩
  have hBz : B ≠ z := fun e => by rw [e] at hy'B; exact hy'z (le_antisymm hy'B (z_le _))
  set X' := app B (psi s y' z) with hX'
  have hBX : B < X' := lt_app_ne (by simp)
  have hXH : X' ≤ H a X' := le_H hX'ot
  have hyB : psi s y z ≤ B := le_of_summand_first hBz hBc
  have hsu : ¬ lt s u = true := fun h => hu (lt_of_le_of_lt has h)
  -- the interval escape of `B` moves to the interval above `H a X′`
  have hlift : ∀ g, (∀ c, B < c → c ≤ A → ∃ d ∈ Gc u c, g ≤ d) →
      ∀ c, H a X' < c → c ≤ A → ∃ d ∈ Gc u c, g ≤ d :=
    fun g h c hc1 hc2 => h c (lt_of_lt_of_le hBX (le_trans hXH (le_of_lt hc1))) hc2
  -- the subscript components
  have hsub : ∀ g ∈ comps u s, g < X' ∨ ∃ d ∈ comps u a, g ≤ d := by
    intro g hg
    rcases hVR u hU hu g hg with h | h | h
    · left
      refine lt_of_le_of_lt h (lt_of_le_of_lt ?_ (lt_of_le_of_lt hyB hBX))
      rcases (le_iff _ _).mp (z_le y) with h' | h'
      · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, h'⟩))
      · rw [← h']
    · exact Or.inl (lt_of_le_of_lt h hBX)
    · exact Or.inr h
  -- the components of `B`
  rw [hX', comps_app] at hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases hB u hU hu g hg with h | h | h
    · exact Or.inl (lt_of_le_of_lt h hBX)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (hlift g h))
  -- the components of `ψ_s(y′)`
  simp only [comps, if_neg hsu, List.append_nil, List.mem_cons, List.mem_append] at hg
  rcases hg with rfl | hg | hg
  · exact Or.inl (lt_of_le_of_lt hy'B hBX)
  · -- through `◁` at `c = ψ_s(B + 1)`
    have hc1 : psi s y' z < psi s (app B one) z :=
      psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_lt hy'B (lt_app_ne (by simp [one]))⟩)
    have hc2 : psi s (app B one) z ≤ psi s y z := by
      rcases (le_iff _ _).mp (app_one_le_of_lt ht.1) with h | h
      · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, h⟩))
      · rw [h]
    have hgm : g ∈ comps u (psi s y' z) := by
      simp only [comps, if_neg hsu, List.append_nil, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl hg)
    obtain ⟨d, hd, hgd⟩ := hl.2 u _ hc1 hc2 g hgm
    simp only [comps, if_neg hsu, List.append_nil, Gc, List.mem_append, List.mem_cons] at hd
    have hB1 : app B one < X' := by
      have h1 : psi z z z < psi s y' z := by
        rcases (le_iff _ _).mp (z_le s) with h | h
        · exact psi_lt_psi_z_iff.mpr (Or.inl h)
        · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨h, hy'pos⟩)
      exact app_lt_app_left B h1
    rcases hd with (rfl | hd | hd) | hd | hd
    · exact Or.inl (lt_of_le_of_lt hgd hB1)
    · -- `d` is a component of `B + 1`
      rw [comps_app] at hd
      rcases List.mem_append.mp hd with hd | hd
      · rcases hB u hU hu d hd with h | ⟨d', hd', h⟩ | h
        · exact Or.inl (lt_of_le_of_lt (le_trans hgd h) hBX)
        · exact Or.inr (Or.inl ⟨d', hd', le_trans hgd h⟩)
        · refine Or.inr (Or.inr (hlift g (fun c hc1 hc2 => ?_)))
          obtain ⟨d', hd', h'⟩ := h c hc1 hc2
          exact ⟨d', hd', le_trans hgd h'⟩
      · have : d = z := by
          revert hd; simp only [one, comps]
          split_ifs <;> simp
        rw [this] at hgd
        exact Or.inl (lt_of_le_of_lt hgd (lt_of_le_of_lt (z_le B) hBX))
    · rcases hsub d hd with h | h
      · exact Or.inl (lt_of_le_of_lt hgd h)
      · obtain ⟨d', hd', h'⟩ := h; exact Or.inr (Or.inl ⟨d', hd', le_trans hgd h'⟩)
    · rw [hd] at hgd; exact Or.inl (lt_of_le_of_lt hgd (lt_of_le_of_lt (z_le B) hBX))
    · simp at hd
  · exact (hsub g hg).elim Or.inl (fun h => Or.inr (Or.inl h))

/-- A single PH3cKindG value gives the same levelwise conclusion. The
zero state is immediate; strictness and nonprefix exclude the other kinds. -/
theorem closed_at_of_shadow_kind {a B s y u : T}
    (ha : isOT a = true) (hB : isOT B = true)
    (hc : isOT (psi s y z) = true) (has : a ≤ s)
    (hK : B ≠ z → PH3cKindG B (split y (psi (succ s) z z)).1
      (split y (psi (succ s) z z)).2 s)
    (hhi : B < (split y (psi (succ s) z z)).1)
    (hnp : ¬ ∃ R, (split y (psi (succ s) z z)).1 = app B R)
    (hseed : ∀ d ∈ comps u s,
      d ≤ psi s z z ∨ d ≤ B ∨ ∃ e ∈ comps u a, d ≤ e) :
    ∀ g ∈ comps u B, g ≤ B ∨ (∃ d ∈ comps u a, g ≤ d) ∨
      Persistent u g B (H a (H s y)) := by
  by_cases hBz : B = z
  · simp [hBz, comps]
  · have hcut : B ∈ cutsNSG s (split y (psi (succ s) z z)).1 := by
      rcases hK hBz with ⟨h, _⟩ | ⟨_, ⟨R, _, h⟩ | ⟨_, h⟩⟩
      · exact False.elim (lt_irrefl' _ (h ▸ hhi))
      · exact False.elim (hnp ⟨R, h⟩)
      · exact h
    exact closed_at_of_shadow_cut ha hB hc has hcut hseed

/-- A drop-in shadow consumer using PH3cKindG and the very same hVR already
passed to relR_frameUL. No full RwClosedL hypothesis is required. -/
theorem shadow_hShL_from_kind {U : T → Prop} {a B s y y' : T}
    (ha : isOT a = true) (hBot : isOT B = true) (hc : isOT (psi s y z) = true)
    (hK : B ≠ z → PH3cKindG B (split y (psi (succ s) z z)).1
      (split y (psi (succ s) z z)).2 s)
    (hhi : B < (split y (psi (succ s) z z)).1)
    (hnp : ¬ ∃ R, (split y (psi (succ s) z z)).1 = app B R)
    (hBc : ∀ q ∈ summands B, psi s y z ≤ q)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hnt : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true))
    (hy'z : y' ≠ z) (hl : Lhd z (psi s y' z) (psi s y z))
    (hX'ot : isOT (psi a (app B (psi s y' z)) z) = true)
    (hVR : ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u s,
      g ≤ psi s z z ∨ g ≤ B ∨ ∃ d ∈ comps u a, g ≤ d) :
    ∀ u, U u → ¬ lt a u = true → ∀ g ∈ comps u (app B (psi s y' z)),
      g < app B (psi s y' z) ∨ (∃ d ∈ comps u a, g ≤ d) ∨
        Persistent u g (H a (app B (psi s y' z))) (H a (H s y)) := by
  apply shadow_hShL_on_levels hBc ht hnt hy'z hl hX'ot _ hVR
  intro u hU hu
  exact closed_at_of_shadow_kind ha hBot hc (le_of_trig ht.2) hK hhi hnp (hVR u hU hu)

#print axioms shadow_hShL_from_kind

end Ytosk.CutClosed
