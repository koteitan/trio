/-
Partial results for ClShL with VDomF and the first conjunct of KAG.

The two unguarded / VDomF-only counterexamples live in V3ClShL.lean.
This file contains ONLY the guarded task's proved helper lemmas.

KA is exactly the requested condition at levels u <= V (unshifted old
components of a); it is not replaced by the stronger SubstDom.1.
low_components_interval_only discharges introduced components, unchanged
component bounds, and moving state/index bounds. General interval persistence
through sh and the levels above V remain unresolved. There is no full clShL
theorem. The shared-leading-index helper is conditional: the original frame
hypotheses do not force the two interval endpoints to share their index.
-/
import Ytosk.V3ShadowL
import Ytosk.V3T2VRAK

namespace Ytosk.ClShLGuarded

open T

/-- The old-component hypothesis requested for the guarded ClShL. -/
def KA (V V' a : T) : Prop :=
  ∀ u, ¬ lt V u = true → ∀ d ∈ comps u a,
    d ≤ psi (shf V V' a) z z ∨ ∃ d' ∈ comps u (shf V V' a), d ≤ d'

/-- The interval alternative, separated from the two component bounds. -/
def Persistent (u g B A : T) : Prop :=
  ∀ c, B < c → c ≤ A → ∃ d ∈ Gc u c, g ≤ d

/-- The frame's summand bound puts the shifted state above Omega_{f(a)}. -/
theorem omega_le_state {V V' a B s y : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a) (hB : isOT B = true) (hBz : B ≠ z)
    (hBs : ∀ q ∈ summands B, psi s y z ≤ q)
    (hBV : ∀ q ∈ summands B, V < lev q)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true) :
    psi (shf V V' a) z z ≤ sh V V' B := by
  have has : a ≤ s := le_of_trig ht.2
  exact om_shf_le_sh hV hV' (le_of_lt hVV) ha hVa hB hBz hBV
    (fun q hq => le_trans has (lev_le_of_le (hBs q hq)))

/-- VDomF discharges every component introduced from V', at all levels. -/
theorem introduced_bound {V V' a B u g : T} (hVD : VDomF V V' a)
    (hOm : psi (shf V V' a) z z ≤ sh V V' B)
    (hu : ¬ lt (shf V V' a) u = true) (hg : g ∈ comps u V') :
    g ≤ sh V V' B ∨ ∃ d ∈ comps u (shf V V' a), g ≤ d := by
  rcases hVD u hu g hg with h | h
  · exact Or.inl (le_trans h hOm)
  · exact Or.inr h

/-- KA discharges the unchanged old components of a at levels at most V. -/
theorem retained_index_bound {V V' a B u g : T} (hKA : KA V V' a)
    (hOm : psi (shf V V' a) z z ≤ sh V V' B)
    (hu : ¬ lt V u = true) (hg : g ∈ comps u a) :
    g ≤ sh V V' B ∨ ∃ d ∈ comps u (shf V V' a), g ≤ d := by
  rcases hKA u hu g hg with h | h
  · exact Or.inl (le_trans h hOm)
  · exact Or.inr h

/-- For an unchanged component of B the only remaining case is its old
interval alternative; neither the state bound nor old-index domination remains. -/
theorem retained_component {V V' a B A u g : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hVa : V ≤ a) (hB : isOT B = true) (hKA : KA V V' a)
    (hOm : psi (shf V V' a) z z ≤ sh V V' B)
    (hcl : ClosedL a B A) (hu : ¬ lt V u = true) (hg : g ∈ comps u B) :
    g ≤ sh V V' B ∨ (∃ d ∈ comps u (shf V V' a), g ≤ d) ∨ Persistent u g B A := by
  have hua : ¬ lt a u = true := not_lt.mpr (le_trans (not_lt.mp hu) hVa)
  rcases hcl u hua g hg with h | ⟨d, hd, hgd⟩ | h
  · exact Or.inl (le_trans h (le_sh hV hV' (le_of_lt hVV) hB))
  · rcases retained_index_bound hKA hOm hu hd with h | ⟨d', hd', hdd'⟩
    · exact Or.inl (le_trans hgd h)
    · exact Or.inr (Or.inl ⟨d', hd', le_trans hgd hdd'⟩)
  · exact Or.inr (Or.inr h)

/-- A precise low-level reduction of guarded ClShL. The unsolved cases
are moving images and the transport of an old interval-persistent component.
This is a reduction, not a proof of the full ClShL statement. -/
theorem low_components {V V' a B A u g : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a) (hB : isOT B = true)
    (hVD : VDomF V V' a) (hKA : KA V V' a)
    (hOm : psi (shf V V' a) z z ≤ sh V V' B)
    (hcl : ClosedL a B A) (hu : ¬ lt V u = true) (hg : g ∈ comps u (sh V V' B)) :
    g ≤ sh V V' B ∨ (∃ d ∈ comps u (shf V V' a), g ≤ d) ∨
      (∃ d ∈ compsAN V u (size B) B, g = sh V V' d) ∨ Persistent u g B A := by
  have hufa : ¬ lt (shf V V' a) u = true :=
    not_lt.mpr (le_trans (not_lt.mp hu) (le_trans hVa (le_shf_self hV hV' (le_of_lt hVV) ha hVa)))
  rcases comps_sh_levA V V' (not_lt.mp hu) (size B) B g (Nat.le_refl _) hg with
      ⟨d, hd, he⟩ | ⟨d, hd, he⟩ | ⟨q, hq, hgq⟩
  · exact Or.inr (Or.inr (Or.inl ⟨d, hd, he⟩))
  · subst g
    rcases retained_component hV hV' hVV hVa hB hKA hOm hcl hu hd with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases introduced_bound hVD hOm hufa (comps_of_mem_summands hq hgq) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

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

/-- Components at moving positions survive the shift at every level at most V. -/
theorem compsAN_sh_forward {V V' u : T}
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
            (compsAN_sh_forward hV hV' hVV huV n (isOT_arg ht) hg)))
        · have hd := compsAN_sh_forward hV hV' hVV huV n
            (isOT_sub_sfx (isOT_sub ht) V) hg
          obtain ⟨P, hP, _⟩ := add_eq_app_prefix V' (sh V V' (sub s V))
          have hidx : sh V V' g ∈ comps u (shf V V' s) := by
            unfold shf
            rw [hP, comps_app]
            exact List.mem_append.mpr (Or.inr hd)
          exact comps_psi_mem_of hfu (Or.inr (Or.inr (Or.inl hidx)))
      · rw [if_neg hc] at hg
        simp at hg
    · have hd := compsAN_sh_forward hV hV' hVV huV n (isOT_rest ht) hg
      rw [sh_psi_app, comps_app]
      exact List.mem_append.mpr (Or.inr hd)

/-- Subtraction only removes summands below the level of the subtrahend. -/
theorem comps_sub_above {u : T} : ∀ t W : T,
    (∀ q ∈ summands W, lev q < u) → comps u (sub t W) = comps u t
  | z, _, _ => by simp [sub, comps]
  | psi s y c, z, _ => rfl
  | psi s y c, psi d e f, hW => by
    rw [sub_psi_psi]
    split
    · rfl
    · rename_i hn
      have hsd : s ≤ d := lev_le_of_le (le_of_not_gt hn)
      have hdu : d < u := hW (psi d e z) (by simp [summands])
      have hsu : lt s u = true := lt_of_le_of_lt hsd hdu
      rw [comps_sub_above c f (fun q hq => hW q (by simp [summands, hq]))]
      simp [comps, hsu]

/-- Below the first moving level, the level parameter in compsAN is immaterial. -/
theorem compsAN_level_eq {V u w : T} (hu : u ≤ succ V) (hw : w ≤ succ V) :
    ∀ n t, compsAN V u n t = compsAN V w n t
  | 0, _ => rfl
  | _ + 1, z => rfl
  | n + 1, psi s y c => by
    have he : (¬ lt s u = true ∧ lt V s = true) ↔
        (¬ lt s w = true ∧ lt V s = true) := by
      constructor
      · intro h
        exact ⟨not_lt.mpr (le_trans hw (succ_le_of_lt h.2)), h.2⟩
      · intro h
        exact ⟨not_lt.mpr (le_trans hu (succ_le_of_lt h.2)), h.2⟩
    simp only [compsAN, he, compsAN_level_eq hu hw n y,
      compsAN_level_eq hu hw n (sub s V), compsAN_level_eq hu hw n c]

/-- An old component above V survives at any new level at most V. -/
theorem high_component_sh_low {V V' u w : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hu : u ≤ V) (hw : V < w) :
    ∀ n {t g : T}, size t ≤ n → isOT t = true → g ∈ comps w t →
      sh V V' g ∈ comps u (sh V V' t)
  | 0, t, _, hn, _, hg => by
    cases t with
    | z => simp [comps] at hg
    | psi => simp [size] at hn
  | n + 1, z, _, _, _, hg => by simp [comps] at hg
  | n + 1, psi s y c, g, hn, ht, hg => by
    have hny : size y ≤ n := by simp [size] at hn; omega
    have hnc : size c ≤ n := by simp [size] at hn; omega
    have hns : size (sub s V) ≤ n := by
      have := size_sub_le s V
      simp [size] at hn
      omega
    simp only [comps, List.mem_append] at hg
    rcases hg with hg | hg
    · split at hg
      · simp at hg
      · rename_i hsw
        have hVs : V < s := lt_of_lt_of_le hw (not_lt.mp hsw)
        rw [sh_psi_gt hVs]
        have hfu : ¬ shf V V' s < u := not_lt.mpr
          (le_trans hu (le_trans (le_of_lt hVV)
            (le_of_lt (lt_shf hV hV' (le_of_lt hVV) (isOT_sub ht) hVs))))
        simp only [List.mem_cons, List.mem_append] at hg
        rcases hg with rfl | hg | hg
        · exact comps_psi_mem_of hfu (Or.inl rfl)
        · exact comps_psi_mem_of hfu (Or.inr (Or.inl
            (high_component_sh_low hV hV' hVV hu hw n hny (isOT_arg ht) hg)))
        · have hsub : g ∈ comps w (sub s V) := by
            rw [comps_sub_above s V (fun q hq =>
              lt_trans (lev_lt_of_summand hV hq) hw)]
            exact hg
          have hd := high_component_sh_low hV hV' hVV hu hw n hns
            (isOT_sub_sfx (isOT_sub ht) V) hsub
          obtain ⟨P, hP, _⟩ := add_eq_app_prefix V' (sh V V' (sub s V))
          have hidx : sh V V' g ∈ comps u (shf V V' s) := by
            unfold shf
            rw [hP, comps_app]
            exact List.mem_append.mpr (Or.inr hd)
          exact comps_psi_mem_of hfu (Or.inr (Or.inr (Or.inl hidx)))
    · have hd := high_component_sh_low hV hV' hVV hu hw n hnc (isOT_rest ht) hg
      rw [sh_psi_app, comps_app]
      exact List.mem_append.mpr (Or.inr hd)

/-- Components of a above V are retained in the new subscript f(a). -/
theorem high_index_sh_low {V V' a u w g : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hu : u ≤ V) (hw : V < w) (hg : g ∈ comps w a) :
    sh V V' g ∈ comps u (shf V V' a) := by
  have hgsub : g ∈ comps w (sub a V) := by
    rw [comps_sub_above a V (fun q hq => lt_trans (lev_lt_of_summand hV hq) hw)]
    exact hg
  have hd := high_component_sh_low hV hV' hVV hu hw (size (sub a V))
    (Nat.le_refl _) (isOT_sub_sfx ha V) hgsub
  obtain ⟨P, hP, _⟩ := add_eq_app_prefix V' (sh V V' (sub a V))
  unfold shf
  rw [hP, comps_app]
  exact List.mem_append.mpr (Or.inr hd)

/-- Moving components need no extra old-index guard: their unresolved case
is precisely the old interval alternative at V or succ V. -/
theorem moving_component {V V' a B A u g : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a) (hB : isOT B = true)
    (hcl : ClosedL a B A) (hu : u ≤ V) {n : Nat} (hg : g ∈ compsAN V u n B) :
    sh V V' g ≤ sh V V' B ∨
      (∃ d ∈ comps u (shf V V' a), sh V V' g ≤ d) ∨
      ∃ w, V ≤ w ∧ w ≤ succ V ∧ w ≤ a ∧ Persistent w g B A := by
  have hgo : isOT g = true := isOT_of_mem_comps u hB (compsAN_sub V u n hg)
  rcases (le_iff _ _).mp hVa with hVa | hVa
  · have hwa : succ V ≤ a := succ_le_of_lt hVa
    have hgw : g ∈ comps (succ V) B := by
      apply compsAN_sub V (succ V) n
      rw [← compsAN_level_eq (le_trans hu (le_of_lt (lt_succ_self V))) (le_refl (succ V)) n B]
      exact hg
    rcases hcl (succ V) (not_lt.mpr hwa) g hgw with h | ⟨d, hd, hgd⟩ | h
    · exact Or.inl (sh_le_sh hV hV' (le_of_lt hVV) hgo hB h)
    · exact Or.inr (Or.inl ⟨sh V V' d,
        high_index_sh_low hV hV' hVV ha hu (lt_succ_self V) hd,
        sh_le_sh hV hV' (le_of_lt hVV) hgo (isOT_of_mem_comps (succ V) ha hd) hgd⟩)
    · exact Or.inr (Or.inr ⟨succ V, le_of_lt (lt_succ_self V), le_refl _, hwa, h⟩)
  · subst a
    have hgv : g ∈ comps V B := by
      apply compsAN_sub V V n
      rw [← compsAN_level_eq (le_trans hu (le_of_lt (lt_succ_self V)))
        (le_of_lt (lt_succ_self V)) n B]
      exact hg
    rcases hcl V (show ¬ lt V V = true from lt_irrefl' V) g hgv with h | ⟨d, hd, _⟩ | h
    · exact Or.inl (sh_le_sh hV hV' (le_of_lt hVV) hgo hB h)
    · rw [comps_self hV] at hd
      simp at hd
    · exact Or.inr (Or.inr ⟨V, le_refl _, le_of_lt (lt_succ_self V), le_refl _, h⟩)

/-- At levels at most V, only transport of the interval alternatives remains.
The moving alternative is evaluated at an old level between V and succ V. -/
theorem low_components_interval_only {V V' a B A u g : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a) (hB : isOT B = true)
    (hVD : VDomF V V' a) (hKA : KA V V' a)
    (hOm : psi (shf V V' a) z z ≤ sh V V' B)
    (hcl : ClosedL a B A) (hu : ¬ lt V u = true) (hg : g ∈ comps u (sh V V' B)) :
    g ≤ sh V V' B ∨ (∃ d ∈ comps u (shf V V' a), g ≤ d) ∨
      Persistent u g B A ∨
      ∃ d w, g = sh V V' d ∧ d ∈ compsAN V u (size B) B ∧
        V ≤ w ∧ w ≤ succ V ∧ w ≤ a ∧ Persistent w d B A := by
  rcases low_components hV hV' hVV ha hVa hB hVD hKA hOm hcl hu hg with
      h | h | ⟨d, hd, he⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases moving_component hV hV' hVV ha hVa hB hcl (not_lt.mp hu) hd with
        h | h | ⟨w, hwV, hwS, hwa, hp⟩
    · exact Or.inl (he ▸ h)
    · exact Or.inr (Or.inl (he ▸ h))
    · exact Or.inr (Or.inr (Or.inr ⟨d, w, he, hd, hwV, hwS, hwa, hp⟩))
  · exact Or.inr (Or.inr (Or.inl h))

/-- Finite right-hand corners: raise one coordinate and reset later coordinates.
These terms need not be standard, just like the terms quantified by Persistent. -/
def rightCorners : T → List T
  | z => [one]
  | psi p x r =>
    (rightCorners p).map (fun v => psi v z z) ++
    (rightCorners x).map (fun e => psi p e z) ++
    (rightCorners r).map (fun t => psi p x t)

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

private theorem dom_gc_refl (u t : T) : Dom (Gc u t) (Gc u t) :=
  fun d hd => ⟨d, hd, le_refl _⟩

private theorem dom_gc_zero (u t : T) : Dom (Gc u z) (Gc u t) := by
  intro d hd
  have hd0 : d = z := by simpa [Gc, comps] using hd
  subst d
  exact ⟨z, List.mem_cons_self, le_refl _⟩

/-- Coordinate domination, including direct argument bounds, respects components. -/
theorem dom_gc_psi {u p x r q y t : T}
    (hp : p ≤ q) (hx : x ≤ y)
    (hpc : Dom (Gc u p) (Gc u q)) (hxc : Dom (Gc u x) (Gc u y))
    (hrc : Dom (Gc u r) (Gc u t)) :
    Dom (Gc u (psi p x r)) (Gc u (psi q y t)) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact ⟨z, List.mem_cons_self, le_refl _⟩
  simp only [comps, List.mem_append] at hg
  rcases hg with hg | hg
  · by_cases hpu : lt p u = true
    · rw [if_pos hpu] at hg
      simp at hg
    · rw [if_neg hpu] at hg
      have hqu : ¬ q < u := not_lt.mpr (le_trans (not_lt.mp hpu) hp)
      simp only [List.mem_cons, List.mem_append] at hg
      rcases hg with rfl | hg | hg
      · exact ⟨y, List.mem_cons_of_mem _ (comps_psi_mem_of hqu (Or.inl rfl)), hx⟩
      · obtain ⟨d, hd, hgd⟩ := hxc g (List.mem_cons_of_mem _ hg)
        exact ⟨d, gc_arg hqu hd, hgd⟩
      · obtain ⟨d, hd, hgd⟩ := hpc g (List.mem_cons_of_mem _ hg)
        exact ⟨d, gc_index hqu hd, hgd⟩
  · obtain ⟨d, hd, hgd⟩ := hrc g (List.mem_cons_of_mem _ hg)
    exact ⟨d, gc_tail hd, hgd⟩

/-- Every right-hand corner is strictly above its source. -/
theorem rightCorners_gt : ∀ {B r : T}, r ∈ rightCorners B → B < r
  | z, r, hr => by
    have hr1 : r = one := by simpa [rightCorners] using hr
    subst r
    exact T.z_lt_psi _ _ _
  | psi p x t, r, hr => by
    simp only [rightCorners, List.mem_append, List.mem_map] at hr
    rcases hr with (⟨v, hv, rfl⟩ | ⟨e, he, rfl⟩) | ⟨s, hs, rfl⟩
    · exact T.psi_lt_psi.mpr (Or.inl (rightCorners_gt hv))
    · exact T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨rfl, rightCorners_gt he⟩))
    · exact T.psi_lt_psi.mpr (Or.inr (Or.inr ⟨rfl, rfl, rightCorners_gt hs⟩))

/-- Above B, some finite corner is below c and its components are dominated
by those of c. No standardness hypothesis is needed for B or c. -/
theorem rightCorners_coinitial (u : T) : ∀ {B c : T}, B < c →
    ∃ r ∈ rightCorners B, r ≤ c ∧ Dom (Gc u r) (Gc u c)
  | z, c, h => by
    refine ⟨one, by simp [rightCorners], one_le_of_ne_z ?_, ?_⟩
    · exact fun he => T.not_lt_z _ (he ▸ h)
    · intro g hg
      have hg0 : g = z := by
        simp [Gc, one, comps] at hg
        tauto
      subst g
      exact ⟨z, List.mem_cons_self, le_refl _⟩
  | psi p x t, z, h => False.elim (T.not_lt_z _ h)
  | psi p x t, psi q y s, h => by
    rcases T.psi_lt_psi.mp h with hp | ⟨rfl, hx⟩ | ⟨rfl, rfl, ht⟩
    · obtain ⟨v, hv, hvq, hvc⟩ := rightCorners_coinitial u hp
      refine ⟨psi v z z, ?_, psi_mono_coords hvq (z_le _) (z_le _),
        dom_gc_psi hvq (z_le _) hvc (dom_gc_zero u y) (dom_gc_zero u s)⟩
      simp only [rightCorners, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl ⟨v, hv, rfl⟩)
    · obtain ⟨e, he, hey, hec⟩ := rightCorners_coinitial u hx
      refine ⟨psi p e z, ?_, psi_mono_coords (le_refl _) hey (z_le _),
        dom_gc_psi (le_refl _) hey (dom_gc_refl u p) hec (dom_gc_zero u s)⟩
      simp only [rightCorners, List.mem_append, List.mem_map]
      exact Or.inl (Or.inr ⟨e, he, rfl⟩)
    · obtain ⟨r, hr, hrs, hrc⟩ := rightCorners_coinitial u ht
      refine ⟨psi p x r, ?_, psi_mono_coords (le_refl _) (le_refl _) hrs,
        dom_gc_psi (le_refl _) (le_refl _) (dom_gc_refl u p) (dom_gc_refl u x) hrc⟩
      simp only [rightCorners, List.mem_append, List.mem_map]
      exact Or.inr ⟨r, hr, rfl⟩

/-- Exact finite characterization of Persistent using the endpoints only. -/
theorem persistent_iff_rightCorners {u g B A : T} :
    Persistent u g B A ↔
      ∀ r ∈ rightCorners B, r ≤ A → ∃ d ∈ Gc u r, g ≤ d := by
  constructor
  · intro hp r hr hra
    exact hp r (rightCorners_gt hr) hra
  · intro hp c hBc hcA
    obtain ⟨r, hr, hrc, hdom⟩ := rightCorners_coinitial u hBc
    obtain ⟨d, hd, hgd⟩ := hp r hr (le_trans hrc hcA)
    obtain ⟨e, he, hde⟩ := hdom d hd
    exact ⟨e, he, le_trans hgd hde⟩

#print axioms persistent_iff_rightCorners
#print axioms rightCorners_coinitial

#print axioms low_components_interval_only

#print axioms high_index_sh_low
#print axioms moving_component

#print axioms comps_sub_above
#print axioms compsAN_level_eq
#print axioms high_component_sh_low

#print axioms compsAN_sh_forward

#print axioms low_components
#print axioms persistent_of_shared_level

end Ytosk.ClShLGuarded
