/-
Partial results for ClShL with VDomF and the first conjunct of KAG.

The two unguarded / VDomF-only counterexamples live in V3ClShL.lean.
This file contains ONLY the guarded task's proved helper lemmas.

KA is exactly the requested condition at levels u <= V (unshifted old
components of a); it is not replaced by the stronger SubstDom.1.
low_components_interval_only discharges introduced components, unchanged
component bounds, and moving state/index bounds. General interval persistence
through sh remains unresolved. All levels above V now reduce to old interval
alternatives (above_cut_interval_only), including gaps of f. There is no full clShL
theorem. The shared-leading-index helper is conditional: the original frame
hypotheses do not force the two interval endpoints to share their index.
-/
import Ytosk.V3ShadowL
import Ytosk.V3T2VRAK
import Ytosk.V3PShG

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

/-- The same-index argument-bound case of interval transport through sh. -/
theorem persistent_sh_argument_bound {V V' u g p x r y t : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hVp : V < p) (hup : u ≤ shf V V' p)
    (hg : isOT g = true) (hx : isOT x = true) (hgx : g ≤ x) :
    Persistent u (sh V V' g) (sh V V' (psi p x r)) (sh V V' (psi p y t)) := by
  rw [sh_psi_gt hVp, sh_psi_gt hVp]
  exact persistent_of_argument_bound hup (sh_le_sh hV hV' (le_of_lt hVV) hg hx hgx)

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

/-- Forward component transport at any new level seeing all old visible indices. -/
theorem high_component_sh_at {V V' u w : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hw : V < w)
    (hcover : ∀ s, isOT s = true → w ≤ s → u ≤ shf V V' s) :
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
        have hfu : ¬ shf V V' s < u :=
          not_lt.mpr (hcover s (isOT_sub ht) (not_lt.mp hsw))
        simp only [List.mem_cons, List.mem_append] at hg
        rcases hg with rfl | hg | hg
        · exact comps_psi_mem_of hfu (Or.inl rfl)
        · exact comps_psi_mem_of hfu (Or.inr (Or.inl
            (high_component_sh_at hV hV' hVV hw hcover n hny (isOT_arg ht) hg)))
        · have hsub : g ∈ comps w (sub s V) := by
            rw [comps_sub_above s V (fun q hq =>
              lt_trans (lev_lt_of_summand hV hq) hw)]
            exact hg
          have hd := high_component_sh_at hV hV' hVV hw hcover n hns
            (isOT_sub_sfx (isOT_sub ht) V) hsub
          obtain ⟨P, hP, _⟩ := add_eq_app_prefix V' (sh V V' (sub s V))
          have hidx : sh V V' g ∈ comps u (shf V V' s) := by
            unfold shf
            rw [hP, comps_app]
            exact List.mem_append.mpr (Or.inr hd)
          exact comps_psi_mem_of hfu (Or.inr (Or.inr (Or.inl hidx)))
    · have hd := high_component_sh_at hV hV' hVV hw hcover n hnc (isOT_rest ht) hg
      rw [sh_psi_app, comps_app]
      exact List.mem_append.mpr (Or.inr hd)

/-- An old component above V survives at any new level at most V. -/
theorem high_component_sh_low {V V' u w : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hu : u ≤ V) (hw : V < w) :
    ∀ n {t g : T}, size t ≤ n → isOT t = true → g ∈ comps w t →
      sh V V' g ∈ comps u (sh V V' t) := by
  apply high_component_sh_at hV hV' hVV hw
  intro s hs hws
  exact le_trans hu (le_trans (le_of_lt hVV)
    (le_of_lt (lt_shf hV hV' (le_of_lt hVV) hs (lt_of_lt_of_le hw hws))))

/-- Forward transport at any new level at most f(w), for an old level w > V. -/
theorem high_component_sh {V V' u w t g : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hw : isOT w = true) (hVw : V < w) (hu : u ≤ shf V V' w)
    (ht : isOT t = true) (hg : g ∈ comps w t) :
    sh V V' g ∈ comps u (sh V V' t) := by
  apply high_component_sh_at hV hV' hVV hVw ?_ (size t) (Nat.le_refl _) ht hg
  intro s hs hws
  rcases (le_iff _ _).mp hws with hws | rfl
  · exact le_trans hu (le_of_lt
      (shf_lt_shf hV hV' (le_of_lt hVV) hw hs (le_of_lt hVw) hws))
  · exact hu

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

/-- High old-index witnesses survive in f(a), up to the corresponding new level. -/
theorem high_index_sh {V V' a u w g : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hw : isOT w = true) (hVw : V < w)
    (hu : u ≤ shf V V' w) (hg : g ∈ comps w a) :
    sh V V' g ∈ comps u (shf V V' a) := by
  have hgsub : g ∈ comps w (sub a V) := by
    rw [comps_sub_above a V (fun q hq => lt_trans (lev_lt_of_summand hV hq) hVw)]
    exact hg
  have hd := high_component_sh hV hV' hVV hw hVw hu (isOT_sub_sfx ha V) hgsub
  obtain ⟨P, hP, _⟩ := add_eq_app_prefix V' (sh V V' (sub a V))
  unfold shf
  rw [hP, comps_app]
  exact List.mem_append.mpr (Or.inr hd)

/-- At a matched high level f(w), only the old interval alternative remains.
No VDomF or KA is needed here: every new component has an old moving preimage. -/
theorem high_components_interval_only {V V' a B A w g' : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hB : isOT B = true) (hw : isOT w = true)
    (hVw : V < w) (hwa : w ≤ a) (hcl : ClosedL a B A)
    (hg' : g' ∈ comps (shf V V' w) (sh V V' B)) :
    g' ≤ sh V V' B ∨ (∃ d ∈ comps (shf V V' w) (shf V V' a), g' ≤ d) ∨
      ∃ g ∈ comps w B, g' = sh V V' g ∧ Persistent w g B A := by
  obtain ⟨g, hg, rfl⟩ := comps_sh hV hV' hVV hw (le_of_lt hVw) hB g' hg'
  have hgo := isOT_of_mem_comps w hB hg
  rcases hcl w (show ¬ lt a w = true from not_lt.mpr hwa) g hg with h | ⟨d, hd, hgd⟩ | h
  · exact Or.inl (sh_le_sh hV hV' (le_of_lt hVV) hgo hB h)
  · exact Or.inr (Or.inl ⟨sh V V' d,
      high_index_sh hV hV' hVV ha hw hVw (le_refl _) hd,
      sh_le_sh hV hV' (le_of_lt hVV) hgo (isOT_of_mem_comps w ha hd) hgd⟩)
  · exact Or.inr (Or.inr ⟨g, hg, rfl, h⟩)

/-- The same-index case of interval transport for a moving index witness. -/
theorem persistent_sh_index {V V' u w g p x r y t : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hp : isOT p = true) (hw : isOT w = true) (hVw : V < w) (hVp : V < p)
    (huw : u ≤ shf V V' w) (hup : u ≤ shf V V' p) (hg : g ∈ comps w p) :
    Persistent u (sh V V' g) (sh V V' (psi p x r)) (sh V V' (psi p y t)) := by
  rw [sh_psi_gt hVp, sh_psi_gt hVp]
  exact persistent_of_shared_level hup (high_index_sh hV hV' hVV hp hw hVw huw hg)

/-- Above V, frozen nodes are invisible: every component is a moving old
component at succ V, or is introduced from V'. -/
theorem components_above_cut (V V' : T) {u : T} (hVu : V < u) :
    ∀ n {t g' : T}, size t ≤ n → g' ∈ comps u (sh V V' t) →
      (∃ g ∈ comps (succ V) t, g' = sh V V' g) ∨ g' ∈ comps u V'
  | 0, t, _, hn, hg => by
    cases t with
    | z => simp [sh_z, comps] at hg
    | psi => simp [size] at hn
  | n + 1, z, _, _, hg => by simp [sh_z, comps] at hg
  | n + 1, psi s y c, g', hn, hg => by
    have hny : size y ≤ n := by simp [size] at hn; omega
    have hnc : size c ≤ n := by simp [size] at hn; omega
    have hns : size (sub s V) ≤ n := by
      have := size_sub_le s V
      simp [size] at hn
      omega
    have htail : g' ∈ comps u (sh V V' c) →
        (∃ g ∈ comps (succ V) (psi s y c), g' = sh V V' g) ∨ g' ∈ comps u V' := by
      intro hc
      rcases components_above_cut V V' hVu n hnc hc with ⟨g, hg, he⟩ | hc
      · exact Or.inl ⟨g, mem_comps_tail hg, he⟩
      · exact Or.inr hc
    by_cases hVs : V < s
    · rw [sh_psi_gt hVs] at hg
      simp only [comps, List.mem_append] at hg
      rcases hg with hg | hg
      · split at hg
        · simp at hg
        · have hsw : ¬ s < succ V := not_lt.mpr (succ_le_of_lt hVs)
          simp only [List.mem_cons, List.mem_append] at hg
          rcases hg with rfl | hg | hg
          · exact Or.inl ⟨y, comps_psi_mem_of hsw (Or.inl rfl), rfl⟩
          · rcases components_above_cut V V' hVu n hny hg with ⟨g, hg, he⟩ | hg
            · exact Or.inl ⟨g, comps_psi_mem_of hsw (Or.inr (Or.inl hg)), he⟩
            · exact Or.inr hg
          · unfold shf at hg
            obtain ⟨P, hP, hPs⟩ := add_eq_app_prefix V' (sh V V' (sub s V))
            rw [hP, comps_app] at hg
            rcases List.mem_append.mp hg with hg | hg
            · obtain ⟨q, hq, hgq⟩ := comps_to_summand hg
              exact Or.inr (comps_of_mem_summands (hPs q hq) hgq)
            · rcases components_above_cut V V' hVu n hns hg with ⟨g, hg, he⟩ | hg
              · exact Or.inl ⟨g, comps_psi_mem_of hsw
                  (Or.inr (Or.inr (Or.inl (comps_sub_sub (succ V) s V hg)))), he⟩
              · exact Or.inr hg
      · exact htail hg
    · rw [sh_psi_le hVs] at hg
      have hsu : lt s u = true := lt_of_le_of_lt (not_lt.mp hVs) hVu
      simp only [comps, hsu, ↓reduceIte, List.nil_append] at hg
      exact htail hg

/-- The new levels strictly between V and V' also reduce to old interval
alternatives. Together with matched high levels, this covers the first gap of f. -/
theorem middle_components_interval_only {V V' a B A u g' : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a) (hB : isOT B = true)
    (hVD : VDomF V V' a) (hOm : psi (shf V V' a) z z ≤ sh V V' B)
    (hcl : ClosedL a B A) (hVu : V < u) (huV' : u ≤ V') :
    g' ∈ comps u (sh V V' B) →
    g' ≤ sh V V' B ∨ (∃ d ∈ comps u (shf V V' a), g' ≤ d) ∨
      ∃ g w, g' = sh V V' g ∧ V ≤ w ∧ w ≤ succ V ∧ w ≤ a ∧ Persistent w g B A := by
  intro hg'
  rcases components_above_cut V V' hVu (size B) (Nat.le_refl _) hg' with
      ⟨g, hg, rfl⟩ | hg
  · have hgo := isOT_of_mem_comps (succ V) hB hg
    rcases (le_iff _ _).mp hVa with hVa | hVa
    · have hwa := succ_le_of_lt hVa
      have huw : u ≤ shf V V' (succ V) := le_trans huV'
        (le_shf hV hV' (le_of_lt hVV) (isOT_succ hV) (le_of_lt (lt_succ_self V)))
      rcases hcl (succ V) (show ¬ lt a (succ V) = true from not_lt.mpr hwa) g hg with
          h | ⟨d, hd, hgd⟩ | h
      · exact Or.inl (sh_le_sh hV hV' (le_of_lt hVV) hgo hB h)
      · exact Or.inr (Or.inl ⟨sh V V' d,
          high_index_sh hV hV' hVV ha (isOT_succ hV) (lt_succ_self V) huw hd,
          sh_le_sh hV hV' (le_of_lt hVV) hgo (isOT_of_mem_comps (succ V) ha hd) hgd⟩)
      · exact Or.inr (Or.inr ⟨g, succ V, rfl, le_of_lt (lt_succ_self V), le_refl _, hwa, h⟩)
    · subst a
      have hgv := comps_mono (le_of_lt (lt_succ_self V)) hg
      rcases hcl V (show ¬ lt V V = true from lt_irrefl' V) g hgv with h | ⟨d, hd, _⟩ | h
      · exact Or.inl (sh_le_sh hV hV' (le_of_lt hVV) hgo hB h)
      · rw [comps_self hV] at hd
        simp at hd
      · exact Or.inr (Or.inr ⟨g, V, rfl, le_refl _, le_of_lt (lt_succ_self V), le_refl _, h⟩)
  · have hufa : ¬ lt (shf V V' a) u = true := not_lt.mpr
      (le_trans huV' (le_shf hV hV' (le_of_lt hVV) ha hVa))
    rcases introduced_bound hVD hOm hufa hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

private theorem shf_mono_old {V V' b s : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hb : isOT b = true) (hs : isOT s = true) (hVb : V ≤ b) (hbs : b ≤ s) :
    shf V V' b ≤ shf V V' s := by
  rcases (le_iff _ _).mp hbs with h | rfl
  · exact le_of_lt (shf_lt_shf hV hV' (le_of_lt hVV) hb hs hVb h)
  · exact le_refl _

private theorem matched_cap {V V' a s u : T}
    (ha : isOT a = true) (hs : isOT s = true) (hVa : V < a) (hVs : V < s)
    (hua : u ≤ shf V V' a) (hus : u ≤ shf V V' s) :
    ∃ b, isOT b = true ∧ V < b ∧ b ≤ a ∧ b ≤ s ∧ u ≤ shf V V' b := by
  by_cases has : a ≤ s
  · exact ⟨a, ha, hVa, le_refl _, has, hua⟩
  · exact ⟨s, hs, hVs, le_of_lt (lt_of_not_ge has), le_refl _, hus⟩

/-- Every component above V can be raised to a matched level f(w) without
losing its occurrence, unless it was introduced from V'. This handles gaps of f. -/
theorem component_raise_to_matched {V V' u : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V') (hVu : V < u) :
    ∀ n {t a g' : T}, size t ≤ n → isOT t = true → isOT a = true → V < a →
      u ≤ shf V V' a → g' ∈ comps u (sh V V' t) →
      (∃ w, isOT w = true ∧ V < w ∧ w ≤ a ∧ u ≤ shf V V' w ∧
        g' ∈ comps (shf V V' w) (sh V V' t)) ∨ g' ∈ comps u V'
  | 0, t, _, _, hn, _, _, _, _, hg => by
    cases t with
    | z => simp [sh_z, comps] at hg
    | psi => simp [size] at hn
  | n + 1, z, _, _, _, _, _, _, _, hg => by simp [sh_z, comps] at hg
  | n + 1, psi s y c, a, g', hn, ht, ha, hVa, hua, hg => by
    have hny : size y ≤ n := by simp [size] at hn; omega
    have hnc : size c ≤ n := by simp [size] at hn; omega
    have hns : size (sub s V) ≤ n := by
      have := size_sub_le s V
      simp [size] at hn
      omega
    have htail : g' ∈ comps u (sh V V' c) →
        (∃ w, isOT w = true ∧ V < w ∧ w ≤ a ∧ u ≤ shf V V' w ∧
          g' ∈ comps (shf V V' w) (sh V V' (psi s y c))) ∨ g' ∈ comps u V' := by
      intro hc
      rcases component_raise_to_matched hV hV' hVV hVu n hnc (isOT_rest ht) ha hVa hua hc with
          ⟨w, hw, hVw, hwa, huw, hgw⟩ | hc
      · refine Or.inl ⟨w, hw, hVw, hwa, huw, ?_⟩
        rw [sh_psi_app, comps_app]
        exact List.mem_append.mpr (Or.inr hgw)
      · exact Or.inr hc
    by_cases hVs : V < s
    · rw [sh_psi_gt hVs] at hg
      simp only [comps, List.mem_append] at hg
      rcases hg with hg | hg
      · split at hg
        · simp at hg
        · rename_i hsu
          obtain ⟨b, hb, hVb, hba, hbs, hub⟩ :=
            matched_cap ha (isOT_sub ht) hVa hVs hua (not_lt.mp hsu)
          have hparent : ∀ w, isOT w = true → V < w → w ≤ b →
              ¬ shf V V' s < shf V V' w := by
            intro w hw hVw hwb
            exact not_lt.mpr (shf_mono_old hV hV' hVV hw (isOT_sub ht)
              (le_of_lt hVw) (le_trans hwb hbs))
          have hsb : ¬ shf V V' s < shf V V' b := hparent b hb hVb (le_refl _)
          simp only [List.mem_cons, List.mem_append] at hg
          rcases hg with rfl | hg | hg
          · refine Or.inl ⟨b, hb, hVb, hba, hub, ?_⟩
            rw [sh_psi_gt hVs]
            exact comps_psi_mem_of hsb (Or.inl rfl)
          · rcases component_raise_to_matched hV hV' hVV hVu n hny (isOT_arg ht) hb hVb hub hg with
                ⟨w, hw, hVw, hwb, huw, hgw⟩ | hg
            · refine Or.inl ⟨w, hw, hVw, le_trans hwb hba, huw, ?_⟩
              rw [sh_psi_gt hVs]
              exact comps_psi_mem_of (hparent w hw hVw hwb) (Or.inr (Or.inl hgw))
            · exact Or.inr hg
          · unfold shf at hg
            obtain ⟨P, hP, hPs⟩ := add_eq_app_prefix V' (sh V V' (sub s V))
            rw [hP, comps_app] at hg
            rcases List.mem_append.mp hg with hg | hg
            · obtain ⟨q, hq, hgq⟩ := comps_to_summand hg
              exact Or.inr (comps_of_mem_summands (hPs q hq) hgq)
            · rcases component_raise_to_matched hV hV' hVV hVu n hns
                (isOT_sub_sfx (isOT_sub ht) V) hb hVb hub hg with
                  ⟨w, hw, hVw, hwb, huw, hgw⟩ | hg
              · have hidx : g' ∈ comps (shf V V' w) (shf V V' s) := by
                  unfold shf
                  rw [hP, comps_app]
                  exact List.mem_append.mpr (Or.inr hgw)
                refine Or.inl ⟨w, hw, hVw, le_trans hwb hba, huw, ?_⟩
                rw [sh_psi_gt hVs]
                exact comps_psi_mem_of (hparent w hw hVw hwb) (Or.inr (Or.inr (Or.inl hidx)))
              · exact Or.inr hg
      · exact htail hg
    · rw [sh_psi_le hVs] at hg
      have hsu : lt s u = true := lt_of_le_of_lt (not_lt.mp hVs) hVu
      simp only [comps, hsu, ↓reduceIte, List.nil_append] at hg
      exact htail hg

/-- All new levels above V, including gaps of f, reduce to old interval
alternatives. KA is needed only for the low levels, not for this reduction. -/
theorem above_cut_interval_only {V V' a B A u g' : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a) (hB : isOT B = true)
    (hVD : VDomF V V' a) (hOm : psi (shf V V' a) z z ≤ sh V V' B)
    (hcl : ClosedL a B A) (hVu : V < u) (hua : u ≤ shf V V' a)
    (hg' : g' ∈ comps u (sh V V' B)) :
    g' ≤ sh V V' B ∨ (∃ d ∈ comps u (shf V V' a), g' ≤ d) ∨
      ∃ w g, isOT w = true ∧ V ≤ w ∧ w ≤ a ∧ u ≤ shf V V' w ∧
        g ∈ comps w B ∧ g' = sh V V' g ∧ Persistent w g B A := by
  have hintro : g' ∈ comps u V' →
      g' ≤ sh V V' B ∨ (∃ d ∈ comps u (shf V V' a), g' ≤ d) ∨
        ∃ w g, isOT w = true ∧ V ≤ w ∧ w ≤ a ∧ u ≤ shf V V' w ∧
          g ∈ comps w B ∧ g' = sh V V' g ∧ Persistent w g B A := by
    intro hg
    rcases introduced_bound hVD hOm (show ¬ lt (shf V V' a) u = true from not_lt.mpr hua) hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  rcases (le_iff _ _).mp hVa with hVa | hVa
  · rcases component_raise_to_matched hV hV' hVV hVu (size B) (Nat.le_refl _)
        hB ha hVa hua hg' with ⟨w, hw, hVw, hwa, huw, hgw⟩ | hg
    · rcases high_components_interval_only hV hV' hVV ha hB hw hVw hwa hcl hgw with
          h | ⟨d, hd, hgd⟩ | ⟨g, hg, he, hp⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨d, comps_mono huw hd, hgd⟩)
      · exact Or.inr (Or.inr ⟨w, g, hw, le_of_lt hVw, hwa, huw, hg, he, hp⟩)
    · exact hintro hg
  · subst a
    rcases components_above_cut V V' hVu (size B) (Nat.le_refl _) hg' with
        ⟨g, hg, he⟩ | hg
    · have hgv := comps_mono (le_of_lt (lt_succ_self V)) hg
      have hgo := isOT_of_mem_comps V hB hgv
      rcases hcl V (show ¬ lt V V = true from lt_irrefl' V) g hgv with h | ⟨d, hd, _⟩ | h
      · exact Or.inl (he ▸ sh_le_sh hV hV' (le_of_lt hVV) hgo hB h)
      · rw [comps_self hV] at hd
        simp at hd
      · exact Or.inr (Or.inr ⟨V, g, hV, le_refl _, le_refl _, hua, hgv, he, h⟩)
    · exact hintro hg

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

/-- Right monotonicity of subtraction only needs the lower endpoint standard. -/
theorem sub_lt_sub_right : ∀ {V s t : T}, isOT V = true → isOT s = true → V ≤ s → s < t →
    sub s V < sub t V
  | z, s, t, _, _, _, h => by simpa [sub_z_right] using h
  | psi d e f, z, _, _, _, h, _ => absurd h (not_le_of_gt (T.z_lt_psi _ _ _))
  | psi d e f, psi a b c, z, _, _, _, h => absurd h (T.not_lt_z _)
  | psi d e f, psi a b c, psi a' b' c', hV, hs, hVs, hst => by
    have hht : psi a b z ≤ psi a' b' z := by simpa [head] using head_le_of_lt hst
    by_cases hh : psi d e z < psi a b z
    · have hh' : psi d e z < psi a' b' z := lt_of_lt_of_le hh hht
      rw [sub_psi_psi, sub_psi_psi, if_pos hh, if_pos hh']; exact hst
    · obtain ⟨rfl, rfl, hfc⟩ := rest_le_of_le_head hVs hh
      by_cases hh' : psi d e z < psi a' b' z
      · rw [sub_psi_self, sub_psi_psi, if_pos hh']
        apply lt_of_head_lt
        exact lt_of_le_of_lt (le_trans (head_sub_le (isOT_rest hs) f) (isOT_psi_iff.mp hs).2.2.2.1) hh'
      · have he : psi d e z = psi a' b' z := le_antisymm hht (le_of_not_gt hh')
        cases he
        rw [sub_psi_self, sub_psi_self]
        have hcc : c < c' := by
          rcases T.psi_lt_psi.mp hst with h | ⟨_, h⟩ | ⟨_, _, h⟩
          · exact False.elim (lt_irrefl' _ h)
          · exact False.elim (lt_irrefl' _ h)
          · exact h
        exact sub_lt_sub_right (isOT_rest hV) (isOT_rest hs) hfc hcc

/-- A standard lower endpoint remains below every greater, arbitrary syntax term. -/
theorem sh_lt_right_aux {V V' : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V') :
    ∀ n (a b : T), size a + size b < n → isOT a = true → a < b →
      sh V V' a < sh V V' b
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, a, b, hn, ha, hab => by
    cases b with
    | z => exact False.elim (T.not_lt_z _ hab)
    | psi d e f =>
      cases a with
      | z => rw [sh_z]; exact lt_of_le_of_ne (z_le _) (Ne.symm (sh_ne_z (by simp)))
      | psi s y c =>
        have hsz : ∀ x, size x ≤ size s → size x + size (sub d V) < n := by
          intro x hx; have := size_sub_le d V; simp [size] at hn; omega
        have hf : V ≤ s → s < d → shf V V' s < shf V V' d := by
          intro hVs hsd
          unfold shf
          apply add_lt_add_left
          exact sh_lt_right_aux hV hV' hVV n _ _ (hsz _ (size_sub_le s V))
            (isOT_sub_sfx (isOT_sub ha) V) (sub_lt_sub_right hV (isOT_sub ha) hVs hsd)
        have hVf : ∀ {w : T}, V < w → V < shf V V' w := by
          intro w hVw
          refine lt_trans hVV ?_
          unfold shf
          have h1 := add_lt_add_left V' (show z < sh V V' (sub w V) from
            lt_of_le_of_ne (z_le _) (Ne.symm (sh_ne_z (sub_ne_z_gen hVw))))
          simpa using h1
        have ihy : y < e → sh V V' y < sh V V' e := fun h =>
          sh_lt_right_aux hV hV' hVV n y e (by simp [size] at hn; omega) (isOT_arg ha) h
        have ihc : c < f → sh V V' c < sh V V' f := fun h =>
          sh_lt_right_aux hV hV' hVV n c f (by simp [size] at hn; omega) (isOT_rest ha) h
        rw [T.psi_lt_psi] at hab
        by_cases hs : V < s <;> by_cases hd : V < d
        · rw [sh_psi_gt hs, sh_psi_gt hd, T.psi_lt_psi]
          rcases hab with h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩
          · exact Or.inl (hf (le_of_lt hs) h)
          · exact Or.inr (Or.inl ⟨rfl, ihy h⟩)
          · exact Or.inr (Or.inr ⟨rfl, rfl, ihc h⟩)
        · exfalso
          rcases hab with h | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
          · exact hd (lt_trans hs h)
          · exact hd hs
          · exact hd hs
        · rw [sh_psi_le hs, sh_psi_gt hd, T.psi_lt_psi]
          exact Or.inl (lt_of_le_of_lt (not_lt.mp hs) (hVf hd))
        · rw [sh_psi_le hs, sh_psi_le hd, T.psi_lt_psi]
          rcases hab with h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨rfl, h⟩)
          · exact Or.inr (Or.inr ⟨rfl, rfl, ihc h⟩)

theorem sh_lt_right {V V' a b : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hab : a < b) : sh V V' a < sh V V' b :=
  sh_lt_right_aux hV hV' hVV _ a b (Nat.lt_succ_self _) ha hab

theorem sh_le_right {V V' a b : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hab : a ≤ b) : sh V V' a ≤ sh V V' b := by
  rcases (le_iff _ _).mp hab with h | rfl
  · exact le_of_lt (sh_lt_right hV hV' hVV ha h)
  · exact le_refl _

theorem shf_le_right {V V' a b : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a) (hab : a ≤ b) : shf V V' a ≤ shf V V' b := by
  rcases (le_iff _ _).mp hab with h | rfl
  · unfold shf
    exact le_of_lt (add_lt_add_left V'
      (sh_lt_right hV hV' hVV (isOT_sub_sfx ha V) (sub_lt_sub_right hV ha hVa h)))
  · exact le_refl _

/-- Domination after shifting source components, without requiring source terms standard. -/
def ShiftDom (V V' w u r c : T) : Prop :=
  ∀ d ∈ Gc w r, ∃ e ∈ Gc u c, sh V V' d ≤ e

private theorem shiftDom_zero (V V' w u c : T) : ShiftDom V V' w u z c := by
  intro d hd
  have hd0 : d = z := by simpa [Gc, comps] using hd
  subst d
  exact ⟨z, List.mem_cons_self, by simp⟩

private theorem shiftDom_of_nil {V V' w u r c : T} (hr : comps w r = []) :
    ShiftDom V V' w u r c := by
  intro d hd
  have hd0 : d = z := by simpa [Gc, hr] using hd
  subst d
  exact ⟨z, List.mem_cons_self, by simp⟩

private theorem comps_succ_high {w : T} (hw : z < w) (t : T) :
    comps w (succ t) = comps w t := by
  have hzw : lt z w = true := hw
  simp [succ, comps_app, one, comps, hzw]

private theorem comps_above_standard {w t : T} (ht : isOT t = true) (hw : lev t < w) :
    comps w t = [] := by
  apply comps_eq_nil_of_lev
  intro q hq
  have hqle := lev_le_of_le (summands_le_head ht q hq)
  have hlev : lev (head t) = lev t := by cases t <;> rfl
  rw [hlev] at hqle
  exact lt_of_le_of_lt hqle hw

private theorem shiftDom_psi {V V' w u p x r q y t : T}
    (hseen : ¬ p < w → ¬ q < u) (hxy : sh V V' x ≤ y)
    (hp : ShiftDom V V' w u p q) (hx : ShiftDom V V' w u x y)
    (hr : ShiftDom V V' w u r t) :
    ShiftDom V V' w u (psi p x r) (psi q y t) := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact ⟨z, List.mem_cons_self, by simp⟩
  simp only [comps, List.mem_append] at hd
  rcases hd with hd | hd
  · by_cases hpw : lt p w = true
    · rw [if_pos hpw] at hd
      simp at hd
    · rw [if_neg hpw] at hd
      have hqu := hseen hpw
      simp only [List.mem_cons, List.mem_append] at hd
      rcases hd with rfl | hd | hd
      · exact ⟨y, List.mem_cons_of_mem _ (comps_psi_mem_of hqu (Or.inl rfl)), hxy⟩
      · obtain ⟨e, he, hde⟩ := hx d (List.mem_cons_of_mem _ hd)
        exact ⟨e, gc_arg hqu he, hde⟩
      · obtain ⟨e, he, hde⟩ := hp d (List.mem_cons_of_mem _ hd)
        exact ⟨e, gc_index hqu he, hde⟩
  · obtain ⟨e, he, hde⟩ := hr d (List.mem_cons_of_mem _ hd)
    exact ⟨e, gc_tail he, hde⟩

private theorem shiftDom_fixed {V V' w u t : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hw : isOT w = true) (hVw : V < w) (hu : u ≤ shf V V' w) (ht : isOT t = true) :
    ShiftDom V V' w u t (sh V V' t) := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact ⟨z, List.mem_cons_self, by simp⟩
  · exact ⟨sh V V' d, List.mem_cons_of_mem _ (high_component_sh hV hV' hVV hw hVw hu ht hd), le_refl _⟩

private theorem shiftDom_index {V V' w u t : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hw : isOT w = true) (hVw : V < w) (hu : u ≤ shf V V' w) (ht : isOT t = true) :
    ShiftDom V V' w u t (shf V V' t) := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact ⟨z, List.mem_cons_self, by simp⟩
  · exact ⟨sh V V' d, List.mem_cons_of_mem _ (high_index_sh hV hV' hVV ht hw hVw hu hd), le_refl _⟩

/-- A target interval term admits a smaller shifted source above B with
sufficient source components. The source may be arbitrary syntax. -/
theorem shift_interval_coinitial {V V' w u : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hw : isOT w = true) (hVw : V < w) (hu : u ≤ shf V V' w) :
    ∀ {B : T}, isOT B = true → ∀ c, sh V V' B < c →
      ∃ r, B < r ∧ sh V V' r ≤ c ∧ ShiftDom V V' w u r c := by
  intro B
  induction B with
  | z =>
    intro _ c hc
    refine ⟨one, T.z_lt_psi _ _ _, ?_, ?_⟩
    · simpa [succ, sh_one] using succ_le_of_lt hc
    · apply shiftDom_of_nil
      exact comps_above_standard isOT_one (lt_of_le_of_lt (z_le V) hVw)
  | psi p x t ihp ihx iht =>
    intro hB c hc
    have hp := isOT_sub hB
    have hx := isOT_arg hB
    have ht := isOT_rest hB
    have hzw : z < w := lt_of_le_of_lt (z_le V) hVw
    by_cases hVp : V < p
    · rw [sh_psi_gt hVp] at hc
      cases c with
      | z => exact False.elim (T.not_lt_z _ hc)
      | psi q y s =>
        have hseen : ¬ p < w → ¬ shf V V' p < u := by
          intro hpw
          exact not_lt.mpr (le_trans hu
            (shf_le_right hV hV' hVV hw (le_of_lt hVw) (not_lt.mp hpw)))
        rcases T.psi_lt_psi.mp hc with hpq | ⟨rfl, hxy⟩ | ⟨rfl, rfl, hts⟩
        · by_cases hVl : V < lev p
          · have hfp : shf V V' p = sh V V' p := shf_eq_sh hV hV' hVV hVl
            rw [hfp] at hpq
            obtain ⟨v, hpv, hvq, hvd⟩ := ihp hp q hpq
            have hVlv : V < lev v := lt_of_lt_of_le hVl (lev_le_of_le (le_of_lt hpv))
            have hVv : V < v := lt_trans hVp hpv
            have hfv : shf V V' v = sh V V' v := shf_eq_sh hV hV' hVV hVlv
            refine ⟨psi v z z, T.psi_lt_psi.mpr (Or.inl hpv), ?_, ?_⟩
            · rw [sh_psi_gt hVv, hfv, sh_z]
              exact psi_mono_coords hvq (z_le _) (z_le _)
            · apply shiftDom_psi ?_ (by simp [z_le]) hvd
                (shiftDom_zero V V' w u y) (shiftDom_zero V V' w u s)
              intro hvw
              exact not_lt.mpr (le_trans hu (le_trans
                (by rw [← hfv]; exact shf_le_right hV hV' hVV hw (le_of_lt hVw) (not_lt.mp hvw)) hvq))
          · have hp0 : comps w p = [] := comps_above_standard hp
              (lt_of_le_of_lt (not_lt.mp hVl) hVw)
            have hsv0 : comps w (succ p) = [] := by rw [comps_succ_high hzw, hp0]
            have hVsp : V < succ p := lt_trans hVp (lt_succ_self p)
            have hq : shf V V' (succ p) ≤ q := by
              rw [shf_succ hV hV' hVV hp (le_of_lt hVp)]
              exact succ_le_of_lt hpq
            refine ⟨psi (succ p) z z, T.psi_lt_psi.mpr (Or.inl (lt_succ_self p)), ?_, ?_⟩
            · rw [sh_psi_gt hVsp, sh_z]
              exact psi_mono_coords hq (z_le _) (z_le _)
            · apply shiftDom_psi ?_ (by simp [z_le]) (shiftDom_of_nil hsv0)
                (shiftDom_zero V V' w u y) (shiftDom_zero V V' w u s)
              intro hsvw
              exact not_lt.mpr (le_trans hu (le_trans
                (shf_le_right hV hV' hVV hw (le_of_lt hVw) (not_lt.mp hsvw)) hq))
        · obtain ⟨e, hxe, hey, hed⟩ := ihx hx y hxy
          refine ⟨psi p e z, T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨rfl, hxe⟩)), ?_, ?_⟩
          · rw [sh_psi_gt hVp, sh_z]
            exact psi_mono_coords (le_refl _) hey (z_le _)
          · exact shiftDom_psi hseen hey (shiftDom_index hV hV' hVV hw hVw hu hp)
              hed (shiftDom_zero V V' w u s)
        · obtain ⟨r, htr, hrs, hrd⟩ := iht ht s hts
          refine ⟨psi p x r, T.psi_lt_psi.mpr (Or.inr (Or.inr ⟨rfl, rfl, htr⟩)), ?_, ?_⟩
          · rw [sh_psi_gt hVp]
            exact psi_mono_coords (le_refl _) (le_refl _) hrs
          · exact shiftDom_psi hseen (le_refl _) (shiftDom_index hV hV' hVV hw hVw hu hp)
              (shiftDom_fixed hV hV' hVV hw hVw hu hx) hrd
    · have hB0 : comps w (psi p x t) = [] := comps_above_standard hB
        (lt_of_le_of_lt (not_lt.mp hVp) hVw)
      refine ⟨succ (psi p x t), lt_succ_self _, ?_, ?_⟩
      · simpa only [succ, sh_app, sh_one] using succ_le_of_lt hc
      · apply shiftDom_of_nil
        rw [comps_succ_high hzw, hB0]

/-- Interval persistence for moving components, without any frame hypotheses. -/
theorem persistent_sh_high {V V' w u g B A : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hw : isOT w = true) (hVw : V < w) (hu : u ≤ shf V V' w)
    (hg : isOT g = true) (hB : isOT B = true) (hA : isOT A = true)
    (hp : Persistent w g B A) :
    Persistent u (sh V V' g) (sh V V' B) (sh V V' A) := by
  intro c hcB hcA
  obtain ⟨r, hBr, hrc, hdom⟩ := shift_interval_coinitial hV hV' hVV hw hVw hu hB c hcB
  have hrA : r ≤ A := by
    by_contra hn
    have hAr : A < r := lt_of_not_ge hn
    exact not_lt_of_ge (le_trans hrc hcA) (sh_lt_right hV hV' hVV hA hAr)
  obtain ⟨d, hd, hgd⟩ := hp r hBr hrA
  obtain ⟨e, he, hde⟩ := hdom d hd
  exact ⟨e, he, le_trans (sh_le_right hV hV' hVV hg hgd) hde⟩

#print axioms persistent_sh_high

#print axioms sh_lt_right

#print axioms persistent_sh_index
#print axioms persistent_sh_argument_bound
#print axioms persistent_app
#print axioms above_cut_interval_only
#print axioms component_raise_to_matched
#print axioms middle_components_interval_only
#print axioms components_above_cut
#print axioms high_components_interval_only
#print axioms high_component_sh
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
