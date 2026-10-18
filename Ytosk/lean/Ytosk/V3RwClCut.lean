/-
Cut-shaped shadow frames: the Omega_s alternative is already bounded by B.
At parent/path levels Inv3V2.vra supplies the remaining seed bound. The bridge
from these levels to every level required by RwClosedL remains explicit.
-/
import Ytosk.V3ClShLV
import Ytosk.V3Inv2

namespace Ytosk.RwClCut

open T ClShLGuarded

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

/-- All existing Inv3V2 fields suffice at the parent and rewrite-path levels.
No claim of coverage of arbitrary lower levels is built into this theorem. -/
theorem inv_closed_at_path_level {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (I : Inv3V2 M ρ rk) {i : Nat} (hi : i < M.length)
    {L : List Nat} {c : Nat} {R : List Nat} (hCL : CL M i = L ++ c :: R)
    {s y : T} (ho : ρ.o c = psi s y z)
    (ht : lt (stB ρ i L) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true)
    (hhi : stB ρ i L < (split y (psi (succ s) z z)).1)
    (hnp : ¬ ∃ R', (split y (psi (succ s) z z)).1 = app (stB ρ i L) R')
    {u : T} (hU : u = ρ.v i ∨ PathLvAll M ρ i u) (hu : ¬ lt (ρ.v i) u = true) :
    ∀ g ∈ comps u (stB ρ i L), g ≤ stB ρ i L ∨
      (∃ d ∈ comps u (ρ.v i), g ≤ d) ∨
      Persistent u g (stB ρ i L) (H (ρ.v i) (H s y)) := by
  by_cases hBz : stB ρ i L = z
  · simp [hBz, comps]
  · have hK := I.ph i hi L c R hCL s y ho hBz ht
    have hcut : stB ρ i L ∈ cutsNSG s (split y (psi (succ s) z z)).1 := by
      rcases hK with ⟨h, _⟩ | ⟨_, ⟨R', _, h⟩ | ⟨_, h⟩⟩
      · exact False.elim (lt_irrefl' _ (h ▸ hhi))
      · exact False.elim (hnp ⟨R', h⟩)
      · exact h
    have hB : isOT (stB ρ i L) = true := isOT_arg (I.fo i hi L c R hCL)
    have hcM : c < M.length := by
      have hccl : c ∈ CL M i := by rw [hCL]; simp
      exact (mem_children (cl_mem_children hccl)).2
    have hsy : isOT (psi s y z) = true := by rw [← ho]; exact I.good.ot_o c hcM
    apply closed_at_of_shadow_cut (I.good.ot_v i hi) hB hsy (le_of_trig ht.2) hcut
    have hhinz : (split y (psi (succ s) z z)).1 ≠ z := by
      intro h
      exact T.not_lt_z _ (h ▸ hhi)
    exact I.vra i c L R s y hCL ho ht hhinz u hU hu

/-- An interval witness at a higher level is still a witness below it. -/
theorem persistent_lower_level {u w g B A : T} (huw : u ≤ w)
    (hp : Persistent w g B A) : Persistent u g B A := by
  intro c hBc hcA
  obtain ⟨d, hd, hgd⟩ := hp c hBc hcA
  rcases List.mem_cons.mp hd with rfl | hd
  · exact ⟨z, List.mem_cons_self, hgd⟩
  · exact ⟨d, List.mem_cons_of_mem _ (comps_mono huw hd), hgd⟩

/-- It suffices to raise each nonsmall component to some checked level.
The lower level itself need not be a rewrite-path level. -/
theorem closedL_of_component_raise {a B A : T} {U : T → Prop}
    (hchecked : ∀ w, U w → ¬ lt a w = true → ∀ g ∈ comps w B,
      g ≤ B ∨ (∃ d ∈ comps w a, g ≤ d) ∨ Persistent w g B A)
    (hraise : ∀ u, ¬ lt a u = true → ∀ g ∈ comps u B,
      g ≤ B ∨ ∃ w, U w ∧ u ≤ w ∧ w ≤ a ∧ g ∈ comps w B) :
    ClosedL a B A := by
  intro u hu g hg
  rcases hraise u hu g hg with h | ⟨w, hw, huw, hwa, hgw⟩
  · exact Or.inl h
  · rcases hchecked w hw (not_lt.mpr hwa) g hgw with h | ⟨d, hd, hgd⟩ | hp
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨d, comps_mono huw hd, hgd⟩)
    · exact Or.inr (Or.inr (persistent_lower_level huw hp))

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

/-- G3 cut shape and the existing level-restricted seed bounds give the
complete shadow-consumer conclusion, without an all-level ClosedL premise. -/
theorem shadow_hShL_from_cut {U : T → Prop} {a B s y y' : T}
    (ha : isOT a = true) (hBot : isOT B = true) (hc : isOT (psi s y z) = true)
    (hcut : B ∈ cutsNSG s (split y (psi (succ s) z z)).1)
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
  exact closed_at_of_shadow_cut ha hBot hc (le_of_trig ht.2) hcut (hVR u hU hu)

/-- The actual shadow premise consumed by relR_frameUL follows pointwise
from Inv3V2, provided U consists of its parent/rewrite-path levels. This
requires neither HRwClL nor a hypothesis about unused levels. -/
theorem inv_shadow_hShL {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (I : Inv3V2 M ρ rk) {i : Nat} (hi : i < M.length)
    {L : List Nat} {c : Nat} {R : List Nat} (hCL : CL M i = L ++ c :: R)
    {s y y' : T} (ho : ρ.o c = psi s y z) {U : T → Prop}
    (hU : ∀ u, U u → u = ρ.v i ∨ PathLvAll M ρ i u)
    (hBc : ∀ q ∈ summands (stB ρ i L), psi s y z ≤ q)
    (ht : lt (stB ρ i L) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true)
    (hhi : stB ρ i L < (split y (psi (succ s) z z)).1)
    (hnp : ¬ ∃ R', (split y (psi (succ s) z z)).1 = app (stB ρ i L) R')
    (hnt : ¬ (lt (stB ρ i L) y' = true ∧ lt (psi (ρ.v i) z z) (psi s y' z) = true))
    (hy'z : y' ≠ z) (hl : Lhd z (psi s y' z) (psi s y z))
    (hX'ot : isOT (psi (ρ.v i) (app (stB ρ i L) (psi s y' z)) z) = true) :
    ∀ u, U u → ¬ lt (ρ.v i) u = true →
      ∀ g ∈ comps u (app (stB ρ i L) (psi s y' z)),
        g < app (stB ρ i L) (psi s y' z) ∨
          (∃ d ∈ comps u (ρ.v i), g ≤ d) ∨
          Persistent u g (H (ρ.v i) (app (stB ρ i L) (psi s y' z)))
            (H (ρ.v i) (H s y)) := by
  apply shadow_hShL_on_levels hBc ht hnt hy'z hl hX'ot
  · intro u hu hau
    exact inv_closed_at_path_level I hi hCL ho ht hhi hnp (hU u hu) hau
  · intro u hu hau
    have hhinz : (split y (psi (succ s) z z)).1 ≠ z := by
      intro h
      exact T.not_lt_z _ (h ▸ hhi)
    exact I.vra i c L R s y hCL ho ht hhinz u (hU u hu) hau

#print axioms inv_shadow_hShL

#print axioms shadow_hShL_from_cut

#print axioms closedL_of_component_raise

#print axioms omega_le_of_shadow_cut
#print axioms inv_closed_at_path_level

end Ytosk.RwClCut
