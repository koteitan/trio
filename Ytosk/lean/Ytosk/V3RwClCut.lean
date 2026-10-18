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

#print axioms closedL_of_component_raise

#print axioms omega_le_of_shadow_cut
#print axioms inv_closed_at_path_level

end Ytosk.RwClCut
