/-
Real-copy FrameDom: partial reductions after replacing the false pure FDsh.
No additional residual or term guard is introduced. The n>=3 old-V ancestor
bound uses the existing T2VAncStep hypothesis at n-1. The n=2 prefix case and
retained low interval transport remain separate proof obligations.
-/
import Ytosk.V3T2VSFC
import Ytosk.V3FDCut
import Ytosk.V3T2CutDom

namespace Ytosk.FDCopy
open T

/-- The old source matrix has VAnc at every guarded copy pair once its
expansion index is at least two. No invariant of the target N is extracted. -/
theorem old_vAnc_of_t2VAncStep {M : Mat} (hVS : T2VAncStep M)
    {n r i : Nat} (hn : 3 ≤ n) {ρP : Valn}
    (hCP : Cons (expand M (n - 1)) ρP) (hGP : Good3 (expand M (n - 1)) ρP)
    (hg : TRIO.le1 (expand M (n - 1)) r i) : VAnc ρP r i :=
  vAnc_of_step hCP hGP (hVS (n - 1) (by omega) ρP hCP) hg

/-- Same application interface at the actual source matrix G2. The equality
is available from expand_eq_gexp in the standard t2 context. -/
theorem old_vAnc_copy {M : Mat} (hVS : T2VAncStep M)
    {n r L i : Nat} (hn : 3 ≤ n)
    (he : expand M (n - 1) = G2 M r L (n - 1)) {ρP : Valn}
    (hCP : Cons (G2 M r L (n - 1)) ρP) (hGP : Good3 (G2 M r L (n - 1)) ρP)
    (hg : TRIO.le1 (G2 M r L (n - 1)) r i) : VAnc ρP r i := by
  rw [← he] at hCP hGP hg
  exact old_vAnc_of_t2VAncStep hVS hn hCP hGP hg

/-- At a single low level already covered by the existing KA conjunct,
old VAnc components are cheap: below the new child's Omega or a new parent
component. This lemma does not extend the level range of T2VRAK. -/
theorem old_vAnc_component {ρP : Valn} {r i : Nat} {V' s u g : T}
    (hAnc : VAnc ρP r i)
    (hfa : ρP.v i ≤ shf (ρP.v r) V' s)
    (hKA : ∀ d ∈ comps u (ρP.v i),
      d ≤ psi (shf (ρP.v r) V' (ρP.v i)) z z ∨
        ∃ d' ∈ comps u (shf (ρP.v r) V' (ρP.v i)), d ≤ d')
    (hfas : shf (ρP.v r) V' (ρP.v i) ≤ shf (ρP.v r) V' s)
    (hg : g ∈ comps u (ρP.v r)) :
    g ≤ psi (shf (ρP.v r) V' s) z z ∨
      ∃ d ∈ comps u (shf (ρP.v r) V' (ρP.v i)), g ≤ d := by
  have om_mono : ∀ {a b : T}, a ≤ b → psi a z z ≤ psi b z z := by
    intro a b hab
    rcases (le_iff _ _).mp hab with hab | rfl
    · exact psi_le_psi_of (Or.inl hab)
    · exact le_refl _
  rcases hAnc u g hg with h | ⟨d, hd, hgd⟩
  · exact Or.inl (le_trans h (om_mono hfa))
  · rcases hKA d hd with h | ⟨d', hd', hdd'⟩
    · exact Or.inl (le_trans hgd (le_trans h (om_mono hfas)))
    · exact Or.inr ⟨d', hd', le_trans hgd hdd'⟩

/-- The ordinary expansion identity, from the real t2 source context. -/
theorem expand_eq_G2_ctx {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (_C : StepCtxT2 M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (m : Nat) : expand M m = G2 M r L m := by
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hl2 : 2 ≤ M.length := by omega
  have he : M.length - 1 = r + L := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧
      TRIO.entry M 1 (M.length - 1) = 0 ∧ TRIO.entry M 2 (M.length - 1) = 0) :=
    fun h => hz ((col_zero_iff M _).mpr h)
  have h := expand_eq_gexp M m hl2 hzT (by rw [h2, he]; exact hr)
  rw [h2, he] at h
  simp only [show (0 < 2) from by omega, show (1 < 2) from by omega,
    if_true, Nat.add_sub_cancel_left] at h
  exact h

/-- No expansion-equality premise is needed at actual n>=3 source frames. -/
theorem old_vAnc_copy_ctx {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hVS : T2VAncStep M)
    {r L n i : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hn : 3 ≤ n) {ρP : Valn} (hCP : Cons (G2 M r L (n - 1)) ρP)
    (hGP : Good3 (G2 M r L (n - 1)) ρP)
    (hg : TRIO.le1 (G2 M r L (n - 1)) r i) : VAnc ρP r i :=
  old_vAnc_copy hVS hn (expand_eq_G2_ctx C hz h2 hlen hr _) hCP hGP hg

/-- The measured shared-index zero-state exceptions have FrameDom without
old FrameDom, VAnc, KA, KG, VDomF or any interval transport. -/
theorem frameDom_sh_zero_of_shared_level {V V' a s y Y : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a) (has : a ≤ s)
    (hH : H (shf V V' s) (sh V V' y) = psi (shf V V' s) Y z) :
    FrameDom (shf V V' a) (sh V V' z) (shf V V' s)
      (H (shf V V' s) (sh V V' y)) := by
  rw [sh_z, hH]
  exact FDCut.zero_FrameDom_of_shared_level
    (ClShLGuarded.shf_le_right hV hV' hVV ha hVa has)

/-- Old-V components at an actual KAG-covered source level require no
interval escape. The level restriction is kept explicit in hKA. -/
theorem old_vAnc_component_of_KAG {ρP : Valn} {r i : Nat} {V' s u g : T}
    {Lv : List T} {cv : T}
    (hAnc : VAnc ρP r i) (hV : isOT (ρP.v r) = true)
    (hV' : isOT V' = true) (hVV : ρP.v r < V')
    (ha : isOT (ρP.v i) = true) (hs : isOT s = true)
    (hVa : ρP.v r ≤ ρP.v i) (hVs : ρP.v r < s) (has : ρP.v i ≤ s)
    (hK : KAG (ρP.v r) V' (ρP.v i) Lv cv u)
    (hg : g ∈ comps u (ρP.v r)) :
    g ≤ psi (shf (ρP.v r) V' s) z z ∨
      ∃ d ∈ comps u (shf (ρP.v r) V' (ρP.v i)), g ≤ d := by
  apply old_vAnc_component hAnc
    (le_trans has (le_shf_self hV hV' (le_of_lt hVV) hs (le_of_lt hVs))) hK.1
    (ClShLGuarded.shf_le_right hV hV' hVV ha hVa has) hg

/-- State components absent from the child's index persist through all three
PH kinds. This is the component certificate for the measured 3 cut exceptions;
no bound on the other components of s is required. -/
theorem state_component_of_kind {B s y u g C : T}
    (hot : isOT (psi s y z) = true)
    (hK : PH3cKindG B (split y (psi (succ s) z z)).1
      (split y (psi (succ s) z z)).2 s)
    (hg : g ∈ comps u B) (hgs : g ∉ comps u s)
    (hBC : B < C) (hCX : C ≤ H s y) :
    ∃ d ∈ Gc u C, g ≤ d := by
  have hPrefix : ∀ R, C ≤ app B R → ∃ d ∈ Gc u C, g ≤ d := by
    intro R hCR
    obtain ⟨c0, hc0, _, _⟩ := between_app (A := B) (x := z) (y := R)
      (by rw [app_z_right]; exact hBC) hCR
    refine ⟨g, List.mem_cons_of_mem _ ?_, le_refl _⟩
    rw [hc0, comps_app]
    exact List.mem_append_left _ hg
  rw [H_eq hot] at hCX
  rcases hK with ⟨hhi, _⟩ | ⟨hne, ⟨R, _, hR⟩ | ⟨_, hc⟩⟩
  · rw [hhi] at hCX
    exact hPrefix _ hCX
  · rw [hR, app_assoc] at hCX
    exact hPrefix _ hCX
  · have hD : CutDom s u C g ∨
        (∃ c0, C = app (split y (psi (succ s) z z)).1 c0) ∧
          CutDom s u (split y (psi (succ s) z z)).1 g := by
      by_cases hCh : C ≤ (split y (psi (succ s) z z)).1
      · exact Or.inl (cutsNS_dom _ hc hBC hCh g hg)
      · right
        have hhiC := lt_of_not_ge hCh
        obtain ⟨c0, hc0, _, _⟩ := between_app (x := z) (c := C)
          (by rw [app_z_right]; exact hhiC) hCX
        refine ⟨⟨c0, hc0⟩, cutsNS_dom _ hc ?_ (le_refl _) g hg⟩
        rcases (le_iff _ _).mp (cutsNSG_le hc) with h | h
        · exact h
        · exact False.elim (hne h.symm)
    rcases hD with h | ⟨⟨c0, hc0⟩, h⟩
    · rcases h with rfl | h | ⟨d, hd, hgd⟩
      · exact ⟨z, List.mem_cons_self, le_refl _⟩
      · exact False.elim (hgs h)
      · exact ⟨d, List.mem_cons_of_mem _ hd, hgd⟩
    · rcases h with rfl | h | ⟨d, hd, hgd⟩
      · exact ⟨z, List.mem_cons_self, le_refl _⟩
      · exact False.elim (hgs h)
      · refine ⟨d, List.mem_cons_of_mem _ ?_, hgd⟩
        rw [hc0, comps_app]
        exact List.mem_append_left _ hd

#print axioms old_vAnc_of_t2VAncStep
#print axioms old_vAnc_copy
#print axioms old_vAnc_component
#print axioms old_vAnc_copy_ctx
#print axioms frameDom_sh_zero_of_shared_level
#print axioms old_vAnc_component_of_KAG
#print axioms state_component_of_kind
end Ytosk.FDCopy
