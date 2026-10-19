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

/-- Row-1 ancestry of a prefix is also ancestry of the whole matrix. -/
theorem le1_take_forward {N : Mat} {k : Nat} :
    ∀ m r i, i < m → TRIO.le1 (N.take k) r i → TRIO.le1 N r i
  | 0, _, _, hi, _ => False.elim (Nat.not_lt_zero _ hi)
  | m + 1, r, i, hi, hg => by
    have hiN : i < N.length := by
      have hiT := hg.2.1
      rw [List.length_take] at hiT
      omega
    by_cases hir : i = r
    · subst hir
      exact le1_self hiN
    · obtain ⟨p, hp, hgp⟩ := le1_par1_down hg hir
      have hpi : p < i := par_lt _ 1 _ _ hp
      have hik : i < k := by
        have hiT := hg.2.1
        rw [List.length_take] at hiT
        omega
      have hpN : par N 1 i = some p := by
        rw [← par_take N 1 i hik]
        exact hp
      exact le1_par1_up (le1_take_forward m r p (by omega) hgp) hpN hiN

/-- Restrict the ancestor conclusion using ONLY equality of the two v values.
Cons of the restricted valuation is not assumed or inferred. -/
theorem vAnc_of_prefix_pair {N : Mat} {k r i : Nat} {σ ρP : Valn}
    (hCN : Cons N σ) (hGN : Good3 N σ) (hVS : VAncStep N σ)
    (hg : TRIO.le1 (N.take k) r i)
    (hvr : σ.v r = ρP.v r) (hvi : σ.v i = ρP.v i) : VAnc ρP r i := by
  have ha := vAnc_of_step hCN hGN hVS
    (le1_take_forward (i + 1) r i (Nat.lt_succ_self _) hg)
  intro u g hgv
  rw [← hvr] at hgv
  have h := ha u g hgv
  rw [hvi] at h
  exact h

/-- n=2 uses hVS at the target index 2, with the structural prefix identity
proved here. Only agreement of the two actually used v values remains explicit. -/
theorem old_vAnc_base_of_pair_values {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hVS : T2VAncStep M)
    {r L i : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    {σ ρP : Valn} (hCN : Cons (G2 M r L 2) σ) (hGN : Good3 (G2 M r L 2) σ)
    (hg : TRIO.le1 (G2 M r L 1) r i)
    (hvr : σ.v r = ρP.v r) (hvi : σ.v i = ρP.v i) : VAnc ρP r i := by
  have hP : G2 M r L 1 = M.take (r + L) := gexp_one_gen hlen
  have hN : (G2 M r L 2).take (r + L) = M.take (r + L) :=
    gexp_take_x hlen (by omega)
  have he := expand_eq_G2_ctx C hz h2 hlen hr 2
  have hstep : VAncStep (G2 M r L 2) σ := by
    have h := hVS 2 (by omega) σ (by rw [he]; exact hCN)
    rw [he] at h
    exact h
  apply vAnc_of_prefix_pair hCN hGN hstep (k := r + L) _ hvr hvi
  rw [hN, ← hP]
  exact hg

/-- A counted child in the shorter matrix rules out a v change in one drop.
This uses chg_struct, rather than equality of full prefix valuations. -/
theorem v_take_of_counted_child {M : Mat} {ρ τ : Valn} {rkT : Bool → Nat → Nat}
    (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {x i c : Nat} (hx : x + 1 = M.length) (hi : i < x)
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT)
    (hc : c ∈ CL (M.take x) i) : τ.v i = ρ.v i := by
  apply (chg_off hx hC hG hT hRT i hi).2
  intro hchg
  have hTop := (chg_struct hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hchg).1 rfl hi
  have hcCh := cl_mem_children hc
  have hcCnt : Counted (M.take x) i c := by
    unfold CL at hc
    exact of_decide_eq_true (List.mem_filter.mp hc).2
  exact hTop.2.1 c hcCh hcCnt

/-- A row-1 child remaining in the prefix also rules out a v change in one drop.
This handles the ancestor r even when r's own counted list is empty. -/
theorem v_take_of_par1_child {M : Mat} {ρ τ : Valn} {rkT : Bool → Nat → Nat}
    (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {x i c : Nat} (hx : x + 1 = M.length) (hi : i < x) (hc : c < x)
    (hT : Cons (M.take x) τ) (hRT : Rk (M.take x) rkT)
    (hp : par M 1 c = some i) : τ.v i = ρ.v i := by
  apply (chg_off hx hC hG hT hRT i hi).2
  intro hchg
  have hTop := (chg_struct hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hchg).1 rfl hi
  exact hTop.2.2 c hc hp

/-- The precise remaining pointwise FrameDom conclusion, not a new residual. -/
def RetainedLowNeed (V V' a B s y u g : T) : Prop :=
  ∀ C, sh V V' B < C → psi (shf V V' s) z z < C →
    C ≤ H (shf V V' s) (sh V V' y) →
    ∃ d ∈ C :: (comps u C ++ comps u (shf V V' a)), g ≤ d

/-- The retained low branch left after state/Omega/parent bounds, the shared
zero-state endpoint, and the state-only cut component certificate. This is a
branch description, not an assertion that it is realizable in a Std matrix. -/
def RetainedLowPending (V V' a B s y u g : T) : Prop :=
  u ≤ V ∧ u ≤ shf V V' a ∧
  (g ∈ comps u B ∨ g ∈ comps u s) ∧
  g ∈ comps u (shf V V' s) ∧
  ¬ g ≤ sh V V' B ∧ ¬ g ≤ psi (shf V V' s) z z ∧
  (∀ d ∈ comps u (shf V V' a), ¬ g ≤ d) ∧
  ¬ (sh V V' B = z ∧ ∃ Y,
    H (shf V V' s) (sh V V' y) = psi (shf V V' s) Y z)

/-- The exact out-of-path retained branch at one real source frame. This Prop
is merely the outstanding goal; it is not added to any top theorem. The full
matrix context and its invariants must discharge it. -/
def RetainedLowOutsidePath (P : Mat) (ρP : Valn) (r i : Nat)
    (V' : T) (Lc : List Nat) (s y : T) : Prop :=
  ∀ u g, ¬ LevAt P ρP i u →
    RetainedLowPending (ρP.v r) V' (ρP.v i)
      (spArg (ρP.v i) z (sumN (Lc.map ρP.o))) s y u g →
    RetainedLowNeed (ρP.v r) V' (ρP.v i)
      (spArg (ρP.v i) z (sumN (Lc.map ρP.o))) s y u g

/-- The already formal zero-state counterexample has old ancestor domination
at ALL levels: a=V+1 contains every component of V. Its failure was KA, not
old VAnc. This does not assert any matrix/path realization of those terms. -/
theorem zero_counterexample_old_ancestor :
    ∀ u g, g ∈ comps u FDCut.ZeroStateCounterexample.V →
      g ≤ psi FDCut.ZeroStateCounterexample.a z z ∨
        ∃ d ∈ comps u FDCut.ZeroStateCounterexample.a, g ≤ d := by
  intro u g hg
  right
  refine ⟨g, ?_, le_refl _⟩
  change g ∈ comps u (app FDCut.ZeroStateCounterexample.V one)
  rw [comps_app]
  exact List.mem_append_left _ hg

/-- The known zero-state example lies in the precise retained-low branch. -/
theorem zero_counterexample_pending : RetainedLowPending
    FDCut.ZeroStateCounterexample.V FDCut.ZeroStateCounterexample.V'
    FDCut.ZeroStateCounterexample.a FDCut.ZeroStateCounterexample.B
    FDCut.ZeroStateCounterexample.s FDCut.ZeroStateCounterexample.y
    z FDCut.ZeroStateCounterexample.D := by
  unfold RetainedLowPending
  rw [FDCut.ZeroStateCounterexample.images.1,
    FDCut.ZeroStateCounterexample.images.2.1,
    FDCut.ZeroStateCounterexample.images.2.2.1,
    FDCut.ZeroStateCounterexample.images.2.2.2,
    FDCut.ZeroStateCounterexample.B, sh_z]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, ?_⟩
  rintro ⟨_, Y, hY⟩
  have h := congrArg lev hY
  exact (show lev FDCut.ZeroStateCounterexample.y ≠ FDCut.ZeroStateCounterexample.sf by decide) h

/-- Old VAnc alone does not repair the bare retained-low term implication.
The existing example lacks KA at the exceptional off-path low level. -/
theorem zero_counterexample_not_need : ¬ RetainedLowNeed
    FDCut.ZeroStateCounterexample.V FDCut.ZeroStateCounterexample.V'
    FDCut.ZeroStateCounterexample.a FDCut.ZeroStateCounterexample.B
    FDCut.ZeroStateCounterexample.s FDCut.ZeroStateCounterexample.y
    z FDCut.ZeroStateCounterexample.D := by
  unfold RetainedLowNeed
  rw [FDCut.ZeroStateCounterexample.images.1,
    FDCut.ZeroStateCounterexample.images.2.1,
    FDCut.ZeroStateCounterexample.images.2.2.1,
    FDCut.ZeroStateCounterexample.images.2.2.2,
    FDCut.ZeroStateCounterexample.B, sh_z]
  intro h
  have hd := h FDCut.ZeroStateCounterexample.y
    (by decide) (by decide) (le_refl _)
  exact (show ¬ ∃ d ∈ FDCut.ZeroStateCounterexample.y ::
      (comps z FDCut.ZeroStateCounterexample.y ++
        comps z FDCut.ZeroStateCounterexample.af), FDCut.ZeroStateCounterexample.D ≤ d by decide) hd

/-- A counted child of the one-column prefix is counted in the original
matrix too (the standard structural drop fact, exposed for CL membership). -/
theorem mem_cl_of_mem_cl_take {M : Mat} (S : SInv M) {x i c : Nat}
    (hx : x + 1 = M.length) (hi : i < x) (hc : c ∈ CL (M.take x) i) :
    c ∈ CL M i := by
  have hch := cl_mem_children hc
  have hcnt : Counted (M.take x) i c := by
    unfold CL at hc
    exact of_decide_eq_true (List.mem_filter.mp hc).2
  have hcnt' := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
    i c (by omega) (by simpa [show M.length - 1 = x by omega] using hch)
    (by simpa [show M.length - 1 = x by omega] using hcnt)
  have hch' : c ∈ children M i := by
    rw [children_take, List.mem_filter] at hch
    exact hch.1
  unfold CL
  exact List.mem_filter.mpr ⟨hch', decide_eq_true hcnt'⟩

/-- n=2 unshifted source v equality at an active NONSEED frame, via original
M. Uses only the existing below-x residual and source context, not target FC. -/
theorem source_v_base_nonseed {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hB : T2BelowXResAt M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L i c : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    {σ ρP : Valn} (hCN : Cons (G2 M r L 2) σ) (hGN : Good3 (G2 M r L 2) σ)
    (hCP : Cons (G2 M r L 1) ρP) (hi : i < r + L)
    (hc : c ∈ CL (G2 M r L 1) i) (hsc : ¬ T2SeedCol M r L i) :
    σ.v i = ρP.v i := by
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hl2 : 2 ≤ M.length := by omega
  have hx : r + L + 1 = M.length := hlen
  have hP : G2 M r L 1 = M.take (r + L) := gexp_one_gen hlen
  rw [hP] at hCP hc
  have hcnt := counted_take_last (M := M) (by omega) C.S.r0p C.S.z2 C.S.sibDec C.S.z1c C.S.uat
  have hRT : Rk (M.take (r + L)) rk := by
    have h := rk_take (by omega) C.I.rank hcnt
    simpa [show M.length - 1 = r + L by omega] using h
  have hvi : ρP.v i = ρ.v i := v_take_of_counted_child C.S C.I.cons C.I.good hx hi hCP hRT hc
  have hGlow : ∀ m, 1 ≤ m → m < 2 → ∀ τ, Cons (G2 M r L m) τ → Good3 (G2 M r L m) τ := by
    intro m hm hm2 τ hτ
    obtain rfl : m = 1 := by omega
    rw [hP] at hτ ⊢
    have h := (take_fields_ctx C.toStepCtxV2 hl2
      (show Cons (M.take (M.length - 1)) τ by simpa [show M.length - 1 = r + L by omega] using hτ)).1
    simpa [show M.length - 1 = r + L by omega] using h
  have hBS := t2BelowXS_of hB C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2 hlen hr
  have hsh := (hBS 2 (by omega) hGlow σ hCN
    (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩) i hi).2.2.2.1 hsc
  have hci : c ∈ CL M i := mem_cl_of_mem_cl_take C.S hx hi hc
  rcases hsh with ⟨hv, _, _⟩ | ⟨hv, _⟩ | ⟨_, hnil⟩
  · exact hv.trans hvi.symm
  · exact hv.trans hvi.symm
  · rw [hnil] at hci
    simp at hci

#print axioms old_vAnc_of_t2VAncStep
#print axioms old_vAnc_copy
#print axioms old_vAnc_component
#print axioms old_vAnc_copy_ctx
#print axioms frameDom_sh_zero_of_shared_level
#print axioms old_vAnc_component_of_KAG
#print axioms state_component_of_kind
#print axioms le1_take_forward
#print axioms vAnc_of_prefix_pair
#print axioms old_vAnc_base_of_pair_values
#print axioms v_take_of_counted_child
#print axioms v_take_of_par1_child
#print axioms zero_counterexample_old_ancestor
#print axioms zero_counterexample_pending
#print axioms zero_counterexample_not_need
#print axioms source_v_base_nonseed
end Ytosk.FDCopy
