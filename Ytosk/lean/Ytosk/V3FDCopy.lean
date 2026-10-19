/-
Real-copy FrameDom: partial reductions after replacing the false pure FDsh.
No additional residual or term guard is introduced. Old VAnc is proved for all
n>=2 active guarded copy frames from the existing context and hVS. The n=2
case compares both valuations through original M, without intermediate-prefix
invariants. The combined term statement FDshCopyKV is recorded for review and
remains unproved; the earlier path-only retained branch is refuted.
-/
import Ytosk.V3T2VSFC
import Ytosk.V3FDCut
import Ytosk.V3T2CutDom

namespace Ytosk.FDCopy
open T

/-- All-low version of T2VRAK in exactly the existing T2CopyK frame shape.
It removes only the LevAt premise; the level bound u <= V remains. -/
def T2VRAKAll (K : T → T → T → List T → T → T → Prop) (M : Mat) : Prop :=
  T2CopyK (fun V V' a Lv cv => ∀ u, u ≤ V → K V V' a Lv cv u) M

/-- The all-low residual supplies every current path-level K consumer. -/
theorem t2VRAK_of_all {K : T → T → T → List T → T → T → Prop} {M : Mat}
    (h : T2VRAKAll K M) : T2VRAK K M := by
  intro r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL u _hu huV
  exact h r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL u huV

/-- Shared full VDomF combines with all-low KAG at the very same copy frames. -/
theorem t2VRAKAll_KVRA_of {M : Mat} (hVD : T2CopyK CopyVDomK M)
    (hAG : T2VRAKAll KAG M) : T2VRAKAll KVRA M := by
  intro r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL u huV
  exact ⟨hVD r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL,
    hAG r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL u huV⟩

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

/-- In a standard t2 source, r is always the seed: if q differs from r,
par0_q_t2 identifies q's parent with r. -/
theorem root_is_seed {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) {r L : Nat}
    (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) :
    T2Seed M r L r := by
  have hA := anc0_of_par M 2 r (r + L) hr
  obtain ⟨q, hq⟩ := par0_of_anc hA (by have := par_lt M 2 _ _ hr; omega)
  by_cases hqr : q = r
  · exact Or.inl ⟨hqr ▸ hq, rfl⟩
  · exact Or.inr ⟨q, hq, hqr,
      par0_q_t2 C.std C.ne (Inv3W.ofV2 C.S C.I) hlen hr hq hqr⟩

/-- An active source column other than r cannot be either exceptional seed
column. The q column has no counted children even in original M. -/
theorem active_ne_root_not_seedcol {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) {r L i c : Nat}
    (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hi : i < r + L) (hc : c ∈ CL (M.take (r + L)) i) (hir : i ≠ r) :
    ¬ T2SeedCol M r L i := by
  have hci := mem_cl_of_mem_cl_take C.S hlen hi hc
  intro hsc
  rcases hsc with hs | ⟨q, hq, hqr, hqi⟩
  · rcases hs with ⟨_, hri⟩ | ⟨q, hq, hqr, hpi⟩
    · exact hir hri
    · have hpq := par0_q_t2 C.std C.ne (Inv3W.ofV2 C.S C.I) hlen hr hq hqr
      rw [hpq] at hpi
      exact hir (Option.some.inj hpi).symm
  · subst i
    have hpq := par0_q_t2 C.std C.ne (Inv3W.ofV2 C.S C.I) hlen hr hq hqr
    have hrq : r < q := par_lt M 0 _ _ hpq
    obtain ⟨qp, rfl⟩ : ∃ qp, q = r + qp := ⟨q - r, by omega⟩
    obtain ⟨hX, hJ⟩ := sInvXJ_std C.std C.ne
    obtain ⟨_, _, _, hnil, _⟩ := t2_qn_struct hX hJ hlen hr hq (by omega) hpq
    rw [hnil] at hci
    simp at hci

/-- The old below-x residual already includes unchanged v of the seed r.
This only projects that existing fact, not the target's FrameClosed. -/
theorem root_v_base_original {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hB : T2BelowXResAt M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    {σ : Valn} (hCN : Cons (G2 M r L 2) σ) (hGN : Good3 (G2 M r L 2) σ) :
    σ.v r = ρ.v r := by
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hl2 : 2 ≤ M.length := by omega
  have hP : G2 M r L 1 = M.take (r + L) := gexp_one_gen hlen
  have hGlow : ∀ m, 1 ≤ m → m < 2 → ∀ τ, Cons (G2 M r L m) τ → Good3 (G2 M r L m) τ := by
    intro m hm hm2 τ hτ
    obtain rfl : m = 1 := by omega
    rw [hP] at hτ ⊢
    have h := (take_fields_ctx C.toStepCtxV2 hl2
      (show Cons (M.take (M.length - 1)) τ by simpa [show M.length - 1 = r + L by omega] using hτ)).1
    simpa [show M.length - 1 = r + L by omega] using h
  have hRaw := hB C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2 r L hlen hr
    2 (by omega) hGlow σ hCN (fun b j _ hj => by
      cases b
      · exact hGN.ot_v j hj
      · exact hGN.ot_o j hj)
  exact (hRaw.1 r (root_is_seed C hlen hr)).2

/-- n=2: every active unshifted source column keeps v, including the seed.
All assumptions here are already available in the real FC copy context. -/
theorem source_v_base_live {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hB : T2BelowXResAt M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L i c : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    {σ ρP : Valn} (hCN : Cons (G2 M r L 2) σ) (hGN : Good3 (G2 M r L 2) σ)
    (hCP : Cons (G2 M r L 1) ρP) (hi : i < r + L)
    (hc : c ∈ CL (G2 M r L 1) i) : σ.v i = ρP.v i := by
  have hP : G2 M r L 1 = M.take (r + L) := gexp_one_gen hlen
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hRT := (C.pre (r + L) (by omega) (by omega)).1.rank
  by_cases hir : i = r
  · subst i
    have hcT : c ∈ CL (M.take (r + L)) r := hP ▸ hc
    have hCT : Cons (M.take (r + L)) ρP := hP ▸ hCP
    exact (root_v_base_original C hB hz h2 hlen hr hCN hGN).trans
      (v_take_of_counted_child C.S C.I.cons C.I.good hlen hi hCT hRT hcT).symm
  · exact source_v_base_nonseed C hB hz h2 hlen hr hCN hGN hCP hi hc
      (active_ne_root_not_seedcol C hlen hr hi (hP ▸ hc) hir)

/-- A nontrivial row-1 descendant supplies a row-1 child of the ancestor. -/
theorem le1_has_first_child {G : Mat} {r i : Nat} (hri : r < i)
    (hg : TRIO.le1 G r i) : ∃ j, j < G.length ∧ par G 1 j = some r := by
  have key : ∀ m i, i < m → r < i → TRIO.le1 G r i →
      ∃ j, j < G.length ∧ par G 1 j = some r := by
    intro m
    induction m with
    | zero => intro i hi; omega
    | succ m ih =>
      intro i hi hri hg
      obtain ⟨p, hp, hgp⟩ := le1_par1_down hg (by omega)
      by_cases hpr : p = r
      · exact ⟨i, hg.2.1, hpr ▸ hp⟩
      · have hpi := par_lt G 1 i p hp
        have hrp := le1_ge hgp
        exact ih p (by omega) (by omega) hgp
  exact key (i + 1) i (Nat.lt_succ_self _) hri hg

/-- BOTH unshifted source values at every active guarded n=2 frame agree.
The ancestor has either the active counted child itself, or a surviving row-1
child; this supplies the one-drop bridge to original M. -/
theorem source_v_base_pair {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hB : T2BelowXResAt M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L i c : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    {σ ρP : Valn} (hCN : Cons (G2 M r L 2) σ) (hGN : Good3 (G2 M r L 2) σ)
    (hCP : Cons (G2 M r L 1) ρP) (hg : TRIO.le1 (G2 M r L 1) r i)
    (hc : c ∈ CL (G2 M r L 1) i) : σ.v r = ρP.v r ∧ σ.v i = ρP.v i := by
  have hP : G2 M r L 1 = M.take (r + L) := gexp_one_gen hlen
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hi : i < r + L := by
    have h := hg.2.1
    rw [hP, List.length_take] at h
    omega
  have hvi := source_v_base_live C hB hz h2 hlen hr hCN hGN hCP hi hc
  refine ⟨?_, hvi⟩
  by_cases hir : i = r
  · simpa [hir] using hvi
  · have hCT : Cons (M.take (r + L)) ρP := hP ▸ hCP
    have hRT := (C.pre (r + L) (by omega) (by omega)).1.rank
    have hgT : TRIO.le1 (M.take (r + L)) r i := hP ▸ hg
    have hri : r < i := by have := le1_ge hg; omega
    obtain ⟨j, hj, hpj⟩ := le1_has_first_child hri hgT
    have hjx : j < r + L := by rw [List.length_take] at hj; omega
    have hvT := v_take_of_par1_child C.S C.I.cons C.I.good hlen hrx hjx hCT hRT
      (show par M 1 j = some r by rw [← par_take M 1 j hjx]; exact hpj)
    exact (root_v_base_original C hB hz h2 hlen hr hCN hGN).trans hvT.symm

/-- n=2 old VAnc at every active guarded source frame, with no source-value
agreement hypothesis and no invariant on intermediate prefixes of the target. -/
theorem old_vAnc_base_live {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hB : T2BelowXResAt M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hVS : T2VAncStep M)
    {r L i c : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    {σ ρP : Valn} (hCN : Cons (G2 M r L 2) σ) (hGN : Good3 (G2 M r L 2) σ)
    (hCP : Cons (G2 M r L 1) ρP) (hg : TRIO.le1 (G2 M r L 1) r i)
    (hc : c ∈ CL (G2 M r L 1) i) : VAnc ρP r i := by
  obtain ⟨hvr, hvi⟩ := source_v_base_pair C hB hz h2 hlen hr hCN hGN hCP hg hc
  exact old_vAnc_base_of_pair_values C hz h2 hVS hlen hr hCN hGN hg hvr hvi

/-- Old VAnc for every active guarded source frame at every n>=2, derived
from the existing hVS and below-x residual. No new top assumption is added. -/
theorem old_vAnc_copy_live {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hB : T2BelowXResAt M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hVS : T2VAncStep M)
    {r L n i c : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hn : 2 ≤ n) {σ ρP : Valn} (hCN : Cons (G2 M r L n) σ)
    (hGN : Good3 (G2 M r L n) σ) (hCP : Cons (G2 M r L (n - 1)) ρP)
    (hGP : Good3 (G2 M r L (n - 1)) ρP)
    (hg : TRIO.le1 (G2 M r L (n - 1)) r i)
    (hc : c ∈ CL (G2 M r L (n - 1)) i) : VAnc ρP r i := by
  by_cases hn2 : n = 2
  · subst n
    exact old_vAnc_base_live C hB hz h2 hVS hlen hr hCN hGN hCP hg hc
  · exact old_vAnc_copy_ctx C hz h2 hVS hlen hr (by omega) hCP hGP hg

/-- All old-V components are discharged by old ancestry and the KA conjunct.
The trigger itself supplies a <= s; no extra parent/child order guard is needed. -/
theorem old_root_component_closed {V V' a s y u g C : T} {Lv : List T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a) (hs : isOT s = true) (hVs : V < s)
    (ht : psi a z z < psi s y z)
    (hOld : ∀ u g, g ∈ comps u V →
      g ≤ psi a z z ∨ ∃ d ∈ comps u a, g ≤ d)
    (hK : KAG V V' a Lv (psi s y z) u)
    (hg : ∃ e ∈ comps u V, g ≤ e)
    (hSC : psi (shf V V' s) z z < C) :
    ∃ d ∈ C :: (comps u C ++ comps u (shf V V' a)), g ≤ d := by
  have has : a ≤ s := by
    simpa only [lev] using lev_le_of_le (le_of_lt ht)
  have hsf : s ≤ shf V V' s := le_shf_self hV hV' (le_of_lt hVV) hs (le_of_lt hVs)
  have haf := ClShLGuarded.shf_le_right hV hV' hVV ha hVa has
  have om_mono : ∀ {p q : T}, p ≤ q → psi p z z ≤ psi q z z := by
    intro p q hpq
    rcases (le_iff _ _).mp hpq with h | rfl
    · exact psi_le_psi_of (Or.inl h)
    · exact le_refl _
  have hfinish : g ≤ psi (shf V V' s) z z →
      ∃ d ∈ C :: (comps u C ++ comps u (shf V V' a)), g ≤ d :=
    fun h => ⟨C, List.mem_cons_self .., le_trans h (le_of_lt hSC)⟩
  obtain ⟨e, he, hge⟩ := hg
  rcases hOld u e he with h | ⟨d, hd, hed⟩
  · exact hfinish (le_trans hge (le_trans h (om_mono (le_trans has hsf))))
  · rcases hK.1 d hd with h | ⟨d', hd', hdd'⟩
    · exact hfinish (le_trans hge (le_trans hed (le_trans h (om_mono haf))))
    · exact ⟨d', List.mem_cons_of_mem _ (List.mem_append_right _ hd'),
        le_trans hge (le_trans hed hdd')⟩

/-- The already proved high-component transport with the actual H endpoint.
This supplies the high branch directly in the FDshCopyKV conclusion. -/
theorem frameDom_copy_high_component {V V' a B s y w u g C : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hB : isOT B = true)
    (hc : isOT (psi s y z) = true) (hVs : V < s)
    (hw : isOT w = true) (hVw : V < w) (hwa : w ≤ a)
    (hu : u ≤ shf V V' w) (hFD : FrameDom a B s (H s y))
    (hg : g ∈ comps w B ∨ g ∈ comps w s)
    (hBC : sh V V' B < C) (hSC : psi (shf V V' s) z z < C)
    (hCX : C ≤ H (shf V V' s) (sh V V' y)) :
    ∃ d ∈ C :: (comps u C ++ comps u (shf V V' a)), sh V V' g ≤ d := by
  apply FDCut.frameDom_sh_high_component hV hV' hVV ha hB (isOT_sub hc)
    (isOT_arg (ClShLGuarded.isOT_H_self hc)) hVs hw hVw hwa hu hFD hg hBC hSC
  rwa [sh_H hV hV' hVV hc hVs]

/-- At an unchanged level every old component has a dominating new component,
unless it belongs to the removed V prefix. This holds at all levels. -/
theorem component_forward_or_old_root {V V' u : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V') :
    ∀ n (t : T), size t ≤ n → isOT t = true → ∀ g ∈ comps u t,
      (∃ e ∈ comps u V, g ≤ e) ∨ ∃ d ∈ comps u (sh V V' t), g ≤ d := by
  intro n
  induction n with
  | zero =>
    intro t hn ht g hg
    cases t with
    | z => simp [comps] at hg
    | psi => simp [size] at hn
  | succ n ih =>
    intro t hn ht g hg
    cases t with
    | z => simp [comps] at hg
    | psi p x r =>
      have hp := isOT_sub ht
      have hx := isOT_arg ht
      have hr := isOT_rest ht
      have hsz : size p ≤ n ∧ size x ≤ n ∧ size r ≤ n := by simp [size] at hn; omega
      have htail : g ∈ comps u r →
          (∃ e ∈ comps u V, g ≤ e) ∨
            ∃ d ∈ comps u (sh V V' (psi p x r)), g ≤ d := by
        intro hg
        rcases ih r hsz.2.2 hr g hg with h | ⟨d, hd, hgd⟩
        · exact Or.inl h
        · right
          by_cases hVp : V < p
          · rw [sh_psi_gt hVp]
            exact ⟨d, mem_comps_tail hd, hgd⟩
          · rw [sh_psi_le hVp]
            exact ⟨d, mem_comps_tail hd, hgd⟩
      simp only [comps, List.mem_append] at hg
      rcases hg with hg | hg
      · by_cases hpu : lt p u = true
        · simp [hpu] at hg
        · rw [if_neg hpu] at hg
          by_cases hVp : V < p
          · have hfu : ¬ shf V V' p < u := not_lt.mpr (le_trans (not_lt.mp hpu)
              (le_shf_self hV hV' (le_of_lt hVV) hp (le_of_lt hVp)))
            have hlift : ∀ d ∈ comps u (shf V V' p),
                d ∈ comps u (sh V V' (psi p x r)) := by
              intro d hd
              rw [sh_psi_gt hVp]
              exact comps_psi_mem_of hfu (Or.inr (Or.inr (Or.inl hd)))
            simp only [List.mem_cons, List.mem_append] at hg
            rcases hg with hgeq | hg | hg
            · subst g
              right
              rw [sh_psi_gt hVp]
              exact ⟨sh V V' x, comps_psi_mem_of hfu (Or.inl rfl),
                le_sh hV hV' (le_of_lt hVV) hx⟩
            · rcases ih x hsz.2.1 hx g hg with h | ⟨d, hd, hgd⟩
              · exact Or.inl h
              · right
                rw [sh_psi_gt hVp]
                exact ⟨d, comps_psi_mem_of hfu (Or.inr (Or.inl hd)), hgd⟩
            · have hg' : g ∈ comps u (add V (sub p V)) := by
                rwa [add_sub_cancel' hV hp (le_of_lt hVp)]
              rcases comps_add u V (sub p V) g hg' with hgV | hgS
              · exact Or.inl ⟨g, hgV, le_refl _⟩
              · rcases ih (sub p V) (le_trans (size_sub_le p V) hsz.1)
                    (isOT_sub_sfx hp V) g hgS with h | ⟨d, hd, hgd⟩
                · exact Or.inl h
                · right
                  refine ⟨d, hlift d ?_, hgd⟩
                  unfold shf
                  obtain ⟨P, hP, _⟩ := add_eq_app_prefix V' (sh V V' (sub p V))
                  rw [hP, comps_app]
                  exact List.mem_append_right _ hd
          · right
            rw [sh_psi_le hVp]
            exact ⟨g, by simp only [comps, List.mem_append]; exact Or.inl (by rw [if_neg hpu]; exact hg), le_refl _⟩
      · exact htail hg

/-- The forward-component certificate for f(t), including high indices. -/
theorem index_component_forward_or_old_root {V V' t u g : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ht : isOT t = true) (hVt : V ≤ t) (hg : g ∈ comps u t) :
    (∃ e ∈ comps u V, g ≤ e) ∨ ∃ d ∈ comps u (shf V V' t), g ≤ d := by
  have hg' : g ∈ comps u (add V (sub t V)) := by
    rwa [add_sub_cancel' hV ht hVt]
  rcases comps_add u V (sub t V) g hg' with hgV | hgS
  · exact Or.inl ⟨g, hgV, le_refl _⟩
  · rcases component_forward_or_old_root hV hV' hVV (size (sub t V)) (sub t V)
        (le_refl _) (isOT_sub_sfx ht V) g hgS with h | ⟨d, hd, hgd⟩
    · exact Or.inl h
    · right
      refine ⟨d, ?_, hgd⟩
      unfold shf
      obtain ⟨P, hP, _⟩ := add_eq_app_prefix V' (sh V V' (sub t V))
      rw [hP, comps_app]
      exact List.mem_append_right _ hd

/-- The entire unchanged persistence claim is settled when B has frozen head.
This includes the zero base case; no restriction on the level or g is needed. -/
theorem persistent_sh_frozen_source {V V' B A u g : T}
    (hB : isOT B = true) (hA : isOT A = true) (hlB : ¬ V < lev B)
    (hP : ClShLGuarded.Persistent u g B A) :
    (∃ d ∈ comps u V, g ≤ d) ∨
      ClShLGuarded.Persistent u g (sh V V' B) (sh V V' A) := by
  by_cases hlA : V < lev A
  · rcases ClShLGuarded.persistent_frozen_to_high_bound hlB hlA hP with rfl | h
    · exact Or.inr (fun c _ _ => ⟨z, List.mem_cons_self, le_refl _⟩)
    · exact Or.inl h
  · exact Or.inr (by rwa [sh_fix hB hlB, sh_fix hA hlA])

/-- A component of a frozen index survives in f(p), except for components
of the removed old V prefix. This is a forward statement at unchanged levels. -/
theorem frozen_index_component_forward {V V' p u g : T}
    (hV : isOT V = true) (hp : isOT p = true) (hVp : V ≤ p)
    (hlev : ¬ V < lev p) (hg : g ∈ comps u p) :
    g ∈ comps u V ∨ g ∈ comps u (shf V V' p) := by
  have hfix : sh V V' (sub p V) = sub p V := by
    apply sh_fix (isOT_sub_sfx hp V)
    have hh := lev_le_of_le (head_sub_le hp V)
    have hhead : ∀ t : T, lev (head t) = lev t := by intro t; cases t <;> rfl
    rw [hhead, hhead] at hh
    exact not_lt.mpr (le_trans hh (not_lt.mp hlev))
  have hmem : g ∈ comps u (add V (sub p V)) := by
    rwa [add_sub_cancel' hV hp hVp]
  rcases comps_add u V (sub p V) g hmem with hgV | hgS
  · exact Or.inl hgV
  · right
    unfold shf
    rw [hfix]
    obtain ⟨P, hP, _⟩ := add_eq_app_prefix V' (sub p V)
    rw [hP, comps_app]
    exact List.mem_append_right _ hgS

/-- Frozen leading-index intervals transport unchanged low components.
The sole exception is old-V domination, closed by old_root_component_closed. -/
theorem frozen_index_interval_transport {V V' p q u g Y R : T}
    (hV : isOT V = true) (hp : isOT p = true) (hq : isOT q = true)
    (hVp : V ≤ p) (hVq : V ≤ q)
    (hlp : ¬ V < lev p) (hlq : ¬ V < lev q)
    (hu : u ≤ shf V V' p) (hg : g ∈ comps u p)
    (hP : ClShLGuarded.Persistent u g p q) :
    (∃ d ∈ comps u V, g ≤ d) ∨
      ClShLGuarded.Persistent u g (psi (shf V V' p) z z) (psi (shf V V' q) Y R) := by
  rcases ClShLGuarded.persistent_shf_frozen hV hp hq hVp hVq hlp hlq hP with hVg | hP'
  · exact Or.inl hVg
  rcases frozen_index_component_forward hV hp hVp hlp hg with hgV | hgp
  · exact Or.inl ⟨g, hgV, le_refl _⟩
  · exact Or.inr (ClShLGuarded.persistent_psi_index hu
      (List.mem_cons_of_mem _ hgp) hP')

/-- The frozen-to-high corner needs only the old-V bound; the frozen-to-frozen
corner is handled by frozen_index_interval_transport. -/
theorem frozen_index_interval_transport_any {V V' p q u g Y R : T}
    (hV : isOT V = true) (hp : isOT p = true) (hq : isOT q = true)
    (hVp : V ≤ p) (hVq : V ≤ q) (hlp : ¬ V < lev p)
    (hu : u ≤ shf V V' p) (hg : g ∈ comps u p)
    (hP : ClShLGuarded.Persistent u g p q) :
    (∃ d ∈ comps u V, g ≤ d) ∨
      ClShLGuarded.Persistent u g (psi (shf V V' p) z z)
        (psi (shf V V' q) Y R) := by
  by_cases hlq : V < lev q
  · rcases ClShLGuarded.persistent_frozen_to_high_bound hlp hlq hP with rfl | h
    · exact Or.inr (fun c _ _ => ⟨z, List.mem_cons_self, le_refl _⟩)
    · exact Or.inl h
  · exact frozen_index_interval_transport hV hp hq hVp hVq hlp hlq hu hg hP

/-- A rightward corner all of whose components are zero, at every level. -/
def quietCorner : T → T
  | z => one
  | psi p _ _ => psi (quietCorner p) z z

theorem lt_quietCorner : ∀ t : T, t < quietCorner t
  | z => T.z_lt_psi _ _ _
  | psi p _x _r => T.psi_lt_psi.mpr (Or.inl (lt_quietCorner p))

theorem quietCorner_components (u : T) : ∀ t d, d ∈ comps u (quietCorner t) → d = z
  | z, d, hd => by
    simp only [quietCorner, one, comps] at hd
    split at hd <;> simp_all
  | psi p _x _r, d, hd => by
    simp only [quietCorner, comps] at hd
    split at hd
    · simp at hd
    · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, false_or, or_false] at hd
      rcases hd with h | hd
      · exact h
      · exact quietCorner_components u p d hd

/-- Crossing to a larger argument forces all persistent bounds into the
fixed head. The tail is tested at a quiet corner, whose components are zero. -/
theorem persistent_head_bound_of_argument_lt {u g p x r y t : T}
    (hxy : x < y)
    (hP : ClShLGuarded.Persistent u g (psi p x r) (psi p y t)) :
    g = z ∨ ∃ d ∈ comps u (psi p x z), g ≤ d := by
  have hBC : psi p x r < psi p x (quietCorner r) :=
    T.psi_lt_psi.mpr (Or.inr (Or.inr ⟨rfl, rfl, lt_quietCorner r⟩))
  have hCA : psi p x (quietCorner r) ≤ psi p y t :=
    le_of_lt (T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨rfl, hxy⟩)))
  obtain ⟨d, hd, hgd⟩ := hP _ hBC hCA
  rcases List.mem_cons.mp hd with rfl | hd
  · exact Or.inl (le_antisymm hgd (z_le _))
  · have heq : psi p x (quietCorner r) = app (psi p x z) (quietCorner r) := rfl
    rw [heq, comps_app] at hd
    rcases List.mem_append.mp hd with hd | hd
    · exact Or.inr ⟨d, hd, hgd⟩
    · have hd0 := quietCorner_components u r d hd
      subst d
      exact Or.inl (le_antisymm hgd (z_le _))

/-- Persistence with the intermediate term itself also allowed as a witness.
This is the exact argument-interval certificate extracted below. -/
def PersistentArg (u g B A : T) : Prop :=
  ∀ c, B < c → c ≤ A → ∃ d ∈ c :: Gc u c, g ≤ d

/-- Argument intervals preserve all witnesses except those already dominated
by the enclosing index. The argument itself is a valid component witness. -/
theorem persistent_argument_of_psi_interval {u g p x r y t : T}
    (hP : ClShLGuarded.Persistent u g (psi p x r) (psi p y t))
    (hIndex : ∀ d ∈ comps u p, ¬ g ≤ d) : PersistentArg u g x y := by
  intro e hxe hey
  have hBC : psi p x r < psi p e z := T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨rfl, hxe⟩))
  have hCA : psi p e z ≤ psi p y t := by
    rcases (le_iff _ _).mp hey with hey | rfl
    · exact le_of_lt (T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨rfl, hey⟩)))
    · exact psi_le_psi_of (Or.inr ⟨rfl, Or.inr ⟨rfl, z_le _⟩⟩)
  obtain ⟨d, hd, hgd⟩ := hP _ hBC hCA
  rcases List.mem_cons.mp hd with rfl | hd
  · exact ⟨z, List.mem_cons_of_mem _ List.mem_cons_self, hgd⟩
  · by_cases hpu : lt p u = true
    · simp [comps, hpu] at hd
    · rw [comps_psi_z_of_ge hpu] at hd
      simp only [List.mem_cons, List.mem_append] at hd
      rcases hd with rfl | hd | hd
      · exact ⟨d, List.mem_cons_self, hgd⟩
      · exact ⟨d, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd), hgd⟩
      · exact False.elim (hIndex d hd hgd)

/-- Tail intervals need no direct-term witness once the fixed head's
components have been excluded. -/
theorem persistent_tail_of_psi_interval {u g p x r t : T}
    (hP : ClShLGuarded.Persistent u g (psi p x r) (psi p x t))
    (hHead : ∀ d ∈ comps u (psi p x z), ¬ g ≤ d) :
    ClShLGuarded.Persistent u g r t := by
  intro e hre het
  have hBC : psi p x r < psi p x e := T.psi_lt_psi.mpr (Or.inr (Or.inr ⟨rfl, rfl, hre⟩))
  have hCA : psi p x e ≤ psi p x t :=
    psi_le_psi_of (Or.inr ⟨rfl, Or.inr ⟨rfl, het⟩⟩)
  obtain ⟨d, hd, hgd⟩ := hP _ hBC hCA
  rcases List.mem_cons.mp hd with rfl | hd
  · exact ⟨z, List.mem_cons_self, hgd⟩
  · have heq : psi p x e = app (psi p x z) e := rfl
    rw [heq, comps_app] at hd
    rcases List.mem_append.mp hd with hd | hd
    · exact False.elim (hHead d hd hgd)
    · exact ⟨d, List.mem_cons_of_mem _ hd, hgd⟩

/-- Persistence across a change of leading index restricts to the index
interval. Its witnesses are tested at the principal terms Omega_v. -/
theorem persistent_index_of_psi_interval {u g p x r q y t : T}
    (hP : ClShLGuarded.Persistent u g (psi p x r) (psi q y t)) :
    ClShLGuarded.Persistent u g p q := by
  intro v hpv hvq
  have hBC : psi p x r < psi v z z := T.psi_lt_psi.mpr (Or.inl hpv)
  have hCA : psi v z z ≤ psi q y t := by
    rcases (le_iff _ _).mp hvq with hvq | rfl
    · exact le_of_lt (T.psi_lt_psi.mpr (Or.inl hvq))
    · exact psi_le_psi_anyG (le_refl _)
  obtain ⟨d, hd, hgd⟩ := hP _ hBC hCA
  rcases List.mem_cons.mp hd with rfl | hd
  · exact ⟨z, List.mem_cons_self, hgd⟩
  · by_cases hvu : lt v u = true
    · simp [comps, hvu] at hd
    · rw [comps_psi_z_of_ge hvu] at hd
      simp only [comps, List.mem_cons, List.mem_append, List.not_mem_nil, false_or] at hd
      rcases hd with rfl | hd
      · exact ⟨z, List.mem_cons_self, hgd⟩
      · exact ⟨d, List.mem_cons_of_mem _ hd, hgd⟩

/-- A nonempty index interval already bounds g by its left index components. -/
theorem persistent_index_left_bound {u g p q : T} (hpq : p < q)
    (hP : ClShLGuarded.Persistent u g p q) :
    g = z ∨ ∃ d ∈ comps u p, g ≤ d := by
  obtain ⟨d, hd, hgd⟩ := hP (succ p) (lt_succ_self p) (succ_le_of_lt hpq)
  rcases List.mem_cons.mp hd with rfl | hd
  · exact Or.inl (le_antisymm hgd (z_le _))
  · rcases comps_succ_sub u d hd with rfl | hd
    · exact Or.inl (le_antisymm hgd (z_le _))
    · exact Or.inr ⟨d, hd, hgd⟩

/-- Lift an index interval when the left boundary only dominates g. -/
theorem persistent_psi_index_of_left_bound {u g p q x r y t : T}
    (hup : u ≤ p) (hg : ∃ d ∈ Gc u p, g ≤ d)
    (hP : ClShLGuarded.Persistent u g p q) :
    ClShLGuarded.Persistent u g (psi p x r) (psi q y t) := by
  intro C hBC hCA
  cases C with
  | z => exact False.elim (T.not_lt_z _ hBC)
  | psi v e f =>
    have hpv : p ≤ v := by simpa only [lev] using lev_le_of_le (le_of_lt hBC)
    have hvq : v ≤ q := by simpa only [lev] using lev_le_of_le hCA
    have huv : ¬ v < u := not_lt.mpr (le_trans hup hpv)
    have lift : ∀ d ∈ Gc u v, d ∈ Gc u (psi v e f) := by
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (comps_psi_mem_of huv (Or.inr (Or.inr (Or.inl hd))))
    rcases (le_iff _ _).mp hpv with hpv | rfl
    · obtain ⟨d, hd, hgd⟩ := hP v hpv hvq
      exact ⟨d, lift d hd, hgd⟩
    · obtain ⟨d, hd, hgd⟩ := hg
      exact ⟨d, lift d hd, hgd⟩

/-- A common prefix is handled entirely by component-forward transport.
Only the strictly smaller tail interval is passed to the recursive hypothesis. -/
theorem persistent_sh_common_prefix {V V' u g P B A : T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hP : isOT P = true)
    (hOld : ClShLGuarded.Persistent u g (app P B) (app P A))
    (hTail : ClShLGuarded.Persistent u g B A →
      (∃ d ∈ comps u V, g ≤ d) ∨
        ClShLGuarded.Persistent u g (sh V V' B) (sh V V' A)) :
    (∃ d ∈ comps u V, g ≤ d) ∨
      ClShLGuarded.Persistent u g (sh V V' (app P B)) (sh V V' (app P A)) := by
  by_cases hHead : ∃ d ∈ comps u P, g ≤ d
  · obtain ⟨d, hd, hgd⟩ := hHead
    rcases component_forward_or_old_root hV hV' hVV (size P) P (le_refl _) hP d hd with
        ⟨e, he, hde⟩ | ⟨e, he, hde⟩
    · exact Or.inl ⟨e, he, le_trans hgd hde⟩
    · right
      rw [sh_app, sh_app]
      intro c hBc hcA
      obtain ⟨c0, rfl, _, _⟩ := between_app hBc hcA
      refine ⟨e, List.mem_cons_of_mem _ ?_, le_trans hgd hde⟩
      rw [comps_app]
      exact List.mem_append_left _ he
  · have hBA : ClShLGuarded.Persistent u g B A := by
      intro c hBc hcA
      obtain ⟨d, hd, hgd⟩ := hOld (app P c) (app_lt_app_left P hBc) (app_le_app_left P hcA)
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨z, List.mem_cons_self, hgd⟩
      · rw [comps_app] at hd
        rcases List.mem_append.mp hd with hd | hd
        · exact False.elim (hHead ⟨d, hd, hgd⟩)
        · exact ⟨d, List.mem_cons_of_mem _ hd, hgd⟩
    rcases hTail hBA with h | h
    · exact Or.inl h
    · right
      rw [sh_app, sh_app]
      exact ClShLGuarded.persistent_app _ h

/-- The complete frozen-index change branch: no component witness is needed
as an input; old persistence supplies it at Omega_(p+1). -/
theorem persistent_sh_frozen_index_change {V V' u g p x r q y t Y R : T}
    (hV : isOT V = true) (hp : isOT p = true) (hq : isOT q = true)
    (hVp : V ≤ p) (hpq : p < q) (hlp : ¬ V < lev p)
    (hu : u ≤ shf V V' p)
    (hP : ClShLGuarded.Persistent u g (psi p x r) (psi q y t)) :
    (∃ d ∈ comps u V, g ≤ d) ∨
      ClShLGuarded.Persistent u g (psi (shf V V' p) z z)
        (psi (shf V V' q) Y R) := by
  have hIdx := persistent_index_of_psi_interval hP
  by_cases hlq : V < lev q
  · rcases ClShLGuarded.persistent_frozen_to_high_bound hlp hlq hIdx with rfl | h
    · exact Or.inr (fun c _ _ => ⟨z, List.mem_cons_self, le_refl _⟩)
    · exact Or.inl h
  · have hVq := le_trans hVp (le_of_lt hpq)
    rcases ClShLGuarded.persistent_shf_frozen hV hp hq hVp hVq hlp hlq hIdx with h | hP'
    · exact Or.inl h
    · rcases persistent_index_left_bound hpq hIdx with rfl | ⟨d, hd, hgd⟩
      · exact Or.inr (fun c _ _ => ⟨z, List.mem_cons_self, le_refl _⟩)
      · rcases frozen_index_component_forward hV hp hVp hlp hd with hdV | hd'
        · exact Or.inl ⟨d, hdV, hgd⟩
        · exact Or.inr (persistent_psi_index_of_left_bound hu
            ⟨d, List.mem_cons_of_mem _ hd', hgd⟩ hP')

set_option linter.unusedVariables false in
/-- Candidate COMBINED term statement, recorded for review before proof.
It adds full old-V ancestor domination to FDshCopy with full VDomF and all-low
KAG. It is not asserted as a theorem here and is not a new top assumption.
The path-only KAG version is already refuted by zero_counterexample_not_need.
The matrix proof old_vAnc_copy_live supplies hOld at actual active copy frames. -/
def FDshCopyKV : Prop := ∀ {V V' a B s y : T} {Lv : List T}
    (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (ha : isOT a = true) (hVa : V ≤ a)
    (hs : ∀ t ∈ Lv ++ [psi s y z], Single t)
    (hp : (Lv ++ [psi s y z]).Pairwise (fun p q => q ≤ p))
    (hlev : V < a ∨ ∀ t ∈ Lv ++ [psi s y z], V < lev t)
    (hB : B = spArg a z (sumN Lv))
    (hFO : isOT (psi a B z) = true)
    (hKind : B ≠ z → PH3cKindG B (split y (psi (succ s) z z)).1
      (split y (psi (succ s) z z)).2 s)
    (hVs : V < s)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hVD : VDomF V V' a)
    (hK : ∀ u, u ≤ V → KAG V V' a Lv (psi s y z) u)
    (hOld : ∀ u g, g ∈ comps u V →
      g ≤ psi a z z ∨ ∃ d ∈ comps u a, g ≤ d)
    (hFD : FrameDom a B s (H s y)),
    FrameDom (shf V V' a) (sh V V' B) (shf V V' s)
      (H (shf V V' s) (sh V V' y))

#print axioms t2VRAK_of_all
#print axioms t2VRAKAll_KVRA_of
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
#print axioms source_v_base_live
#print axioms source_v_base_pair
#print axioms old_vAnc_base_live
#print axioms quietCorner_components
#print axioms persistent_head_bound_of_argument_lt
#print axioms persistent_sh_common_prefix
#print axioms persistent_argument_of_psi_interval
#print axioms persistent_tail_of_psi_interval
#print axioms persistent_sh_frozen_index_change
#print axioms persistent_index_of_psi_interval
#print axioms persistent_index_left_bound
#print axioms persistent_psi_index_of_left_bound
#print axioms persistent_sh_frozen_source
#print axioms index_component_forward_or_old_root
#print axioms component_forward_or_old_root
#print axioms frozen_index_interval_transport_any
#print axioms frozen_index_component_forward
#print axioms frozen_index_interval_transport
#print axioms old_root_component_closed
#print axioms frameDom_copy_high_component
#print axioms old_vAnc_copy_live
end Ytosk.FDCopy
