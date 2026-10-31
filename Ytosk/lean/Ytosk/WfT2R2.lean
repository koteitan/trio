/-
**WfT2R2: the `FrameOT` skeleton and the `FDCopy` consumers with `T2BelowXResAtX` (2026-11-01).**

Copies (suffix `XR`) of `clField_expand_t2`・`frameOT_expand_t2` (V3ExpT2FO; `clField_of_shape` replaced by
`WfT2X.clField_of_shapeX`, which needs `hQlowV`), the `source_v_base_*`・`root_v_base_original` lemmas
(V3FDCopy) and `root_v_original`・`t2CopyK_FDshAt_of_path`・`t2FDCopyRes_of_path` (V3FDCopyRoot).
-/
import Ytosk.WfT2R1
import Ytosk.V3FDCopyRoot
import Ytosk.V3ExpT2FO

namespace Ytosk.FDCopy
open T
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- n=2 unshifted source v equality at an active NONSEED frame, via original
M. Uses only the existing below-x residual and source context, not target FC. -/
theorem source_v_base_nonseedXR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hB : WfT2X.T2BelowXResAtX M ρ rk)
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
    have h := (take_fields_ctx C.toStepCtxB hl2
      (show Cons (M.take (M.length - 1)) τ by simpa [show M.length - 1 = r + L by omega] using hτ)).1
    simpa [show M.length - 1 = r + L by omega] using h
  have hBS := WfT2X.t2BelowXS_ofX hB C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 hlen hr
  have hsh := (hBS 2 (by omega) hGlow σ hCN
    (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩) i hi).2.2.2.1 hsc
  have hci : c ∈ CL M i := mem_cl_of_mem_cl_take C.S hx hi hc
  rcases hsh with (⟨hv, _, _⟩ | ⟨hv, _⟩ | ⟨_, hnil⟩) | ⟨hv, _⟩
  · exact hv.trans hvi.symm
  · exact hv.trans hvi.symm
  · rw [hnil] at hci
    simp at hci
  · exact hv.trans hvi.symm

end Ytosk.FDCopy

namespace Ytosk.FDCopy
open T
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The old below-x residual already includes unchanged v of the seed r.
This only projects that existing fact, not the target's FrameClosed. -/
theorem root_v_base_originalXR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hB : WfT2X.T2BelowXResAtX M ρ rk)
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
    have h := (take_fields_ctx C.toStepCtxB hl2
      (show Cons (M.take (M.length - 1)) τ by simpa [show M.length - 1 = r + L by omega] using hτ)).1
    simpa [show M.length - 1 = r + L by omega] using h
  have hRaw := hB C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 r L hlen hr
    2 (by omega) hGlow σ hCN (fun b j _ hj => by
      cases b
      · exact hGN.ot_v j hj
      · exact hGN.ot_o j hj)
  exact (hRaw.1 r (root_is_seed C hlen hr)).2

end Ytosk.FDCopy

namespace Ytosk.FDCopy
open T
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- n=2: every active unshifted source column keeps v, including the seed.
All assumptions here are already available in the real FC copy context. -/
theorem source_v_base_liveXR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hB : WfT2X.T2BelowXResAtX M ρ rk)
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
    exact (root_v_base_originalXR C hB hz h2 hlen hr hCN hGN).trans
      (v_take_of_counted_child C.S C.I.cons C.I.good hlen hi hCT hRT hcT).symm
  · exact source_v_base_nonseedXR C hB hz h2 hlen hr hCN hGN hCP hi hc
      (active_ne_root_not_seedcol C hlen hr hi (hP ▸ hc) hir)

end Ytosk.FDCopy

namespace Ytosk.FDCopy
open T
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- BOTH unshifted source values at every active guarded n=2 frame agree.
The ancestor has either the active counted child itself, or a surviving row-1
child; this supplies the one-drop bridge to original M. -/
theorem source_v_base_pairXR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hB : WfT2X.T2BelowXResAtX M ρ rk)
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
  have hvi := source_v_base_liveXR C hB hz h2 hlen hr hCN hGN hCP hi hc
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
    exact (root_v_base_originalXR C hB hz h2 hlen hr hCN hGN).trans hvT.symm

end Ytosk.FDCopy

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **A counted-frame property of every `M[n]`** (`t = 2`, `n ≥ 1`), from its `σ`-invariance, its stability
under lowering the last child by `◁`, the frames of `M` and `M.take x`, and the seed frames. -/
theorem clField_expand_t2XR {Q : T → List T → T → Prop}
    (hQσ : ∀ (V V' a : T) (Lv : List T) (cv : T), isOT V = true → isOT V' = true → V < V' →
      isOT a = true → V ≤ a → (∀ t ∈ Lv ++ [cv], Single t) →
      (Lv ++ [cv]).Pairwise (fun a b => b ≤ a) → (V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t) →
      Q a Lv cv → Q (shf V V' a) (Lv.map (sh V V')) (sh V V' cv))
    (hQlow : ∀ a Lv cv cv', Q a Lv cv → Lhd z cv' cv → isOT cv' = true → Q a Lv cv')
    (hQlowV : ∀ a Lv s s', Q a Lv (psi s z z) → Lhd a (psi s' z z) (psi s z z) → isOT (psi s' z z) = true →
      Q a Lv (psi s' z z))
    {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk) (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hQM : CLField Q M ρ)
    (hQT : ∀ τ, Cons (M.take (M.length - 1)) τ → CLField Q (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames Q M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → CLField Q (expand M n) σ := by
  have hGall := good3_expand_t2 hM hS I R hz h2 (WfT2X.t2BelowXE_ofX hB hM hS I R hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I R hz h2)
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  rw [h2] at hr
  have hrx : r < M.length - 1 := par_lt M 2 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  rw [hL] at hr hQT
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  have hd1 : 0 < d1 := by omega
  have hexp : ∀ n, expand M n = TRIO.gexp M r L d0 d1 n := by
    intro n
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hG : ∀ m, 1 ≤ m → ∀ σ, Cons (TRIO.gexp M r L d0 d1 m) σ → Good3 (TRIO.gexp M r L d0 d1 m) σ :=
    fun m hm σ hσ => by rw [← hexp m] at hσ ⊢; exact hGall m hm σ hσ
  have hRk : ∀ m, 1 ≤ m → ∃ rk, Rk (TRIO.gexp M r L d0 d1 m) rk := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hBE : ∀ m, 1 ≤ m → BumpE2 (TRIO.gexp M r L d0 d1 m) := fun m _ => by
    rw [← hexp m]; exact (sInvX_expand hX m).loc.2.2.1
  have hCR := t2CopyResAll_holds M ρ rk hM hS I R hz h2 r L hlen hr
  have hBS := WfT2X.t2BelowXS_ofX hB hM hS I R hz h2 hlen hr
  have hSD := hX.loc.1
  have key : ∀ n, 1 ≤ n → ∀ σ, Cons (TRIO.gexp M r L d0 d1 n) σ → CLField Q (TRIO.gexp M r L d0 d1 n) σ := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        intro σ hσ
        rw [gexp_one_gen hlen] at hσ ⊢
        exact hQT σ hσ
      · intro σ hCN
        have hn2 : 2 ≤ m + 1 := by omega
        obtain ⟨rkP, hRP⟩ := hRk m hm0
        have hCP : Cons (TRIO.gexp M r L d0 d1 m) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
        have hGP := hG m hm0 _ hCP
        have hQP := ih hm0 _ hCP
        have hm : m + 1 - 1 = m := by omega
        obtain ⟨hKV, hB', hV', hVV⟩ := hCR (m + 1) hn2 σ _ hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP)
        have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBE m hm0)
        have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r hX.r0p hSD
        have hF := copy_facts_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBE m hm0)
          hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP) (by rw [hm]; exact hRP) hK hKV hRK hB' hV' hVV
        rw [hm] at hF
        have hlN : (TRIO.gexp M r L d0 d1 (m + 1)).length = r + (m + 1) * L := TRIO.gexp_length hlen
        have hlP : (TRIO.gexp M r L d0 d1 m).length = r + m * L := TRIO.gexp_length hlen
        have hmL : (m + 1) * L = m * L + L := Nat.succ_mul m L
        have hrP : r < (TRIO.gexp M r L d0 d1 m).length := by
          have : L ≤ m * L := Nat.le_mul_of_pos_left L hm0
          omega
        have hcopy := clField_copy hQσ hF hCP hGP hrP hV' hVV hQP
        have hGN := hG (m + 1) (by omega) σ hCN
        intro i hi Lc c R hCL
        rcases Nat.lt_or_ge i (r + L) with hix | hix
        · by_cases hsc : T2SeedCol M r L i
          · exact hSeed r L hlen hr (m + 1) hn2 (fun k hk1 _ τ hτ => hG k hk1 τ hτ) σ hCN hGN i hsc Lc c R hCL
          · have hsh := (hBS (m + 1) hn2 (fun k hk1 _ τ hτ => hG k hk1 τ hτ) σ hCN (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩) i hix).2.2.2.1 hsc
            exact WfT2X.clField_of_shapeX hQlow hQlowV hsh
              (fun d hd => hGN.ot_o d (mem_children (cl_mem_children hd)).2) (fun Lc c R h => hQM i (by omega) Lc c R h) Lc c R hCL
        · obtain ⟨a, rfl⟩ : ∃ a, i = r + a + L := ⟨i - L - r, by omega⟩
          exact hcopy (r + a) (by omega) (by omega) Lc c R hCL
  intro n hn σ hσ
  rw [hexp n] at hσ ⊢
  exact key n hn σ hσ

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **`FrameOT` of every `M[n]`** (`t = 2`), from `FrameOT` of `M` and `M.take x` and the seed frames. -/
theorem frameOT_expand_t2XR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → FrameOT (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QFO M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → FrameOT (expand M n) σ :=
  clField_expand_t2XR qFO_sh (fun _ _ _ _ h _ _ => h) WfT2X.qFO_lowV hB hM hS I R hz h2 I.fo hT hSeed

end Ytosk

namespace Ytosk.FDCopyRoot
open T FDCopy
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- Every expansion keeps the original root value once its index is at least 2. -/
theorem root_v_originalXR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hB : WfT2X.T2BelowXResAtX M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L n : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r)
    (hn : 2 ≤ n)
    (hG : ∀ m, 1 ≤ m → ∀ τ, Cons (G2 M r L m) τ → Good3 (G2 M r L m) τ)
    {σ : Valn} (hCN : Cons (G2 M r L n) σ) : σ.v r = ρ.v r := by
  have hGN := hG n (by omega) σ hCN
  have hRaw := hB C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 r L hlen hr
    n hn (fun m hm _ τ hτ => hG m hm τ hτ) σ hCN (fun b j _ hj => by
      cases b
      · exact hGN.ot_v j hj
      · exact hGN.ot_o j hj)
  exact (hRaw.1 r (root_is_seed C hlen hr)).2

end Ytosk.FDCopyRoot

namespace Ytosk.FDCopyRoot
open T FDCopy
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

theorem t2CopyK_FDshAt_of_pathXR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtxT2 M ρ rk) (hB : WfT2X.T2BelowXResAtX M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hSeedFO : T2SeedFrames QFO M) (hU : T2VAncUse M)
    (hAG : T2VRAK KAG M) : T2CopyK FDshAt M := by
  have IW := Inv3W.ofV2 C.S C.I
  have RW : Res3W M ρ rk := C.toW
  have hCR := t2CopyResAll_holds M ρ rk C.std C.ne IW RW hz h2
  have hG := good3_expand_t2 C.std C.ne IW RW hz h2
    (WfT2X.t2BelowXE_ofX hB C.std C.ne IW RW hz h2) hCR
  have hVD := hU.vdom
  have hT : ∀ τ, Cons (M.take (M.length - 1)) τ → FrameOT (M.take (M.length - 1)) τ := by
    intro τ hτ
    have hl2 : 2 ≤ M.length := by
      obtain ⟨hX, _⟩ := sInvXJ_std C.std C.ne
      obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
      rw [h2] at hr
      have := par_lt M 2 _ r hr
      omega
    obtain ⟨I1, _⟩ := C.pre (M.length - 1) (by omega) (by omega)
    exact clField_congr (Q := QFO) I1.fo (agree_of_cons I1.cons hτ I1.rank)
  have hF := frameOT_expand_t2XR hB C.std C.ne IW RW hz h2 hT hSeedFO
  intro r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL
  change Cons (G2 M r L n) σ at hCN
  change Cons (G2 M r L (n - 1)) ρP at hCP
  have hc : c ∈ CL (G2 M r L (n - 1)) i := by rw [hCL]; simp
  have hGN : Good3 (G2 M r L n) σ := by
    rw [← expand_eq_G2_ctx C hz h2 hlen hr n] at hCN ⊢
    exact hG n (by omega) σ hCN
  have hFOP : FrameOT (G2 M r L (n - 1)) ρP := by
    rw [← expand_eq_G2_ctx C hz h2 hlen hr (n - 1)] at hCP ⊢
    exact hF (n - 1) (by omega) ρP hCP
  obtain ⟨_hKV, _hBase, hV', hVV⟩ := hCR r L hlen hr n hn σ ρP hCN hCP hGP
  have hrP : r < (G2 M r L (n - 1)).length := Nat.lt_of_le_of_lt hri hi
  have hV := hGP.ot_v r hrP
  have ha := hGP.ot_v i hi
  have hVa := v_le_of_le1 (vMono1_of hCP hGP) (i + 1) r i (Nat.lt_succ_self i) hg
  have hDom := hVD r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL
  have hGK : ∀ m, 1 ≤ m → ∀ τ, Cons (G2 M r L m) τ → Good3 (G2 M r L m) τ := by
    intro m hm τ hτ
    rw [← expand_eq_G2_ctx C hz h2 hlen hr m] at hτ ⊢
    exact hG m hm τ hτ
  have hvr : σ.v r = ρP.v r := by
    by_cases hn2 : n = 2
    · subst n
      exact (source_v_base_pairXR C hB hz h2 hlen hr hCN hGN hCP hg hc).1
    · exact (root_v_originalXR C hB hz h2 hlen hr hn hGK hCN).trans
        (root_v_originalXR C hB hz h2 hlen hr (by omega) hGK hCP).symm
  have hEdge := hU.edge r L hlen hr n hn σ hCN hGN
  unfold VAnc at hEdge
  rw [hvr] at hEdge
  have hRoot := rootDom_of_seed hV hV' hVV ha hVa hEdge hDom
  intro s y hcv hVs htr1 htr2 hFD
  have hcOT : isOT (psi s y z) = true := by
    rw [← hcv]
    exact hGP.ot_o c (mem_children (cl_mem_children hc)).2
  have hKG : ρP.v i = ρP.v r → ∀ fuel d,
      d ∈ compsAN (ρP.v r) (ρP.v r) fuel (sub s (ρP.v r)) →
      d ≤ psi s z z ∨ d ≤ spArg (ρP.v i) z (sumN (Lc.map ρP.o)) := by
    intro haV fuel d hd
    have hK := hAG r L hlen hr n hn σ ρP hCN hCP hGP i hri hi hg Lc c R hCL
      (ρP.v r) (Or.inl haV.symm) (le_refl _)
    exact hK.2 s y hcv hVs fuel d hd
  exact frameDom_sh_root hV hV' hVV ha hVa hcOT rfl
    (hFOP i hi Lc c R hCL) hVs htr2 hDom
    (fun u hu => hRoot u (le_trans hu (le_trans hVa
      (le_shf_self hV hV' (le_of_lt hVV) ha hVa)))) hKG hFD

end Ytosk.FDCopyRoot

namespace Ytosk.FDCopyRoot
open T FDCopy
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

theorem t2FDCopyRes_of_pathXR (hB : WfT2X.T2BelowXResV2X) (hFO : T2FOSeedV2)
    (hVS : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VAncUse M)
    (hAG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAK KAG M) : T2FDCopyRes := by
  intro M ρ rk C hz h2
  exact t2CopyK_FDshAt_of_pathXR C (hB M ρ rk C) hz h2
    (hFO M ρ rk C hz h2) (hVS M ρ rk C hz h2) (hAG M ρ rk C hz h2)

end Ytosk.FDCopyRoot
