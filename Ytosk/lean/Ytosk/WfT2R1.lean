/-
**WfT2R1: the `VRA` consumers of `T2BelowXResAt` with `T2BelowXResAtX` (2026-11-01, t = 2 Bad2 route).**

Copies (suffix `XR`) of `t2VRAPre_of` (V3T2VRAPre), `t2VRASeed_of`・`t2VRASeedG_of` (V3T2VRASeed), the seed
lemmas of V3T2VRASV and `vsmallRAll_expand_t2`・`t2VRAV2_of` (V3T2VRA), with `t2BelowXS_of` replaced by
`WfT2X.t2BelowXS_ofX` (frame shape `FrameShapeX`) and the frame-shape readers replaced by their X versions
(WfT2X5・WfT2X6・WfT2X7). `pathLv_of_shapeXR`: `pathLv_of_shape` with `FrameShapeX`.
-/
import Ytosk.WfT2X8
import Ytosk.V3T2VRASV
import Ytosk.V3T2VRA
import Ytosk.V3T2VRAPre
import Ytosk.V3T2VRASeed

namespace Ytosk

open T Classical

/-- **`pathLv_of_shape` (V3T2VRASeed) with `FrameShapeX`.** -/
theorem pathLv_of_shapeXR {M N : Mat} {ρ σ : Valn} (hC : Cons M ρ) (hCN : Cons N σ) {c : Nat}
    (hS : ∀ k, par N 0 c = some k → WfAbsW.FrameShapeX M N ρ σ k)
    (hup : ∀ k u, par N 0 c = some k → PathLvAll N σ k u → PathLvAll M ρ k u) :
    ∀ u, PathLvAll N σ c u → PathLvAll M ρ c u := by
  intro u h
  have hpar : ∀ {k : Nat} {Lc R : List Nat}, CL N k = Lc ++ c :: R → par N 0 c = some k := by
    intro k Lc R hcl
    exact (mem_children_iff.mp (cl_mem_children (show c ∈ CL N k by rw [hcl]; simp))).2
  cases h with
  | top hcl hsy ht =>
    obtain ⟨y', hclM, hv, hLc, hy', ht'⟩ := WfT2X.rw_frame_of_shapeX hC hCN (hS _ (hpar hcl)) hcl hsy ht
    rw [← hv]
    exact PathLvAll.top hclM hy' ht'
  | step hcl hsy ht hk =>
    obtain ⟨y', hclM, hv, hLc, hy', ht'⟩ := WfT2X.rw_frame_of_shapeX hC hCN (hS _ (hpar hcl)) hcl hsy ht
    exact PathLvAll.step hclM hy' ht' (hup _ u (hpar hcl) hk)

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The path levels before `x`** (away from `q ≠ r`) are levels of `M`. -/
theorem pathLvAll_pre_t2XR {M N : Mat} {ρ σ : Valn} {r L : Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hCN : Cons N σ) (hGN : Good3 N σ)
    (hshape : ∀ k, k < r + L → ¬ T2SeedCol M r L k → WfAbsW.FrameShapeX M N ρ σ k)
    (hSP : ∀ p, T2Seed M r L p → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N p = Lc ++ c :: R →
      c < r + L → (∀ q, par M 0 (r + L) = some q → c ≠ q) → ∀ s y, σ.o c = psi s y z →
      (lt (spArg (σ.v p) z (sumN (Lc.map σ.o))) y = true ∧ lt (psi (σ.v p) z z) (psi s y z) = true) →
      ∃ (Lc' R' : List Nat) (yM : T), CL M p = Lc' ++ c :: R' ∧ σ.v p = ρ.v p ∧ Lc'.map ρ.o = Lc.map σ.o ∧
        ρ.o c = psi s yM z ∧ y ≤ yM ∧
        (lt (spArg (ρ.v p) z (sumN (Lc'.map ρ.o))) yM = true ∧ lt (psi (ρ.v p) z z) (psi s yM z) = true))
    (hqc : ∀ q, par M 0 (r + L) = some q → q ≠ r → ∀ c ∈ CL N q, ¬ c < r + L) :
    ∀ c u, PathLvAll N σ c u → c < r + L → (∀ q, par M 0 (r + L) = some q → q ≠ r → c ≠ q) →
      PathLvAll M ρ c u := by
  -- one frame of the path
  have hframe : ∀ k (Lc : List Nat) c (R : List Nat) s y, CL N k = Lc ++ c :: R → σ.o c = psi s y z →
      (lt (spArg (σ.v k) z (sumN (Lc.map σ.o))) y = true ∧ lt (psi (σ.v k) z z) (psi s y z) = true) →
      c < r + L → (∀ q, par M 0 (r + L) = some q → q ≠ r → c ≠ q) →
      (∀ q, par M 0 (r + L) = some q → q ≠ r → k ≠ q) ∧
      ∃ (Lc' R' : List Nat) (yM : T), CL M k = Lc' ++ c :: R' ∧ σ.v k = ρ.v k ∧
        ρ.o c = psi s yM z ∧
        (lt (spArg (ρ.v k) z (sumN (Lc'.map ρ.o))) yM = true ∧ lt (psi (ρ.v k) z z) (psi s yM z) = true) := by
    intro k Lc c R s y hcl hsy ht hcx hcq
    have hcCL : c ∈ CL N k := by rw [hcl]; simp
    have hkc := (mem_children (cl_mem_children hcCL)).1
    have hkq : ∀ q, par M 0 (r + L) = some q → q ≠ r → k ≠ q := by
      intro q hq hqr hkq; subst hkq; exact hqc k hq hqr c hcCL hcx
    refine ⟨hkq, ?_⟩
    by_cases hsc : T2SeedCol M r L k
    · rcases hsc with hsd | ⟨q, hq, hqr, hkq'⟩
      · obtain ⟨Lc', R', yM, h1, h2, _, h4, _, h6⟩ := hSP k hsd Lc c R hcl hcx
          (fun q hq => by
            by_cases hqr : q = r
            · intro hcq'; subst hcq'
              rcases hsd with ⟨_, hkr⟩ | ⟨q', hq', hq'r, _⟩
              · omega
              · rw [hq] at hq'; cases hq'; exact absurd hqr hq'r
            · exact hcq q hq hqr) s y hsy ht
        exact ⟨Lc', R', yM, h1, h2, h4, h6⟩
      · exact absurd hkq' (hkq q hq hqr)
    · obtain ⟨Lc', R', yM, h1, h2, _, h4, _, h6⟩ :=
        WfT2X.frame_of_shapeX hC hG hCN hGN (hshape k (by omega) hsc) hcl hsy ht
      exact ⟨Lc', R', yM, h1, h2, h4, h6⟩
  intro c u hp
  induction hp with
  | @top k c Lc R s y hcl hsy ht =>
    intro hcx hcq
    obtain ⟨_, Lc', R', yM, h1, h2, h4, h6⟩ := hframe k Lc c R s y hcl hsy ht hcx hcq
    rw [h2]; exact PathLvAll.top h1 h4 h6
  | @step k c Lc R s y u hcl hsy ht _ ih =>
    intro hcx hcq
    obtain ⟨hkq, Lc', R', yM, h1, _, h4, h6⟩ := hframe k Lc c R s y hcl hsy ht hcx hcq
    have hkc := (mem_children (cl_mem_children (show c ∈ CL N k by rw [hcl]; simp))).1
    exact PathLvAll.step h1 h4 h6 (ih (by omega) hkq)

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The C seed frames of `M[n]`** from `seed_last_C` and `T2CFrRes`. -/
theorem seed_C_dataXR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2) (hRes : G.T2SeedPRes M ρ)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) (hq : par M 0 (r + L) = some q)
    (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q]) {n : Nat} (hn : 2 ≤ n) {σ : Valn}
    (hCN : Cons (G2 M r L n) σ) (hGN : Good3 (G2 M r L n) σ) :
    (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (G2 M r L m) τ → Good3 (G2 M r L m) τ) ∧
    ∃ τ0, Cons (M.take (r + L)) τ0 ∧ τ0.v r = ρ.v r ∧ CL (G2 M r L n) r = CL (M.take (r + L)) r ++ [q] ∧
      (∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d) ∧ σ.v r = ρ.v r ∧ (∃ Y, σ.o q = psi (qnS M ρ r L q) Y z) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hGall := good3_expand_t2 hM hS I R hz h2 (WfT2X.t2BelowXE_ofX hB hM hS I R hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I R hz h2)
  have hx : M.length - 1 = r + L := by omega
  have hlen2 : 2 ≤ M.length := by have := par_lt M 2 _ _ hr; omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = G2 M r L m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, hx]; exact hr)
    rw [h2, hx] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hGlow : ∀ m, 1 ≤ m → m < n → ∀ τ, Cons (G2 M r L m) τ → Good3 (G2 M r L m) τ :=
    fun m hm _ τ hτ => by rw [← hexp m] at hτ ⊢; exact hGall m hm τ hτ
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [hx] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  obtain ⟨hCR, hBig⟩ := hRes.C r L q hlen hr hq hqr hncl
  have hFix := G.t2SeedCFix_of hM hS I R hlen hr hq hqr hncl hCR hBig
  obtain ⟨_, _, hCLN, hσT, hσv, _, _, hoq, _, _⟩ :=
    G.seed_last_C hM hS I R hz h2 hlen hr hq hqr hncl hCR hFix hC0 hRk1 n hn hGlow σ hCN hGN
  have hv0 := v_take_of_untopped I hlen (par_lt M 2 _ _ hr) (topP_C hM hS I hlen hr hq hqr) hC0
  exact ⟨hGlow, _, hC0, hv0, hCLN, hσT, hσv, ⟨_, hoq⟩⟩

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **`T2SeedPreShapeC` from `T2CFrRes`.** -/
theorem t2SeedPreShapeC_ofXR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2) (hRes : G.T2SeedPRes M ρ)
    (hCF : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2CFrRes M ρ r L q) : T2SeedPreShapeC M ρ := by
  intro r L hlen hr hcase n hn σ hCN hGN p hp Lc c R' hCL hcx hcq s y hsy ht
  obtain ⟨q, hq, hqr, hncl⟩ := hcase
  have hpr : p = r := by
    rcases hp with ⟨h, _⟩ | ⟨q', hq', _, hpq⟩
    · rw [hq] at h; cases h; exact absurd rfl hqr
    · rw [hq] at hq'; cases hq'
      rw [par0_q_t2 hM hS I hlen hr hq hqr] at hpq; cases hpq; rfl
  subst hpr
  obtain ⟨_, τ0, hC0, _, hCLN, hσT, hvr, _⟩ := seed_C_dataXR hB hM hS I R hz h2 hRes hlen hr hq hqr hncl hn hCN hGN
  obtain ⟨hCLM, hc0⟩ := hCF p L q hlen hr hq hqr hncl
  rw [hCLN] at hCL
  have hR : R' ≠ [] := by
    rintro rfl
    obtain ⟨_, h2'⟩ := List.append_inj' hCL rfl
    simp only [List.cons.injEq, and_true] at h2'
    exact hcq q hq h2'.symm
  have h1 : CL (M.take (p + L)) p = Lc ++ c :: R'.dropLast := by
    have := congrArg List.dropLast hCL
    rw [List.dropLast_concat, List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil hR] at this
    exact this
  rcases List.eq_nil_or_concat (CL (M.take (p + L)) p) with hT | ⟨Lc0, c0, hT0⟩
  · rw [hT] at h1; simp at h1
  have hT : CL (M.take (p + L)) p = Lc0 ++ [c0] := by rw [hT0, List.concat_eq_append]
  obtain ⟨hLc0, hc0'⟩ := hc0 τ0 hC0 Lc0 c0 hT
  have hσρ : ∀ d ∈ Lc0, σ.o d = ρ.o d := fun d hd => by
    rw [hσT d (by rw [hT]; exact List.mem_append_left _ hd)]; exact hLc0 d hd
  rw [hT] at h1
  by_cases hR2 : R'.dropLast = []
  · rw [hR2] at h1
    obtain ⟨h3, h4⟩ := List.append_inj' h1 rfl
    simp only [List.cons.injEq, and_true] at h4
    subst h3; subst h4
    have hLm : Lc0.map ρ.o = Lc0.map σ.o := List.map_congr_left (fun d hd => (hσρ d hd).symm)
    have hy : y ≠ z := fun h0 => by rw [h0] at ht; exact T.not_lt_z _ ht.1
    obtain ⟨yM, hyM, hyy⟩ := hc0' s y (by rw [← hσT c0 (by rw [hT]; simp)]; exact hsy) hy
    have hpp : psi s y z ≤ psi s yM z := by
      rcases (le_iff _ _).mp hyy with h5 | h5
      · exact psi_le_psi_of (Or.inr ⟨rfl, Or.inl h5⟩)
      · exact psi_le_psi_of (Or.inr ⟨rfl, Or.inr ⟨h5, le_refl _⟩⟩)
    refine ⟨Lc0, [], yM, by rw [hCLM, hT], hvr, hLm, hyM, hyy, ?_⟩
    rw [hLm, ← hvr]
    exact ⟨lt_of_lt_of_le ht.1 hyy, lt_of_lt_of_le ht.2 hpp⟩
  · have hdl : (Lc ++ c :: R'.dropLast).dropLast = Lc0 := by rw [← h1]; simp
    rw [List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil hR2] at hdl
    have hLs : ∀ d ∈ Lc, d ∈ Lc0 := fun d hd => by rw [← hdl]; exact List.mem_append_left _ hd
    have hcs : c ∈ Lc0 := by rw [← hdl]; simp
    have hclM : CL M p = Lc ++ c :: (R'.dropLast.dropLast ++ [c0]) := by rw [hCLM, hT, ← hdl]; simp
    have hLm : Lc.map ρ.o = Lc.map σ.o := List.map_congr_left (fun d hd => (hσρ d (hLs d hd)).symm)
    refine ⟨Lc, _, y, hclM, hvr, hLm, by rw [← hσρ c hcs]; exact hsy, le_refl _, ?_⟩
    rw [hLm, ← hvr]; exact ht

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **VSmallRAll of every `M[n]`** (`t = 2`, `n ≥ 1`) from VSmallRAll of `M` and `M.take x` and the named
residuals. -/
theorem vsmallRAll_expand_t2XR {K : T → T → T → List T → T → T → Prop} (hsh : QVRAshK K) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk)
    (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hVM : VSmallRAll M ρ)
    (hVT : ∀ τ, Cons (M.take (M.length - 1)) τ → VSmallRAll (M.take (M.length - 1)) τ)
    (hSeed : T2VRASeed M) (hPre : T2VRAPre M ρ) (hCopy : T2VRACopyEsc M) (hKM : T2VRAK K M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → VSmallRAll (expand M n) σ := by
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
  rw [hL] at hr hVT
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by omega
  have hd0 : 0 < entry M 0 (r + L) - entry M 0 r := by omega
  have hd1 : 0 < entry M 1 (r + L) - entry M 1 r := by omega
  have hexp : ∀ n, expand M n = G2 M r L n := by
    intro n
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hG : ∀ m, 1 ≤ m → ∀ σ, Cons (G2 M r L m) σ → Good3 (G2 M r L m) σ :=
    fun m hm σ hσ => by rw [← hexp m] at hσ ⊢; exact hGall m hm σ hσ
  have hRk : ∀ m, 1 ≤ m → ∃ rk, Rk (G2 M r L m) rk := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hBE : ∀ m, 1 ≤ m → BumpE2 (G2 M r L m) := fun m _ => by
    rw [← hexp m]; exact (sInvX_expand hX m).loc.2.2.1
  have hCR := t2CopyResAll_holds M ρ rk hM hS I R hz h2 r L hlen hr
  have hBS := WfT2X.t2BelowXS_ofX hB hM hS I R hz h2 hlen hr
  have hSD := hX.loc.1
  have key : ∀ n, 1 ≤ n → ∀ σ, Cons (G2 M r L n) σ → VSmallRAll (G2 M r L n) σ := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        intro σ hσ
        unfold G2 at hσ ⊢
        rw [gexp_one_gen hlen] at hσ ⊢
        exact hVT σ hσ
      · intro σ hCN
        have hn2 : 2 ≤ m + 1 := by omega
        obtain ⟨rkP, hRP⟩ := hRk m hm0
        set ρP := rhsIt (G2 M r L m) (rkBound (G2 M r L m) rkP) with hρP
        have hCP : Cons (G2 M r L m) ρP := cons_of_rk hRP
        have hGP := hG m hm0 _ hCP
        have hQP := ih hm0 _ hCP
        have hm : m + 1 - 1 = m := by omega
        obtain ⟨hKV, hB', hV', hVV⟩ := hCR (m + 1) hn2 σ _ hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP)
        have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBE m hm0)
        have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r hX.r0p hSD
        have hF := copy_facts_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBE m hm0)
          hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP) (by rw [hm]; exact hRP) hK hKV hRK hB' hV' hVV
        rw [hm] at hF
        have hlN : (G2 M r L (m + 1)).length = r + (m + 1) * L := TRIO.gexp_length hlen
        have hlP : (G2 M r L m).length = r + m * L := TRIO.gexp_length hlen
        have hmL : (m + 1) * L = m * L + L := Nat.succ_mul m L
        have hrP : r < (G2 M r L m).length := by
          have : L ≤ m * L := Nat.le_mul_of_pos_left L hm0
          omega
        have hGN := hG (m + 1) (by omega) σ hCN
        apply vsmallRAll_iff.mpr
        intro k Lc c Rr hCL u hu
        rcases Nat.lt_or_ge k (r + L) with hix | hix
        · by_cases hsc : T2SeedCol M r L k
          · exact hSeed r L hlen hr (m + 1) hn2 σ hCN hGN k hsc Lc c Rr hCL u hu
          · have hshp := (hBS (m + 1) hn2 (fun k hk1 _ τ hτ => hG k hk1 τ hτ) σ hCN
              (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩) k hix).2.2.2.1 hsc
            have hlevM : LevAt M ρ k u := by
              rcases hu with hu | hu
              · left
                rw [hu]
                rcases hshp with (⟨hv, _, _⟩ | ⟨hv, _⟩ | ⟨hN, _⟩) | ⟨hv, _⟩
                · exact hv
                · exact hv
                · rw [hN] at hCL; simp at hCL
                · exact hv
              · exact Or.inr (hPre r L hlen hr (m + 1) hn2 σ hCN hGN k hix hsc u hu)
            exact WfT2X.clField_of_shapeSX (Q := fun a Lv cv => QVRAt a Lv cv u)
              (fun a Lv cv cv' h1 h2 h3 h4 h5 => qVRAt_low a Lv cv cv' u h1 h2 h3 h4 h5)
              (WfT2X.qVRAt_lowV u) I.cons I.good hCN hGN hshp
              (fun Lc0 c0 R0 h => (vsmallRAll_iff.mp hVM) k Lc0 c0 R0 h u hlevM) Lc c Rr hCL
        · obtain ⟨a, rfl⟩ : ∃ a, k = r + a + L := ⟨k - L - r, by omega⟩
          have hia : r + a < (G2 M r L m).length := by
            have hkN : r + a + L < (G2 M r L (m + 1)).length :=
              (mem_children (cl_mem_children (show c ∈ CL _ (r + a + L) by rw [hCL]; simp))).1.trans
                (mem_children (cl_mem_children (show c ∈ CL _ (r + a + L) by rw [hCL]; simp))).2
            omega
          intro s y hsy ht hhi hku g hg
          by_cases hOmega : g ≤ psi s z z
          · exact Or.inl hOmega
          by_cases hState : g ≤ spArg (σ.v (r + a + L)) z (sumN (Lc.map σ.o))
          · exact Or.inr (Or.inl hState)
          obtain ⟨hu1, huV⟩ := hCopy r L hlen hr (m + 1) hn2 σ _ hCN hGN hCP hGP (r + a) (by omega) hia
            Lc c Rr hCL s y hsy ht hhi u hu hku g hg (lt_of_not_ge hOmega) (lt_of_not_ge hState)
          exact copyFrame_VRA hsh hF hCP hGP hrP hV' hVV (i := r + a) (by omega) hia (fun _ => huV)
            (fun hg Lc0 c0 R0 h => hKM r L hlen hr (m + 1) hn2 σ _ hCN hCP hGP (r + a) (by omega) hia hg
              Lc0 c0 R0 h u hu1 huV)
            (fun Lc0 c0 R0 h => (vsmallRAll_iff.mp hQP) (r + a) Lc0 c0 R0 h u hu1) Lc c Rr hCL
            s y hsy ht hhi hku g hg
  intro n hn σ hσ
  rw [hexp n] at hσ ⊢
  exact key n hn σ hσ

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **T2VRAV2 from the named residuals.** -/
theorem t2VRAV2_ofXR {K : T → T → T → List T → T → T → Prop} (hsh : QVRAshK K) (hB : WfT2X.T2BelowXResV2X)
    (hSeedG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRASeed M)
    (hPreG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAPre M ρ)
    (hCopyG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRACopyEsc M)
    (hKG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAK K M) : T2VRAV2 := by
  intro M ρ rk C hz h2 n hn σ rkN hCN _ _ _
  obtain ⟨hX, _⟩ := sInvXJ_std C.std C.ne
  have hl2 : 2 ≤ M.length := by
    obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
    rw [h2] at hr
    have := par_lt M 2 _ r hr; omega
  obtain ⟨I1, _⟩ := C.pre (M.length - 1) (by omega) (by omega)
  have hRk1 : Rk (M.take (M.length - 1)) rk := I1.rank
  have hC1 := I1.cons
  exact vsmallRAll_expand_t2XR hsh (hB M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 C.I.vra
    (fun τ hτ => vsmallRAll_congr (agree_of_cons hC1 hτ hRk1) I1.vra)
    (hSeedG M ρ rk C hz h2) (hPreG M ρ rk C hz h2) (hCopyG M ρ rk C hz h2) (hKG M ρ rk C hz h2) n (by omega) σ hCN

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **T2VRASeed** (`VSmallRAll` at the seed frames of `M[n]`) for qr and qn, with the residuals `T2VRAQNDom`
and `T2VRASeedSVC` (sv, C). The levels of `r` are those of `M` (`pathLv_of_shapeXR`, `T2VRAPre`). -/
theorem t2VRASeed_ofXR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hVM : VSmallRAll M ρ) (hRes : G.T2SeedPRes M ρ) (hPre : T2VRAPre M ρ)
    (hQN : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc)
    (hSVC : T2VRASeedSVC M) : T2VRASeed M := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hGall := good3_expand_t2 hM hS I R hz h2 (WfT2X.t2BelowXE_ofX hB hM hS I R hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I R hz h2)
  have hlen1 : 1 ≤ M.length := by
    rcases hM0 : M with _ | _
    · rw [hM0] at hz; exact absurd rfl hz
    · simp
  have hRk1 : Rk (M.take (M.length - 1)) rk :=
    rk_take (by omega) I.rank (counted_take_last (M := M) hlen1 I.r0p I.z2 I.sd I.z1 I.uat)
  have hC1 := cons_of_rk hRk1
  set τ0 := rhsIt (M.take (M.length - 1)) (rkBound (M.take (M.length - 1)) rk) with hτ0
  intro r L hlen hr n hn σ hCN hGN i hsc Lc c R' hCL u hu
  have hx : M.length - 1 = r + L := by omega
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = G2 M r L m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, hx]; exact hr)
    rw [h2, hx] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hGlow : ∀ m, 1 ≤ m → m < n → ∀ τ, Cons (G2 M r L m) τ → Good3 (G2 M r L m) τ :=
    fun m hm _ τ hτ => by rw [← hexp m] at hτ ⊢; exact hGall m hm τ hτ
  have hBS := WfT2X.t2BelowXS_ofX hB hM hS I R hz h2 hlen hr n hn hGlow σ hCN
    (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩)
  have hC0 : Cons (M.take (r + L)) τ0 := by rw [← hx]; exact hC1
  have hR0 : Rk (M.take (r + L)) rk := by rw [← hx]; exact hRk1
  -- the columns before `r` are not seeds
  have hns : ∀ k, k < r → ¬ T2SeedCol M r L k := by
    intro k hk hsk
    rcases hsk with (⟨_, hkr⟩ | ⟨q, hq, hqr, hpq⟩) | ⟨q, hq, hqr, hkq⟩
    · omega
    · rw [par0_q_t2 hM hS I hlen hr hq hqr] at hpq; cases hpq; omega
    · have := par_lt M 0 q r (par0_q_t2 hM hS I hlen hr hq hqr); omega
  -- the levels of `r` in `N` are levels of `M`
  have hlev : σ.v r = ρ.v r → ∀ u, LevAt (G2 M r L n) σ r u → LevAt M ρ r u := by
    intro hvr u hu
    rcases hu with hu | hu
    · exact Or.inl (by rw [hu, hvr])
    · right
      refine pathLv_of_shapeXR I.cons hCN (c := r) (fun k hk => ?_) (fun k u hk hku => ?_) u hu
      · have hkr : k < r := par_lt _ 0 r k hk
        exact (hBS k (by omega)).2.2.2.1 (hns k hkr)
      · have hkr : k < r := par_lt _ 0 r k hk
        exact hPre r L hlen hr n hn σ hCN hGN k (by omega) (hns k hkr) u hku
  by_cases hqr : par M 0 (r + L) = some r
  · -- q = r: the seed is `r`
    have hir : i = r := by
      rcases hsc with (⟨_, h⟩ | ⟨q, hq, hqr', _⟩) | ⟨q, hq, hqr', _⟩
      · exact h
      · rw [hqr] at hq; cases hq; exact absurd rfl hqr'
      · rw [hqr] at hq; cases hq; exact absurd rfl hqr'
    subst i
    by_cases hux : upg M (r + L - 1) = some (r + L)
    · exact hSVC r L hlen hr (Or.inl ⟨hqr, hux⟩) n hn σ hCN hGN Lc c R' hCL u hu
    · have hXu : ∀ j, upg M j ≠ some (r + L) := by
        intro j hj
        have := G.upg_last_eq hlen hj
        rw [this] at hj; exact hux hj
      obtain ⟨Lc0, hLc0⟩ := G.cl_qr I.z2 hlen hr hqr hXu
      obtain ⟨Y, hox, _, hCLN, hvr, hLc⟩ :=
        seed_last_qr hM hS I R hz h2 hlen hr hqr hXu hLc0 (hRes.qr r L hlen hr hqr hXu Lc0 hLc0) hC0 ⟨rk, hR0⟩
          n hn hGlow σ hCN
      refine vra_lift hVM hLc0 hCLN hvr hLc (hlev hvr) (fun u _ => ?_) Lc c R' hCL u hu
      rw [hox]
      intro s y hsy _ _ _ g hg
      simp only [psi.injEq] at hsy
      obtain ⟨rfl, -⟩ := hsy
      rcases comps_succ_sub u g hg with h | h
      · left; rw [h]; exact z_le _
      · exact Or.inr (Or.inr ⟨g, h, le_refl _⟩)
  · -- q ≠ r
    obtain ⟨q, hq⟩ : ∃ q, par M 0 (r + L) = some q :=
      par0_some_of hrx (anc0_e0_lt (anc0_of_par M 2 r (r + L) hr) (by omega))
    have hqr' : q ≠ r := fun h => hqr (by rw [hq, h])
    have hir : i = r ∨ i = q := by
      rcases hsc with (⟨h, _⟩ | ⟨q', hq', _, hpq⟩) | ⟨q', hq', _, h⟩
      · exact absurd h hqr
      · rw [hq] at hq'; cases hq'
        rw [par0_q_t2 hM hS I hlen hr hq hqr'] at hpq; cases hpq; exact Or.inl rfl
      · rw [hq] at hq'; cases hq'; exact Or.inr h
    by_cases hcl : ∃ Lc0, CL M r = Lc0 ++ [q]
    · obtain ⟨Lc0, hLc0⟩ := hcl
      obtain ⟨ft, hCLN, hCLNq, hvr, hLc, hvx, hvq, hoq, _, _⟩ :=
        seed_last_qn hM hS I R hz h2 hlen hr hq hqr' hLc0 (hRes.qn r L q hlen hr hq hqr' Lc0 hLc0) hC0
          ⟨rk, hR0⟩ n hn hGlow σ hCN
      rcases hir with hir | hir <;> subst i
      · refine vra_lift hVM hLc0 hCLN hvr hLc (hlev hvr) (fun u hu' => ?_) Lc c R' hCL u hu
        rw [hoq]
        intro s y hsy _ _ hu2 g hg
        simp only [psi.injEq] at hsy
        obtain ⟨rfl, -⟩ := hsy
        exact hQN r L q hlen hr hq hqr' Lc0 hLc0 u hu' hu2 g hg
      · -- the frame of `q`: its only child has the subscript `v_N(q)`
        rw [hCLNq] at hCL
        have hc : c = r + L ∧ Lc = [] := by
          rcases Lc with _ | ⟨a, l⟩
          · simp at hCL; exact ⟨hCL.1.symm, rfl⟩
          · simp at hCL
        obtain ⟨rfl, rfl⟩ := hc
        have hxN : r + L < (G2 M r L n).length := by
          rw [TRIO.gexp_length hlen]
          have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
          omega
        obtain ⟨y0, hy0⟩ := o_psi_sub hCN hxN
        rw [sf_ot (hGN.ot_v _ hxN), hvx, ← hvq] at hy0
        exact qVRAt_self ⟨y0, hy0⟩
    · rcases hir with hir | hir <;> subst i
      · exact hSVC r L hlen hr (Or.inr ⟨q, hq, hqr', hcl⟩) n hn σ hCN hGN Lc c R' hCL u hu
      · -- the frame of `q` in the C case: as in qn
        obtain ⟨hCR, hBig⟩ := hRes.C r L q hlen hr hq hqr' hcl
        have hFix := G.t2SeedCFix_of hM hS I R hlen hr hq hqr' hcl hCR hBig
        obtain ⟨_, _, _, _, _, hvx, hvq, _, hCLNq, _⟩ :=
          G.seed_last_C hM hS I R hz h2 hlen hr hq hqr' hcl hCR hFix hC0 hR0 n hn hGlow σ hCN hGN
        rw [hCLNq] at hCL
        have hc : c = r + L ∧ Lc = [] := by
          rcases Lc with _ | ⟨a, l⟩
          · simp at hCL; exact ⟨hCL.1.symm, rfl⟩
          · simp at hCL
        obtain ⟨rfl, rfl⟩ := hc
        have hxN : r + L < (G2 M r L n).length := by
          rw [TRIO.gexp_length hlen]
          have : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
          omega
        obtain ⟨y0, hy0⟩ := o_psi_sub hCN hxN
        rw [sf_ot (hGN.ot_v _ hxN), hvx, ← hvq] at hy0
        exact qVRAt_self ⟨y0, hy0⟩

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **`T2SeedPreShapeSVC` from the sv residual `T2SVc0` and the C part.** -/
theorem t2SeedPreShapeSVC_ofXR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hc0 : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → T2SVCase M r L → T2SVc0 M ρ r L)
    (hC : T2SeedPreShapeC M ρ) : T2SeedPreShapeSVC M ρ := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hGall := good3_expand_t2 hM hS I R hz h2 (WfT2X.t2BelowXE_ofX hB hM hS I R hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I R hz h2)
  intro r L hlen hr hcase n hn σ hCN hGN p hp Lc c R' hCL hcx hcq s y hsy ht
  rcases hcase with ⟨hq, hux⟩ | hCc
  swap
  · exact hC r L hlen hr hCc n hn σ hCN hGN p hp Lc c R' hCL hcx hcq s y hsy ht
  have hpr : p = r := by
    rcases hp with ⟨_, h⟩ | ⟨q, hq', hqr, _⟩
    · exact h
    · rw [hq] at hq'; cases hq'; exact absurd rfl hqr
  subst hpr
  have hx : M.length - 1 = p + L := by omega
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = G2 M p L m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, hx]; exact hr)
    rw [h2, hx] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hGlow : ∀ m, 1 ≤ m → m < n → ∀ τ, Cons (G2 M p L m) τ → Good3 (G2 M p L m) τ :=
    fun m hm _ τ hτ => by rw [← hexp m] at hτ ⊢; exact hGall m hm τ hτ
  have hRk : ∀ m, 1 ≤ m → ∃ rk', Rk (G2 M p L m) rk' := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [hx] at hcnt
  have hRk1 : Rk (M.take (p + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  obtain ⟨hG0, hv0, _⟩ := sv_children_ctx hM hS I R hlen hr hq hux hC0
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
  have hCP := cons_of_rk hRP
  have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
  obtain ⟨hCLN, hσT, hσv, _, _⟩ := sv_frame hM hS I R hz h2 hlen hr hq hux (topP_sv hlen I.z2 I.z1 hr hq hux)
    hn hCN hRN hCP hGP hRP hC0 hG0 hRk1
  have hvr : σ.v p = ρ.v p := by rw [hσv, hv0]
  have hCLM := cl_sv I hlen hq hux
  rw [hCLN] at hCL
  have hR : R' ≠ [] := by
    rintro rfl
    obtain ⟨_, h2'⟩ := List.append_inj' hCL rfl
    simp only [List.cons.injEq, and_true] at h2'
    omega
  have h1 : CL (M.take (p + L)) p = Lc ++ c :: R'.dropLast := by
    have := congrArg List.dropLast hCL
    rw [List.dropLast_concat, List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil hR] at this
    exact this
  rcases List.eq_nil_or_concat (CL (M.take (p + L)) p) with hT | ⟨Lc0, c0, hT0⟩
  · rw [hT] at h1; simp at h1
  have hT : CL (M.take (p + L)) p = Lc0 ++ [c0] := by rw [hT0, List.concat_eq_append]
  obtain ⟨hLc0, hc0'⟩ := hc0 p L hlen hr ⟨hq, hux⟩ _ hC0 Lc0 c0 hT
  have hσρ : ∀ d ∈ Lc0, σ.o d = ρ.o d := fun d hd => by
    rw [hσT d (by rw [hT]; exact List.mem_append_left _ hd)]; exact hLc0 d hd
  rw [hT] at h1
  by_cases hR2 : R'.dropLast = []
  · rw [hR2] at h1
    obtain ⟨h3, h4⟩ := List.append_inj' h1 rfl
    simp only [List.cons.injEq, and_true] at h4
    subst h3; subst h4
    have hLm : Lc0.map ρ.o = Lc0.map σ.o := List.map_congr_left (fun d hd => (hσρ d hd).symm)
    have hy : y ≠ z := fun h0 => by rw [h0] at ht; exact T.not_lt_z _ ht.1
    obtain ⟨yM, hyM, hyy⟩ := hc0' s y (by rw [← hσT c0 (by rw [hT]; simp)]; exact hsy) hy
    have hpp : psi s y z ≤ psi s yM z := by
      rcases (le_iff _ _).mp hyy with h5 | h5
      · exact psi_le_psi_of (Or.inr ⟨rfl, Or.inl h5⟩)
      · exact psi_le_psi_of (Or.inr ⟨rfl, Or.inr ⟨h5, le_refl _⟩⟩)
    refine ⟨Lc0, [], yM, by rw [hCLM, hT], hvr, hLm, hyM, hyy, ?_⟩
    rw [hLm, ← hvr]
    exact ⟨lt_of_lt_of_le ht.1 hyy, lt_of_lt_of_le ht.2 hpp⟩
  · have hdl : (Lc ++ c :: R'.dropLast).dropLast = Lc0 := by rw [← h1]; simp
    rw [List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil hR2] at hdl
    have hLs : ∀ d ∈ Lc, d ∈ Lc0 := fun d hd => by rw [← hdl]; exact List.mem_append_left _ hd
    have hcs : c ∈ Lc0 := by rw [← hdl]; simp
    have hclM : CL M p = Lc ++ c :: (R'.dropLast.dropLast ++ [c0]) := by rw [hCLM, hT, ← hdl]; simp
    have hLm : Lc.map ρ.o = Lc.map σ.o := List.map_congr_left (fun d hd => (hσρ d (hLs d hd)).symm)
    refine ⟨Lc, _, y, hclM, hvr, hLm, by rw [← hσρ c hcs]; exact hsy, le_refl _, ?_⟩
    rw [hLm, ← hvr]; exact ht

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **`T2VRASeedSVC` from the sv residual `T2SVc0` and the C part `T2VRASeedC`.** -/
theorem t2VRASeedSVC_ofXR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hVM : VSmallRAll M ρ) (hPre : T2VRAPre M ρ)
    (hc0 : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → T2SVCase M r L → T2SVc0 M ρ r L)
    (hC : T2VRASeedC M) : T2VRASeedSVC M := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hGall := good3_expand_t2 hM hS I R hz h2 (WfT2X.t2BelowXE_ofX hB hM hS I R hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I R hz h2)
  intro r L hlen hr hcase n hn σ hCN hGN Lc c R' hCL u hu
  rcases hcase with ⟨hq, hux⟩ | hCc
  swap
  · exact hC r L hlen hr hCc n hn σ hCN hGN Lc c R' hCL u hu
  have hx : M.length - 1 = r + L := by omega
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = G2 M r L m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, hx]; exact hr)
    rw [h2, hx] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hGlow : ∀ m, 1 ≤ m → m < n → ∀ τ, Cons (G2 M r L m) τ → Good3 (G2 M r L m) τ :=
    fun m hm _ τ hτ => by rw [← hexp m] at hτ ⊢; exact hGall m hm τ hτ
  have hRk : ∀ m, 1 ≤ m → ∃ rk', Rk (G2 M r L m) rk' := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hBS := WfT2X.t2BelowXS_ofX hB hM hS I R hz h2 hlen hr n hn hGlow σ hCN
    (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩)
  have hns : ∀ k, k < r → ¬ T2SeedCol M r L k := by
    intro k hk hsk
    rcases hsk with (⟨_, hkr⟩ | ⟨q, hq', hqr, hpq⟩) | ⟨q, hq', hqr, hkq⟩
    · omega
    · rw [par0_q_t2 hM hS I hlen hr hq' hqr] at hpq; cases hpq; omega
    · have := par_lt M 0 q r (par0_q_t2 hM hS I hlen hr hq' hqr); omega
  have hlev : σ.v r = ρ.v r → ∀ u, LevAt (G2 M r L n) σ r u → LevAt M ρ r u := by
    intro hvr u hu
    rcases hu with hu | hu
    · exact Or.inl (by rw [hu, hvr])
    · right
      refine pathLv_of_shapeXR I.cons hCN (c := r) (fun k hk => ?_) (fun k u hk hku => ?_) u hu
      · have hkr : k < r := par_lt _ 0 r k hk
        exact (hBS k (by omega)).2.2.2.1 (hns k hkr)
      · have hkr : k < r := par_lt _ 0 r k hk
        exact hPre r L hlen hr n hn σ hCN hGN k (by omega) (hns k hkr) u hku
  -- the valuation of `M.take x`
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [hx] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  obtain ⟨hG0, hv0, _⟩ := sv_children_ctx hM hS I R hlen hr hq hux hC0
  -- the frames of `r` in `N`
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
  have hCP := cons_of_rk hRP
  have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
  obtain ⟨hCLN, hσT, hσv, hox, _⟩ := sv_frame hM hS I R hz h2 hlen hr hq hux (topP_sv hlen I.z2 I.z1 hr hq hux)
    hn hCN hRN hCP hGP hRP hC0 hG0 hRk1
  have hvr : σ.v r = ρ.v r := by rw [hσv, hv0]
  have hCLM := cl_sv I hlen hq hux
  have hlastG : ∀ (Lv : List T) u, QVRAt (ρ.v r) Lv (σ.o (r + L)) u := by
    intro Lv u
    rw [hox]
    intro s y hsy _ _ _ g hg
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, -⟩ := hsy
    rcases comps_succ_sub u g hg with h | h
    · left; rw [h]; exact z_le _
    · exact Or.inr (Or.inr ⟨g, h, le_refl _⟩)
  rcases List.eq_nil_or_concat (CL (M.take (r + L)) r) with hT | ⟨Lc0, c0, hT0⟩
  · rw [hT] at hCLN
    rw [hCLN] at hCL
    have hc : Lc = [] ∧ c = r + L := by
      rcases Lc with _ | ⟨a, l⟩
      · simp at hCL; exact ⟨rfl, hCL.1.symm⟩
      · simp at hCL
    obtain ⟨rfl, rfl⟩ := hc
    rw [hvr]; exact hlastG _ u
  · have hT : CL (M.take (r + L)) r = Lc0 ++ [c0] := by rw [hT0, List.concat_eq_append]
    obtain ⟨hLc0, hc0'⟩ := hc0 r L hlen hr ⟨hq, hux⟩ _ hC0 Lc0 c0 hT
    refine vra_lift_sv hVM (by rw [hCLM, hT]) (by rw [hCLN, hT]; simp) hvr
      (fun d hd => by rw [hσT d (by rw [hT]; exact List.mem_append_left _ hd)]; exact hLc0 d hd)
      (fun s y hs hy => hc0' s y (by rw [← hσT c0 (by rw [hT]; simp)]; exact hs) hy)
      (hlev hvr) (fun u _ => hlastG _ u) Lc c R' hCL u hu

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **`T2VRAPre` from `T2SeedPreShape`** (and t2's `T2BelowXRes`). -/
theorem t2VRAPre_ofXR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hSP : T2SeedPreShape M ρ) : T2VRAPre M ρ := by
  intro r L hlen hr n hn σ hCN hGN k hk hsc u hu
  have hGall := good3_expand_t2 hM hS I R hz h2 (WfT2X.t2BelowXE_ofX hB hM hS I R hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I R hz h2)
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hlen2 : 2 ≤ M.length := by have := par_lt M 2 _ r hr; omega
  have hL : M.length - 1 = r + L := by omega
  have hexp : ∀ m, expand M m = G2 M r L m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hG : ∀ m, 1 ≤ m → ∀ τ, Cons (G2 M r L m) τ → Good3 (G2 M r L m) τ :=
    fun m hm τ hτ => by rw [← hexp m] at hτ ⊢; exact hGall m hm τ hτ
  have hBS := WfT2X.t2BelowXS_ofX hB hM hS I R hz h2 hlen hr
  have hshape : ∀ j, j < r + L → ¬ T2SeedCol M r L j → WfAbsW.FrameShapeX M (G2 M r L n) ρ σ j :=
    fun j hj hsj => (hBS n hn (fun m hm1 _ τ hτ => hG m hm1 τ hτ) σ hCN
      (fun i _ hi => ⟨hGN.ot_o i hi, hGN.ot_v i hi⟩) j hj).2.2.2.1 hsj
  refine pathLvAll_pre_t2XR I.cons I.good hCN hGN hshape (hSP r L hlen hr n hn σ hCN hGN)
    (fun q hq hqr => q_nocnt_t2 hX hJ hlen hr (by omega) hq hqr) k u hu hk ?_
  intro q hq hqr hkq
  exact hsc (Or.inr ⟨q, hq, hqr, hkq⟩)

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The levels of the seed `r` in `M[n]` are levels of `M`** (as in `t2VRASeed_ofXR`). -/
theorem seed_lev_ofXR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2) (hPre : T2VRAPre M ρ)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) {n : Nat} (hn : 2 ≤ n)
    (hGlow : ∀ m, 1 ≤ m → m < n → ∀ τ, Cons (G2 M r L m) τ → Good3 (G2 M r L m) τ)
    {σ : Valn} (hCN : Cons (G2 M r L n) σ) (hGN : Good3 (G2 M r L n) σ) :
    σ.v r = ρ.v r → ∀ u, LevAt (G2 M r L n) σ r u → LevAt M ρ r u := by
  have hBS := WfT2X.t2BelowXS_ofX hB hM hS I R hz h2 hlen hr n hn hGlow σ hCN
    (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩)
  have hns : ∀ k, k < r → ¬ T2SeedCol M r L k := by
    intro k hk hsk
    rcases hsk with (⟨_, hkr⟩ | ⟨q, hq', hqr, hpq⟩) | ⟨q, hq', hqr, hkq⟩
    · omega
    · rw [par0_q_t2 hM hS I hlen hr hq' hqr] at hpq; cases hpq; omega
    · have := par_lt M 0 q r (par0_q_t2 hM hS I hlen hr hq' hqr); omega
  intro hvr u hu
  rcases hu with hu | hu
  · exact Or.inl (by rw [hu, hvr])
  · right
    refine pathLv_of_shapeXR I.cons hCN (c := r) (fun k hk => ?_) (fun k u hk hku => ?_) u hu
    · have hkr : k < r := par_lt _ 0 r k hk
      exact (hBS k (by omega)).2.2.2.1 (hns k hkr)
    · have hkr : k < r := par_lt _ 0 r k hk
      exact hPre r L hlen hr n hn σ hCN hGN k (by omega) (hns k hkr) u hku

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **`T2VRASeedC` from `T2CFrRes`.** -/
theorem t2VRASeedC_ofXR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : WfT2X.T2BelowXResAtX M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hVM : VSmallRAll M ρ) (hPre : T2VRAPre M ρ) (hRes : G.T2SeedPRes M ρ)
    (hCF : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2CFrRes M ρ r L q)
    (hCB : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCBase M ρ r L q) : T2VRASeedC M := by
  intro r L hlen hr hcase n hn σ hCN hGN Lc c R' hCL u hu
  obtain ⟨q, hq, hqr, hncl⟩ := hcase
  obtain ⟨hGlow, τ0, hC0, hv0, hCLN, hσT, hvr, Y, hoq⟩ :=
    seed_C_dataXR hB hM hS I R hz h2 hRes hlen hr hq hqr hncl hn hCN hGN
  have hlev := seed_lev_ofXR hB hM hS I R hz h2 hPre hlen hr hn hGlow hCN hGN hvr
  obtain ⟨hCLM, hc0⟩ := hCF r L q hlen hr hq hqr hncl
  have hdom : ∀ τ, Cons (M.take (r + L)) τ → ∀ u, LevAt M ρ r u → ¬ lt (ρ.v r) u = true →
      ∀ g ∈ comps u (qnS M ρ r L q), g ≤ psi (qnS M ρ r L q) z z ∨ g ≤ t2X1 M r L τ ∨
        ∃ d ∈ comps u (ρ.v r), g ≤ d := by
    intro τ hτ u hu' hVu g hg
    obtain ⟨X, hX⟩ := o_arg_form I (show r < M.length by omega)
    obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, hcl⟩ := hCB r L q hlen hr hq hqr hncl τ hτ X hX
    exact Or.inr (Or.inl (le_of_lt (hcl u hu' hVu g (List.mem_append_right _ hg))))
  have hlastG : ∀ u, LevAt M ρ r u → QVRAt (ρ.v r) ((CL (M.take (r + L)) r).map σ.o) (σ.o q) u := by
    intro u hu'
    rw [hoq]
    intro s y hsy _ _ hu2 g hg
    simp only [psi.injEq] at hsy
    obtain ⟨rfl, -⟩ := hsy
    have hX : spArg (ρ.v r) z (sumN ((CL (M.take (r + L)) r).map σ.o)) = t2X1 M r L τ0 := by
      unfold t2X1; rw [hv0, List.map_congr_left hσT]
    rw [hX]; exact hdom _ hC0 u hu' hu2 g hg
  rcases List.eq_nil_or_concat (CL (M.take (r + L)) r) with hT | ⟨Lc0, c0, hT0⟩
  · have hl := hlastG
    rw [hT] at hCLN hl
    rw [hCLN] at hCL
    have hc : Lc = [] ∧ c = q := by
      rcases Lc with _ | ⟨a, l⟩
      · simp at hCL; exact ⟨rfl, hCL.1.symm⟩
      · simp at hCL
    obtain ⟨rfl, rfl⟩ := hc
    rw [hvr]; exact hl u (hlev u hu)
  · have hT : CL (M.take (r + L)) r = Lc0 ++ [c0] := by rw [hT0, List.concat_eq_append]
    obtain ⟨hLc0, hc0'⟩ := hc0 τ0 hC0 Lc0 c0 hT
    refine vra_lift_sv (x' := q) hVM (by rw [hCLM, hT]) (by rw [hCLN, hT]; simp) hvr
      (fun d hd => by rw [hσT d (by rw [hT]; exact List.mem_append_left _ hd)]; exact hLc0 d hd)
      (fun s y hs hy => hc0' s y (by rw [← hσT c0 (by rw [hT]; simp)]; exact hs) hy)
      hlev (fun u hu' => by have := hlastG u hu'; rw [hT] at this; exact this) Lc c R' hCL u hu

end Ytosk

namespace Ytosk
open T Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The top-level form** of `T2VRASeed` (t1's `t2VRAV2_ofXR` argument `hSeedG`). -/
theorem t2VRASeedG_ofXR (hB : WfT2X.T2BelowXResV2X) (hPR : T2SeedPResV2)
    (hPreG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRAPre M ρ)
    (hQNG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r →
        par M 0 (r + L) = some q → q ≠ r → ∀ Lc, CL M r = Lc ++ [q] → T2VRAQNDom M ρ r L q Lc)
    (hSVCG : ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRASeedSVC M) :
    ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VRASeed M :=
  fun M ρ rk C hz h2 => t2VRASeed_ofXR (hB M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) C.toW hz h2 C.I.vra
    (hPR M ρ rk C hz h2) (hPreG M ρ rk C hz h2) (hQNG M ρ rk C hz h2) (hSVCG M ρ rk C hz h2)

end Ytosk
