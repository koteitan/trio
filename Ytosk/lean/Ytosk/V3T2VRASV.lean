/-
**t = 2 の種の列の枠の VSmallRAll: sv の場合（2026-10-17、lead）。**

残り T2VRASeedSVC の sv の欄を、M と M.take x だけの残り `T2SVc0` に減らす。
- sv では x は r で数えられない（x − 1 が x へ上げ、x は子がないので topped）。よって CL_M(r) = CL_{M.take x}(r)
  （`cl_sv`）。N = M[n] では CL_N(r) = CL_{M.take x}(r) ++ [x]（`sv_frame`）。
- r の枠のうち、最後の子 c₀（M.take x での r の最後の数える子）より前は M の枠そのもの（値は M と同じ、`T2SVc0` の欄）。
  c₀ の枠は N の値 o_{M.take x}(c₀) = ψ_s(y) が y ≠ 0 なら M の値 ψ_s(y_M)（同じ添字、y ≤ y_M）で、引き金と split は
  M の枠に移り、結論は添字 s だけによる（`vra_lift_sv`）。最後の枠（子 x）の添字は V + 1 で自明。
- 段は M の段（t2VRASeed_of と同じ `pathLv_of_shape`・`T2VRAPre`）。

実測（tmp/lead/probes/svpre.py）: d3s・deep2・expP の sv の種 6900 件で CL_M(r) = CL_{M.take x}(r)、c₀ より前の値は
同じ、c₀ は y ≠ 0 の 1300 件すべてで同じ添字と y ≤ y_M。
-/
import Ytosk.V3T2VRASeed
import Ytosk.V3T2SeedSV
import Ytosk.V3ExpT1R
import Ytosk.V3T2SeedPre
import Ytosk.V3T2SeedSVCl

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- **The frames of a seed column whose last counted child `c₀` of `M` is followed by `x′` in `N`**: before `c₀`
the frames of `M`; the frame of `c₀` moves to `M` when the new child has the same subscript and a smaller argument;
the last frame is given (`hlast`). -/
theorem vra_lift_sv {M N : Mat} {ρ σ : Valn} {i c0 x' : Nat} {Lc0 : List Nat}
    (hVM : VSmallRAll M ρ) (hCLM : CL M i = Lc0 ++ [c0]) (hCLN : CL N i = Lc0 ++ [c0, x'])
    (hvr : σ.v i = ρ.v i) (hLc : ∀ d ∈ Lc0, σ.o d = ρ.o d)
    (hc0 : ∀ s y, σ.o c0 = psi s y z → y ≠ z → ∃ yM, ρ.o c0 = psi s yM z ∧ y ≤ yM)
    (hlev : ∀ u, LevAt N σ i u → LevAt M ρ i u)
    (hlast : ∀ u, LevAt M ρ i u → QVRAt (ρ.v i) ((Lc0 ++ [c0]).map σ.o) (σ.o x') u) :
    ∀ (Lc' : List Nat) (c : Nat) (R' : List Nat), CL N i = Lc' ++ c :: R' →
      ∀ u, LevAt N σ i u → QVRAt (σ.v i) (Lc'.map σ.o) (σ.o c) u := by
  intro Lc' c R' h u hu
  have hu' := hlev u hu
  rw [hCLN] at h
  rw [hvr]
  by_cases hR : R' = []
  · subst hR
    have h' : (Lc0 ++ [c0]) ++ [x'] = Lc' ++ [c] := by rw [← h]; simp
    obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
    simp only [List.cons.injEq, and_true] at h2
    subst h1; subst h2
    exact hlast u hu'
  · have h1 : Lc0 ++ [c0] = Lc' ++ c :: R'.dropLast := by
      have := congrArg List.dropLast h
      rw [show Lc0 ++ [c0, x'] = (Lc0 ++ [c0]) ++ [x'] by simp, List.dropLast_concat,
        List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil hR] at this
      exact this
    by_cases hR2 : R'.dropLast = []
    · rw [hR2] at h1
      obtain ⟨h3, h4⟩ := List.append_inj' h1 rfl
      simp only [List.cons.injEq, and_true] at h4
      subst h3; subst h4
      have hLm : Lc0.map σ.o = Lc0.map ρ.o := List.map_congr_left hLc
      intro s y hsy ht hsp hu2 g hg
      have hy : y ≠ z := fun h0 => by rw [h0] at ht; exact T.not_lt_z _ ht.1
      obtain ⟨yM, hyM, hyy⟩ := hc0 s y hsy hy
      have hpp : psi s y z ≤ psi s yM z := by
        rcases (le_iff _ _).mp hyy with h5 | h5
        · exact psi_le_psi_of (Or.inr ⟨rfl, Or.inl h5⟩)
        · exact psi_le_psi_of (Or.inr ⟨rfl, Or.inr ⟨h5, le_refl _⟩⟩)
      rw [hLm] at ht ⊢
      exact (vsmallRAll_iff.mp hVM) i Lc0 c0 [] hCLM u hu' s yM hyM
        ⟨lt_of_lt_of_le ht.1 hyy, lt_of_lt_of_le ht.2 hpp⟩ (split_fst_ne_of_le hsp hyy) hu2 g hg
    · have hdl : (Lc' ++ c :: R'.dropLast).dropLast = Lc0 := by rw [← h1]; simp
      rw [List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil hR2] at hdl
      have hLs : ∀ d ∈ Lc', d ∈ Lc0 := fun d hd => by rw [← hdl]; exact List.mem_append_left _ hd
      have hcs : c ∈ Lc0 := by rw [← hdl]; simp
      have hclM : CL M i = Lc' ++ c :: (R'.dropLast.dropLast ++ [c0]) := by rw [hCLM, ← hdl]; simp
      rw [List.map_congr_left (fun d hd => hLc d (hLs d hd)), hLc c hcs]
      exact (vsmallRAll_iff.mp hVM) i Lc' c _ hclM u hu'

/-- **In the sv case `x` is not counted by `r`**, so `CL_M(r) = CL_{M.take x}(r)`. -/
theorem cl_sv {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk) {r L : Nat}
    (hlen : r + L + 1 = M.length) (hq : par M 0 (r + L) = some r) (hux : upg M (r + L - 1) = some (r + L)) :
    CL M r = CL (M.take (r + L)) r := by
  have hrx : r < r + L := par_lt M 0 _ _ hq
  have hL : 0 < L := by omega
  have hx : r + L + 1 = M.length := hlen
  have hxc : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  -- `x` is an upgrade target without children
  have hnx : ¬ Counted M r (r + L) := by
    rintro ⟨_, h⟩
    apply h
    refine ⟨?_, ?_⟩
    · unfold isUpg
      rw [List.any_eq_true]
      exact ⟨r + L - 1, List.mem_range.mpr (by omega), by simp [hux]⟩
    · have hch : children M (r + L) = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro d hd
        have h1 := (mem_children hd).1
        have h2 := (mem_children hd).2
        omega
      unfold topped; rw [hch]; rfl
  unfold CL
  rw [children_split_x hx hxc, List.filter_append, children_take]
  have hx' : List.filter (fun c => decide (Counted M r c)) [r + L] = [] := by simp [hnx]
  rw [hx', List.append_nil]
  apply List.filter_congr
  intro d hd
  have h := List.mem_filter.mp hd
  have hdx : d < r + L := by simpa using h.2
  have hdr : d ≠ r := fun e => by have := (mem_children h.1).1; omega
  simp only [decide_eq_decide]
  constructor
  · intro hM; exact counted_take_of hlen hL hq hdx hdr hM hrx
  · intro hT
    exact hcnt r d hrx (by rw [children_take]; exact List.mem_filter.mpr ⟨h.1, by simpa using hdx⟩) hT

/-- **Residual (t2, sv): the last counted child `c₀` of `r` in `M.take x`.** The children before `c₀` have the values
of `M`, and the value of `c₀` with a nonzero argument has the subscript of `o_M(c₀)` and a smaller argument. -/
def T2SVc0 (M : Mat) (ρ : Valn) (r L : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ Lc0 c0, CL (M.take (r + L)) r = Lc0 ++ [c0] →
    (∀ d ∈ Lc0, τ.o d = ρ.o d) ∧ ∀ s y, τ.o c0 = psi s y z → y ≠ z → ∃ yM, ρ.o c0 = psi s yM z ∧ y ≤ yM

/-- **The C part of `T2VRASeedSVC`** (the sv part is `t2VRASeedSVC_of`). -/
def T2VRASeedC (M : Mat) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
    (∃ q, par M 0 (r + L) = some q ∧ q ≠ r ∧ ¬ ∃ Lc, CL M r = Lc ++ [q]) →
    ∀ n, 2 ≤ n → ∀ σ, Cons (G2 M r L n) σ → Good3 (G2 M r L n) σ →
      ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL (G2 M r L n) r = Lc ++ c :: R →
        ∀ u, LevAt (G2 M r L n) σ r u → QVRAt (σ.v r) (Lc.map σ.o) (σ.o c) u

/-- **`T2VRASeedSVC` from the sv residual `T2SVc0` and the C part `T2VRASeedC`.** -/
theorem t2VRASeedSVC_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hVM : VSmallRAll M ρ) (hPre : T2VRAPre M ρ)
    (hc0 : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → T2SVCase M r L → T2SVc0 M ρ r L)
    (hC : T2VRASeedC M) : T2VRASeedSVC M := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hGall := good3_expand_t2 hM hS I R hz h2 (t2BelowXE_of hB hM hS I R hz h2)
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
  have hBS := t2BelowXS_of hB hM hS I R hz h2 hlen hr n hn hGlow σ hCN
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
      refine pathLv_of_shape I.cons hCN (c := r) (fun k hk => ?_) (fun k u hk hku => ?_) u hu
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

/-! ## 種の列の枠の形（T2SeedPreShapeSVC）の sv の欄 -/

/-- **The C part of `T2SeedPreShapeSVC`.** -/
def T2SeedPreShapeC (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → T2CCase M r L → ∀ n, 2 ≤ n →
    ∀ σ, Cons (G2 M r L n) σ → Good3 (G2 M r L n) σ →
    ∀ p, T2Seed M r L p → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL (G2 M r L n) p = Lc ++ c :: R →
      c < r + L → (∀ q, par M 0 (r + L) = some q → c ≠ q) → ∀ s y, σ.o c = psi s y z →
      (lt (spArg (σ.v p) z (sumN (Lc.map σ.o))) y = true ∧ lt (psi (σ.v p) z z) (psi s y z) = true) →
      ∃ (Lc' R' : List Nat) (yM : T), CL M p = Lc' ++ c :: R' ∧ σ.v p = ρ.v p ∧ Lc'.map ρ.o = Lc.map σ.o ∧
        ρ.o c = psi s yM z ∧ y ≤ yM ∧
        (lt (spArg (ρ.v p) z (sumN (Lc'.map ρ.o))) yM = true ∧ lt (psi (ρ.v p) z z) (psi s yM z) = true)

/-- **`T2SeedPreShapeSVC` from the sv residual `T2SVc0` and the C part.** -/
theorem t2SeedPreShapeSVC_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hc0 : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → T2SVCase M r L → T2SVc0 M ρ r L)
    (hC : T2SeedPreShapeC M ρ) : T2SeedPreShapeSVC M ρ := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hGall := good3_expand_t2 hM hS I R hz h2 (t2BelowXE_of hB hM hS I R hz h2)
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

/-! ## C の場合 -/

/-- **The levels of the seed `r` in `M[n]` are levels of `M`** (as in `t2VRASeed_of`). -/
theorem seed_lev_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2) (hPre : T2VRAPre M ρ)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) {n : Nat} (hn : 2 ≤ n)
    (hGlow : ∀ m, 1 ≤ m → m < n → ∀ τ, Cons (G2 M r L m) τ → Good3 (G2 M r L m) τ)
    {σ : Valn} (hCN : Cons (G2 M r L n) σ) (hGN : Good3 (G2 M r L n) σ) :
    σ.v r = ρ.v r → ∀ u, LevAt (G2 M r L n) σ r u → LevAt M ρ r u := by
  have hBS := t2BelowXS_of hB hM hS I R hz h2 hlen hr n hn hGlow σ hCN
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
    refine pathLv_of_shape I.cons hCN (c := r) (fun k hk => ?_) (fun k u hk hku => ?_) u hu
    · have hkr : k < r := par_lt _ 0 r k hk
      exact (hBS k (by omega)).2.2.2.1 (hns k hkr)
    · have hkr : k < r := par_lt _ 0 r k hk
      exact hPre r L hlen hr n hn σ hCN hGN k (by omega) (hns k hkr) u hku

/-- **Residual (t2, C): the seed `r` of the C case in `M` and `M.take x`.** `x` does not change the counted children
of `r`, and the last counted child `c₀` of `r` in `M.take x` is as in `T2SVc0` (the components of `s′` at the levels of
`r` come from `T2SeedCBase`). -/
def T2CFrRes (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  CL M r = CL (M.take (r + L)) r ∧ T2SVc0 M ρ r L

/-- **The C seed frames of `M[n]`** from `seed_last_C` and `T2CFrRes`. -/
theorem seed_C_data {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2) (hRes : G.T2SeedPRes M ρ)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) (hq : par M 0 (r + L) = some q)
    (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q]) {n : Nat} (hn : 2 ≤ n) {σ : Valn}
    (hCN : Cons (G2 M r L n) σ) (hGN : Good3 (G2 M r L n) σ) :
    (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (G2 M r L m) τ → Good3 (G2 M r L m) τ) ∧
    ∃ τ0, Cons (M.take (r + L)) τ0 ∧ τ0.v r = ρ.v r ∧ CL (G2 M r L n) r = CL (M.take (r + L)) r ++ [q] ∧
      (∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d) ∧ σ.v r = ρ.v r ∧ (∃ Y, σ.o q = psi (qnS M ρ r L q) Y z) := by
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hGall := good3_expand_t2 hM hS I R hz h2 (t2BelowXE_of hB hM hS I R hz h2)
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

/-- **`T2VRASeedC` from `T2CFrRes`.** -/
theorem t2VRASeedC_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk)
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
    seed_C_data hB hM hS I R hz h2 hRes hlen hr hq hqr hncl hn hCN hGN
  have hlev := seed_lev_of hB hM hS I R hz h2 hPre hlen hr hn hGlow hCN hGN hvr
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

/-- **`T2SeedPreShapeC` from `T2CFrRes`.** -/
theorem t2SeedPreShapeC_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk)
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
  obtain ⟨_, τ0, hC0, _, hCLN, hσT, hvr, _⟩ := seed_C_data hB hM hS I R hz h2 hRes hlen hr hq hqr hncl hn hCN hGN
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
