/-
**T2VRAPre on the V3 context from the seed residuals (2026-11-06).**

The C part `T2SeedPreShapeC` of the seed frame shape, split by `upg M (x − 1)` as in V3SeedPFAll:
- C1 (`upg M (x − 1) = none`): `CL_N(r) = CL_T(r) ++ [q]` (`seed_last_CV3` with `SeedPFResV3.C1`), `CL_M(r) = CL_T(r)`
  (`cl_C`), and the last counted child of `r` in `T = M.take x` (`T2SVc0`, proved: `t2SVc0_ofV3`).
- C2 (`x − 1` upgrades): the named residual `T2C2Kids` — `M[n]` adds `q` to the counted children of `r` of `M`, keeps
  `v(r)` and the children before the last one, and the last one keeps its subscript with an argument that does not grow.
`hPre_of`: the input `T2VRAPre` of `hN_of2` from `hBXU`, `SeedPFResV3` and `T2C2Kids`.
-/
import Ytosk.V3VRAPreU
import Ytosk.V3SeedVF
import Ytosk.V3SeedPFAll

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **Residual (t2, C2): the counted children of `r` in `M[n]`.** -/
def T2C2Kids (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  ∀ n, 2 ≤ n → ∀ σ, Cons (G2 M r L n) σ → Good3 (G2 M r L n) σ →
    CL (G2 M r L n) r = CL M r ++ [q] ∧ σ.v r = ρ.v r ∧
    ∀ Lc0 c0, CL M r = Lc0 ++ [c0] → (∀ d ∈ Lc0, σ.o d = ρ.o d) ∧
      ∀ s y, σ.o c0 = psi s y z → y ≠ z → ∃ yM, ρ.o c0 = psi s yM z ∧ y ≤ yM

/-- **The C1 seed frames of `M[n]`** (`seed_C_dataXR` on the V3 context). -/
theorem seed_C_dataV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowAtV3U M ρ)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    {r L q : Nat} (hlen : r + L + 1 = M.length) (hr : par M 2 (r + L) = some r) (hq : par M 0 (r + L) = some q)
    (hqr : q ≠ r) (hncl : ¬ ∃ Lc, CL M r = Lc ++ [q]) (hCR : CRel M ρ r L q) (hBig : T2SeedCBig M ρ r L q)
    {n : Nat} (hn : 2 ≤ n) {σ : Valn}
    (hCN : Cons (G2 M r L n) σ) (hGN : Good3 (G2 M r L n) σ) :
    ∃ τ0, Cons (M.take (r + L)) τ0 ∧ CL (G2 M r L n) r = CL (M.take (r + L)) r ++ [q] ∧
      (∀ d ∈ CL (M.take (r + L)) r, σ.o d = τ0.o d) ∧ σ.v r = ρ.v r := by
  have hGall := good3_expand_t2V3 hM hS I (Ctx.drop (len2_of_t2 Ctx hz h2)) hz h2
    (t2BelowXE_V3U hB hM hS I (Ctx.drop (len2_of_t2 Ctx hz h2)) hz h2) (t2CopyResV3 hM hS I hz h2)
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
  have hFix := t2SeedCFix_ofV3 hM hS I Ctx hlen hr hq hqr hncl hCR hBig
  obtain ⟨_, _, hCLN, hσT, hσv, _⟩ :=
    seed_last_CV3 hM hS I Ctx hz h2 hlen hr hq hqr hncl hCR hFix hC0 hRk1 n hn hGlow σ hCN hGN
  exact ⟨_, hC0, hCLN, hσT, hσv⟩

/-- **`T2SeedPreShapeC`** from `SeedPFResV3.C1` (C1) and `T2C2Kids` (C2). -/
theorem t2SeedPreShapeC_ofV3U {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowAtV3U M ρ)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hC1 : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → CRel M ρ r L q ∧ T2SeedCBig M ρ r L q)
    (hC2 : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → T2C2Kids M ρ r L q) :
    T2SeedPreShapeC M ρ := by
  intro r L hlen hr hcase n hn σ hCN hGN p hp Lc c R' hCL hcx hcq s y hsy ht
  obtain ⟨q, hq, hqr, hncl⟩ := hcase
  have hpr : p = r := by
    rcases hp with ⟨h, _⟩ | ⟨q', hq', _, hpq⟩
    · rw [hq] at h; cases h; exact absurd rfl hqr
    · rw [hq] at hq'; cases hq'
      rw [par0_q_t2 hM hS I hlen hr hq hqr] at hpq; cases hpq; rfl
  subst hpr
  -- the counted children of `p` in `M[n]` are `B ++ [q]`, `B` the children of `p` in `M`, with
  -- `σ.v p = ρ.v p`, the children before the last one with the values of `M`, the last one with a smaller argument
  obtain ⟨hCLN, hvr, hkid⟩ : CL (G2 M p L n) p = CL M p ++ [q] ∧ σ.v p = ρ.v p ∧
      ∀ Lc0 c0, CL M p = Lc0 ++ [c0] → (∀ d ∈ Lc0, σ.o d = ρ.o d) ∧
        ∀ s y, σ.o c0 = psi s y z → y ≠ z → ∃ yM, ρ.o c0 = psi s yM z ∧ y ≤ yM := by
    cases hu : upg M (p + L - 1) with
    | none =>
      obtain ⟨hCR, hBig⟩ := hC1 p L q hlen hr hq hqr hncl hu
      obtain ⟨τ0, hC0, hCLN, hσT, hvr⟩ := seed_C_dataV3 hB hM hS I Ctx hz h2 hlen hr hq hqr hncl hCR hBig hn hCN hGN
      have hCLM : CL M p = CL (M.take (p + L)) p := cl_C hM hS I hlen hr hq hqr hncl hu
      have hc0 : T2SVc0 M ρ p L := t2SVc0_ofV3 I Ctx hlen hr
      refine ⟨by rw [hCLN, hCLM], hvr, fun Lc0 c0 hT => ?_⟩
      rw [hCLM] at hT
      obtain ⟨hLc0, hc0'⟩ := hc0 τ0 hC0 Lc0 c0 hT
      refine ⟨fun d hd => by rw [hσT d (by rw [hT]; exact List.mem_append_left _ hd)]; exact hLc0 d hd, ?_⟩
      intro s y hsy hy
      exact hc0' s y (by rw [← hσT c0 (by rw [hT]; simp)]; exact hsy) hy
    | some k => exact hC2 p L q k hlen hr hq hqr hncl hu n hn σ hCN hGN
  rw [hCLN] at hCL
  have hR : R' ≠ [] := by
    rintro rfl
    obtain ⟨_, h2'⟩ := List.append_inj' hCL rfl
    simp only [List.cons.injEq, and_true] at h2'
    exact hcq q hq h2'.symm
  have h1 : CL M p = Lc ++ c :: R'.dropLast := by
    have := congrArg List.dropLast hCL
    rw [List.dropLast_concat, List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil hR] at this
    exact this
  rcases List.eq_nil_or_concat (CL M p) with hT | ⟨Lc0, c0, hT0⟩
  · rw [hT] at h1; simp at h1
  have hT : CL M p = Lc0 ++ [c0] := by rw [hT0, List.concat_eq_append]
  obtain ⟨hσρ, hc0'⟩ := hkid Lc0 c0 hT
  rw [hT] at h1
  by_cases hR2 : R'.dropLast = []
  · rw [hR2] at h1
    obtain ⟨h3, h4⟩ := List.append_inj' h1 rfl
    simp only [List.cons.injEq, and_true] at h4
    subst h3; subst h4
    have hLm : Lc0.map ρ.o = Lc0.map σ.o := List.map_congr_left (fun d hd => (hσρ d hd).symm)
    have hy : y ≠ z := fun h0 => by rw [h0] at ht; exact T.not_lt_z _ ht.1
    obtain ⟨yM, hyM, hyy⟩ := hc0' s y hsy hy
    have hpp : psi s y z ≤ psi s yM z := by
      rcases (le_iff _ _).mp hyy with h5 | h5
      · exact psi_le_psi_of (Or.inr ⟨rfl, Or.inl h5⟩)
      · exact psi_le_psi_of (Or.inr ⟨rfl, Or.inr ⟨h5, le_refl _⟩⟩)
    refine ⟨Lc0, [], yM, hT, hvr, hLm, hyM, hyy, ?_⟩
    rw [hLm, ← hvr]
    exact ⟨lt_of_lt_of_le ht.1 hyy, lt_of_lt_of_le ht.2 hpp⟩
  · have hdl : (Lc ++ c :: R'.dropLast).dropLast = Lc0 := by rw [← h1]; simp
    rw [List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil hR2] at hdl
    have hLs : ∀ d ∈ Lc, d ∈ Lc0 := fun d hd => by rw [← hdl]; exact List.mem_append_left _ hd
    have hcs : c ∈ Lc0 := by rw [← hdl]; simp
    have hclM : CL M p = Lc ++ c :: (R'.dropLast.dropLast ++ [c0]) := by rw [hT, ← hdl]; simp
    have hLm : Lc.map ρ.o = Lc.map σ.o := List.map_congr_left (fun d hd => (hσρ d (hLs d hd)).symm)
    refine ⟨Lc, _, y, hclM, hvr, hLm, by rw [← hσρ c hcs]; exact hsy, le_refl _, ?_⟩
    rw [hLm, ← hvr]; exact ht

/-- **The input `T2VRAPre`** of `hN_of2` from `hBXU`, `SeedPFResV3` (its C1 field) and the C2 residual `T2C2Kids`. -/
theorem hPre_of (hBXU : T2AtV3 T2BelowAtV3U) (hPF : T2AtV3 (fun M ρ => SeedPFResV3 M ρ))
    (hK : T2AtV3 (fun M ρ => ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r →
      par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k →
      T2C2Kids M ρ r L q)) :
    T2AtV3 (fun M ρ => T2VRAPre M ρ) := by
  intro M ρ rk C hz h2
  have I : Inv3W M ρ rk := coreW C.S C.I
  exact t2VRAPre_ofC (hBXU M ρ rk C hz h2) C.std C.ne I C hz h2
    (t2SeedPreShapeC_ofV3U (hBXU M ρ rk C hz h2) C.std C.ne I C hz h2 (hPF M ρ rk C hz h2).C1
      (hK M ρ rk C hz h2))

#print axioms hPre_of

end Ytosk.V3Main.SeedPF
