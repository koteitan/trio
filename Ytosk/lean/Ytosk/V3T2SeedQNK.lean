/-
**t = 2 の種の残り T2SeedPResRC の qn の欄から、項の補題で出る 2 つの欄を外す（2026-10-17、lead）。**

qn の欄は「すべての k で V < t_k、f(t_k) ≥ s′ + 1、k ≥ 1 で t_k < v(q) と t_k = v(q) か t_k ◁ v(q)」だった
（t_{k+1} = f(t_k) = s′ + σ(t_k − V)）。前の 2 つは V < t₁ と t₁ の標準形から出る（`tqN_facts`）:
V < t なら s′ < f(t)（`lt_shf`）なので f(t) は s′ + 1 より小さくない（`lt_succ_iff`）、V < s′ < f(t)。
残り `T2SeedPResRCV2B` の qn の欄は V < t₁・t₁ の標準形・k ≥ 1 の欄だけ。
-/
import Ytosk.V3TopV2
import Ytosk.V3T2SeedSVCl

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The qn subscripts stay above `V`, and `f(t_k)` is not below `s′ + 1`.** -/
theorem tqN_facts {V V' t1 : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
    (hVt : V < t1) (ht1 : isOT t1 = true) :
    ∀ k, isOT (tqN V V' t1 k) = true ∧ V < tqN V V' t1 k ∧ ¬ shf V V' (tqN V V' t1 k) < succ V'
  | k => by
    have base : ∀ k, isOT (tqN V V' t1 k) = true ∧ V < tqN V V' t1 k := by
      intro k
      induction k with
      | zero => exact ⟨ht1, hVt⟩
      | succ k ih =>
        exact ⟨isOT_shf hV hV' hVV ih.1, lt_trans hVV (lt_shf hV hV' (le_of_lt hVV) ih.1 ih.2)⟩
    obtain ⟨hk, hVk⟩ := base k
    refine ⟨hk, hVk, fun h => ?_⟩
    exact lt_irrefl' _ (lt_of_lt_of_le (lt_shf hV hV' (le_of_lt hVV) hk hVk) (lt_succ_iff.mp h))

/-- **The seed residuals left at the top**, with the qn field reduced to `V < t₁`, the standard form of `t₁` and the
fields for `k ≥ 1`. -/
structure T2SeedPResRC2 (M : Mat) (ρ : Valn) : Prop where
  qr : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] → T2SeedQRResR M ρ r L Lc
  sv : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
    upg M (r + L - 1) = some (r + L) → T2SVStrict M ρ r L ∧
      ∀ τ, Cons (M.take (r + L)) τ → ∀ k, 1 ≤ k →
        Lhd z (psi (ρ.v r) (shIt (ρ.v r) (succ (ρ.v r)) (t2X1 M r L τ) k) z) (ρ.o r)
  qn : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → ∀ τ, Cons (M.take (r + L)) τ → ∃ t1,
      spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z) ∧
      ρ.v r < t1 ∧ isOT t1 = true ∧
      ∀ k, 1 ≤ k → tqN (ρ.v r) (qnS M ρ r L q) t1 k < ρ.v q ∧
        (tqN (ρ.v r) (qnS M ρ r L q) t1 k = ρ.v q ∨ Lhd z (tqN (ρ.v r) (qnS M ρ r L q) t1 k) (ρ.v q))
  C : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCResR M ρ r L q

/-- **Residual (t2): the seed residuals with the reduced qn field.** -/
def T2SeedPResRCV2B : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedPResRC2 M ρ

theorem t2SeedPResRCV2_of_B (h : T2SeedPResRCV2B) : T2SeedPResRCV2 := by
  intro M ρ rk C hz h2
  have H := h M ρ rk C hz h2
  have IW := Inv3W.ofV2 C.S C.I
  refine ⟨H.qr, H.sv, fun r L q hlen hr hq hqr Lc hCL τ hτ => ?_, H.C⟩
  obtain ⟨t1, he, hVt, ht1, hk⟩ := H.qn r L q hlen hr hq hqr Lc hCL τ hτ
  have hrM : r < M.length := by omega
  have hF := tqN_facts (IW.good.ot_v r hrM) (qnS_ot IW hrM L q) (qnS_gt M ρ r L q) hVt ht1
  exact ⟨t1, he, fun k => ⟨(hF k).2.1, (hF k).2.2, hk k⟩⟩

end Ytosk
