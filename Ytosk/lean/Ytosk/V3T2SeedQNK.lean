/-
**t = 2 の種の残り T2SeedPResRC の qn・C の欄から、項の補題で出る欄を外す（2026-10-17、lead）。**

qn の欄は「すべての k で V < t_k、f(t_k) ≥ s′ + 1、k ≥ 1 で t_k < v(q) と t_k = v(q) か t_k ◁ v(q)」だった
（t_{k+1} = f(t_k) = s′ + σ(t_k − V)）。前の 2 つは V < t₁ と t₁ の標準形から出る（`tqN_facts`）:
V < t なら s′ < f(t)（`lt_shf`）なので f(t) は s′ + 1 より小さくない（`lt_succ_iff`）、V < s′ < f(t)。
残り `T2SeedPResRCV2B` の qn の欄は V < t₁・t₁ の標準形・k ≥ 1 の欄だけ。
C の rw（すべての k で r の枠が σ X_k を保つ）は X₁ < σ X₁ と T2SeedCBase の欄から出る（`c_rw_of_base`）。
-/
import Ytosk.V3TopV2
import Ytosk.V3T2SeedSVCl
import Ytosk.V3T2SeedFrV2
import Ytosk.V3T2VRASeed

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

/-- **The C frame of `r` keeps `σ X_k`** (`T2SeedCResR.rw`) from `X₁ < σ X₁` and `T2SeedCBase` (the summands of
`σ X₁` are at least `Ω_{s′+1}`): the frame of `q` keeps `Y = σ X_k`, and the frame of `r` rewrites (`X₁ < σ X₁ ≤ Y`)
to `H(s′, Y) = Y`. -/
theorem c_rw_of_base {M : Mat} {ρ : Valn} {r L q : Nat} (hV : isOT (ρ.v r) = true)
    (hs : isOT (qnS M ρ r L q) = true) (hXex : ∃ X, ρ.o r = psi (ρ.v r) X z) (h : T2SeedCBase M ρ r L q)
    (hst : ∀ τ, Cons (M.take (r + L)) τ → t2X1 M r L τ < sh (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ)) :
    ∀ τ, Cons (M.take (r + L)) τ → ∀ k,
      step (ρ.v r) (t2X1 M r L τ) (qnS M ρ r L q) (step (qnS M ρ r L q) z (qnS M ρ r L q)
        (sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k)) z) z =
      sh (ρ.v r) (qnS M ρ r L q) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k) := by
  intro τ hτ k
  obtain ⟨X, hX⟩ := hXex
  obtain ⟨_, _, _, T1, -, hX1, hT1, -, -, -, hhi, hot, -⟩ := h τ hτ X hX
  have hVV := qnS_gt M ρ r L q
  have hlt0 := hst τ hτ
  set V := ρ.v r
  set s' := qnS M ρ r L q
  set X1 := t2X1 M r L τ
  have hX1z : X1 ≠ z := by rw [hX1]; exact app_ne_z_right hT1
  have hY : sh V s' (shIt V s' X1 k) = shIt V s' (sh V s' X1) k := shIt_succ' X1 k
  have hhigh : ∀ g ∈ summands (sh V s' (shIt V s' X1 k)), ¬ g < psi (succ s') z z := by
    rw [hY]; exact b0_shIt hV hs hVV (isOT_sh hV hs hVV hot) hhi k
  have hne : sh V s' (shIt V s' X1 k) ≠ z := sh_ne_z (shIt_ne_z hX1z k)
  have hzlt : z < sh V s' (shIt V s' X1 k) := z_lt_of_ne_z hne
  have hin : step s' z s' (sh V s' (shIt V s' X1 k)) z = sh V s' (shIt V s' X1 k) := by
    unfold step
    rw [if_pos ⟨hzlt, psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hzlt⟩)⟩]
    exact H_of_high hs hhigh
  have hchain : ∀ j, sh V s' X1 ≤ sh V s' (shIt V s' X1 j) := by
    intro j
    induction j with
    | zero => exact le_refl _
    | succ j ih =>
      exact le_trans ih (le_sh hV hs (le_of_lt hVV) (isOT_sh hV hs hVV (isOT_shIt_svc hV hs hVV hot j)))
  rw [hin]
  unfold step
  rw [if_pos ⟨lt_of_lt_of_le hlt0 (hchain k), psi_lt_psi_z_iff.mpr (Or.inl hVV)⟩]
  exact H_of_high hs hhigh

/-- **`T2SeedCResR` with `rw` replaced by the `k`-free `X₁ < σ X₁`** (`un` is `¬ T2CBad` of the context). -/
structure T2SeedCResR2 (M : Mat) (ρ : Valn) (r L q : Nat) : Prop where
  decP : ∀ τ, Cons (M.take (r + L)) τ → ∀ Lc c0, CL (M.take (r + L)) r = Lc ++ [c0] →
    ∃ s y, τ.o c0 = psi s y z ∧ qnS M ρ r L q < s
  strict : ∀ τ, Cons (M.take (r + L)) τ → t2X1 M r L τ < sh (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ)
  lhd : ∀ τ, Cons (M.take (r + L)) τ → ∀ k, 1 ≤ k →
    Lhd z (psi (ρ.v r) (shIt (ρ.v r) (qnS M ρ r L q) (t2X1 M r L τ) k) z) (ρ.o r)

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
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCResR2 M ρ r L q

/-- **Residual (t2): the seed residuals with the reduced qn and C fields.** -/
def T2SeedPResRCV2B : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedPResRC2 M ρ

theorem t2SeedPResRCV2_of_B (hCl : T2SeedClV2B) (h : T2SeedPResRCV2B) : T2SeedPResRCV2 := by
  intro M ρ rk C hz h2
  have H := h M ρ rk C hz h2
  have IW := Inv3W.ofV2 C.S C.I
  refine ⟨H.qr, H.sv, fun r L q hlen hr hq hqr Lc hCL τ hτ => ?_, fun r L q hlen hr hq hqr hncl => ?_⟩
  swap
  · have hrM : r < M.length := by omega
    have HC := H.C r L q hlen hr hq hqr hncl
    obtain ⟨_, _, hCC⟩ := hCl M ρ rk C hz h2 r L hlen hr
    have hun : upg M (r + L - 1) = none := by
      by_contra hne
      exact C.good ⟨r, L, q, hlen, hr, hq, hqr, hncl, hne⟩
    exact ⟨HC.decP, hun, c_rw_of_base (IW.good.ot_v r hrM) (qnS_ot IW hrM L q) (o_arg_form IW hrM)
      (hCC q hq hqr hncl) HC.strict, HC.lhd⟩
  obtain ⟨t1, he, hVt, ht1, hk⟩ := H.qn r L q hlen hr hq hqr Lc hCL τ hτ
  have hrM : r < M.length := by omega
  have hF := tqN_facts (IW.good.ot_v r hrM) (qnS_ot IW hrM L q) (qnS_gt M ρ r L q) hVt ht1
  exact ⟨t1, he, fun k => ⟨(hF k).2.1, (hF k).2.2, hk k⟩⟩

/-! ## T2VRAQNDom の Lc ≠ [] の場合は T2SeedQNDom から -/

/-- **The residual `T2VRAQNDom` for `Lc = []`** (`q` is the only counted child of `r`; `B = 0`). -/
def T2VRAQNDom0 (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  ∀ u, LevAt M ρ r u → ¬ lt (ρ.v r) u = true → ∀ g ∈ comps u (qnS M ρ r L q),
    g ≤ psi (qnS M ρ r L q) z z ∨ ∃ d ∈ comps u (ρ.v r), g ≤ d

/-- **`T2VRAQNDom` from `T2SeedQNDom` (`Lc ≠ []`, every level) and `T2VRAQNDom0` (`Lc = []`).** -/
theorem t2VRAQNDom_of {M : Mat} {ρ : Valn} {r L q : Nat} {Lc : List Nat} (hD : T2SeedQNDom M ρ r L q Lc)
    (h0 : Lc = [] → T2VRAQNDom0 M ρ r L q) : T2VRAQNDom M ρ r L q Lc := by
  intro u hu hVu g hg
  by_cases hL : Lc = []
  · rcases h0 hL u hu hVu g hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rcases hD.1 hL u hVu g hg with h | h | h
    · left; rw [h]; exact z_le _
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

end Ytosk
