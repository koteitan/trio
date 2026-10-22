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
import Ytosk.V3CutPSh

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

/-- **`T2VRAQNDom` from its `Lc ≠ []` part and `T2VRAQNDom0` (`Lc = []`).** -/
theorem t2VRAQNDom_of {M : Mat} {ρ : Valn} {r L q : Nat} {Lc : List Nat}
    (hD : Lc ≠ [] → T2VRAQNDom M ρ r L q Lc)
    (h0 : Lc = [] → T2VRAQNDom0 M ρ r L q) : T2VRAQNDom M ρ r L q Lc := by
  intro u hu hVu g hg
  by_cases hL : Lc = []
  · rcases h0 hL u hu hVu g hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · exact hD hL u hu hVu g hg

/-- **`T2VRAQNDom0` from `T2SeedQNBase` with `Lc = []`**: `X₁ = Ω_{t₁}` with `t₁ ≤ s′`, and the components of `s′` at the
level `V` and the path levels are below `X₁`. -/
theorem t2VRAQNDom0_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk) {r L q : Nat}
    (hlen : r + L + 1 = M.length) (h : T2SeedQNBase M ρ r L q [])
    (hP : ∀ τ, Cons (M.take (r + L)) τ → ∃ t1,
      spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ []) (psi t1 z z)) :
    T2VRAQNDom0 M ρ r L q := by
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hC0 := cons_of_rk (rk_take (by omega) I.rank hcnt)
  obtain ⟨t1, ht1⟩ := hP _ hC0
  obtain ⟨-, hcV, hts, hcl⟩ := h _ hC0 t1 ht1
  have hB : app (t2B (ρ.v r) ρ []) (psi t1 z z) = psi t1 z z := rfl
  have hle : psi t1 z z ≤ psi (qnS M ρ r L q) z z := by
    rcases (le_iff _ _).mp (hts rfl) with h5 | h5
    · exact psi_le_psi_of (Or.inl h5)
    · rw [h5]
  intro u hu hVu g hg
  left
  rcases hu with rfl | hu
  · have := hcV g hg; rw [hB] at this; exact le_trans (le_of_lt this) hle
  · have := hcl u hu hVu g (List.mem_append_right _ hg); rw [hB] at this; exact le_trans (le_of_lt this) hle

/-! ## T2SeedCDom の段 V の欄は T2SeedCBase から -/

/-- **The residual `T2SeedCDom` without its level-`V` field** (2026-10-22): `s′` starts `f(s′) = s′ + σ(s′ − V)`, the subscript image
of `s′` (`prefB s′ (shf V s′ s′)`). With the cut `X₁ ∈ cutsNSG s′ (σ X₁)` of `T2SeedCFix` (`X₁` moves under `σ`, else the trigger
fails) the cut is at a position whose subscript starts with `s′` (`cutsPNS_of_fix`), every `σ^{k+1} X₁` has it
(`cutP_all`), and FrameDom at the C seed frame needs no condition on the components of `s′` (`frameDom_of_cutP`).
The earlier form (all levels `u ≤ V`: the components of `s′` are `0`, below `X₁` or below a component of `V`) is false on
standard matrices (expP's t = 2 one-column extensions, 28). -/
def T2SeedCDom1 (M : Mat) (ρ : Valn) (r L q : Nat) : Prop :=
  prefB (qnS M ρ r L q) (shf (ρ.v r) (qnS M ρ r L q) (qnS M ρ r L q)) = true

theorem t2SeedCDom_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk) {r L q : Nat}
    (hrM : r < M.length) (h1 : T2SeedCDom1 M ρ r L q) (hB : T2SeedCBase M ρ r L q) : G.T2SeedCDom M ρ r L q := by
  intro τ hτ
  obtain ⟨X, hX⟩ := o_arg_form I hrM
  obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, hcl⟩ := hB τ hτ X hX
  refine ⟨fun _ => h1, fun g hg => Or.inr ?_⟩
  exact le_of_lt (hcl _ (Or.inl rfl) (lt_irrefl' _) g (List.mem_append_right _ hg))

/-! ## T2SeedQNDom の段 V の欄は第 1 欄と T2SeedQNBase から -/

/-- **The residual `T2SeedQNDom` without its level-`V` field**, with `Lc ≠ []`: at every level `u ≤ V` the
components of `s′` are `0`, below `B`, below `Ω_{s′}`, below a component of `B` or below a component of `V` (what FrameDom
needs), and at the levels of `r` (`LevAt`) below `Ω_{s′}`, below `B` or below a component of `V` (`T2VRAQNDom`).
The earlier form (all levels, only `0`・`B`・`V`) is false on a standard matrix (2026-10-21). -/
def T2SeedQNDom1 (M : Mat) (ρ : Valn) (r L q : Nat) (Lc : List Nat) : Prop :=
  Lc ≠ [] →
    (∀ u, ¬ lt (ρ.v r) u = true → ∀ g ∈ comps u (qnS M ρ r L q),
      g = z ∨ g ≤ t2B (ρ.v r) ρ Lc ∨ g ≤ psi (qnS M ρ r L q) z z ∨
        (∃ d ∈ comps u (t2B (ρ.v r) ρ Lc), g ≤ d) ∨ ∃ d ∈ comps u (ρ.v r), g ≤ d) ∧
    T2VRAQNDom M ρ r L q Lc

/-- **`T2SeedQNDom` from `T2SeedQNDom1` and `T2SeedQNBase`.** The level-`V` field: with `Lc ≠ []` it is the
`LevAt` part at `u = V` (`V` has no components at its own level); with `Lc = []` the components of `s′` at the level
`V` are below `X₁ = Ω_{t₁}` and `t₁ ≤ s′`. -/
theorem t2SeedQNDom_of1 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3W M ρ rk) {r L q : Nat}
    {Lc : List Nat} (hlen : r + L + 1 = M.length) (h1 : T2SeedQNDom1 M ρ r L q Lc)
    (hB : T2SeedQNBase M ρ r L q Lc)
    (hP : ∀ τ, Cons (M.take (r + L)) τ → ∃ t1,
      spArg (τ.v r) z (sumN ((CL (M.take (r + L)) r).map τ.o)) = app (t2B (ρ.v r) ρ Lc) (psi t1 z z)) :
    T2SeedQNDom M ρ r L q Lc := by
  refine ⟨fun hL => (h1 hL).1, fun g hg => ?_⟩
  by_cases hL : Lc = []
  · subst hL
    have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
    rw [show M.length - 1 = r + L by omega] at hcnt
    have hC0 := cons_of_rk (rk_take (by omega) I.rank hcnt)
    obtain ⟨t1, ht1⟩ := hP _ hC0
    obtain ⟨-, hcV, hts, -⟩ := hB _ hC0 t1 ht1
    have hBz : app (t2B (ρ.v r) ρ []) (psi t1 z z) = psi t1 z z := rfl
    have hle : psi t1 z z ≤ psi (qnS M ρ r L q) z z := by
      rcases (le_iff _ _).mp (hts rfl) with h5 | h5
      · exact psi_le_psi_of (Or.inl h5)
      · rw [h5]
    left
    have := hcV g hg; rw [hBz] at this; exact le_trans (le_of_lt this) hle
  · rcases (h1 hL).2 (ρ.v r) (Or.inl rfl) (lt_irrefl' _) g hg with h | h | ⟨d, hd, _⟩
    · exact Or.inl h
    · exact Or.inr h
    · rw [comps_self (I.good.ot_v r (by omega))] at hd; simp at hd

/-- **Residual (t2): `T2SeedDomV2` with the qn part reduced to `T2SeedQNDom1` and the C part to `T2SeedCDom1`.** -/
def T2SeedDomV2B : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    (∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDom1 M ρ r L q Lc) ∧
    (∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCDom1 M ρ r L q)

theorem t2SeedDomV2_of_B (hCl : T2SeedClV2B) (hPB : T2SeedPResRCV2B) (h : T2SeedDomV2B) : T2SeedDomV2 := by
  intro M ρ rk C hz h2
  obtain ⟨hQ, hC1⟩ := h M ρ rk C hz h2
  refine ⟨fun r L q hlen hr hq hqr Lc hCL => ?_, fun r L q hlen hr hq hqr hncl => ?_⟩
  · exact t2SeedQNDom_of1 (Inv3W.ofV2 C.S C.I) hlen (hQ r L q hlen hr hq hqr Lc hCL)
      ((hCl M ρ rk C hz h2 r L hlen hr).1 q Lc hq hqr hCL)
      (fun τ hτ => let ⟨t1, he, _⟩ := (hPB M ρ rk C hz h2).qn r L q hlen hr hq hqr Lc hCL τ hτ; ⟨t1, he⟩)
  · exact t2SeedCDom_of (Inv3W.ofV2 C.S C.I) (by omega) (hC1 r L q hlen hr hq hqr hncl)
      ((hCl M ρ rk C hz h2 r L hlen hr).2.2 q hq hqr hncl)

end Ytosk
