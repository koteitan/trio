/-
**WfCofC3 (2026-11-01): `HCountS` for `t = 1, 2` reduced to the last root.**

- `t = 1` never has the successor-argument type (`HNoSucc1`, measured: no `t = 1` matrix of `succ` type in any run).
- `t = 2`: the copies ascend in row 0, so `A[n]` has the roots of `A`; the roots before the last root `Rt` keep their
  values (`HRootKeep2`), and the count bound is at `Rt` (`HCntRoot2`: `fsD(o_A(Rt), k) ≤ o_{A[k+2]}(Rt)`).
  `fsD(tA, k) = S + fsD(o_A(Rt), k) ≤ S + o_{A[k+2]}(Rt) = val(A[k+2])` (`count_at_last_root`).
- `hCountS12_of`, and `evalFSNZ2_of_C3` (EvalFSNZ 2 from the WfCofH chain with all of `HCountS` replaced).

Design of the bound behind `HCntRoot2` (measured, not used in Lean yet; `HCntV2`): along the row-1 path from `x`
down to `Rt`, every column `c ≠ x` whose `v_A(c)` has the successor-argument type satisfies
`fsD(v_A(c), k) ≤ v_{A[k+2]}(c)` (the ω-bump of `v` counts the copies). The naive form at the last column of
`A[k+2]` is false (4678 failures at n = 2).
-/
import Ytosk.WfCofC2

namespace Ytosk.WfCofC3

open T Ytosk Ytosk.WfCofH2 Ytosk.WfCofH3 Ytosk.WfCofC1

set_option linter.unusedSectionVars false

/-- **Counting at the last root**: if `N` has the roots of `A`, the roots before the last root `Rt` keep their
values, and `fsD(o_A(Rt), η) ≤ o_N(Rt)`, then `fsD(root A, η) ≤ root N`. -/
theorem count_at_last_root (hRS : HRootSP) {A N : Mat} (hAs : Std A) (hNs : Std N) (hNE : A ≠ [])
    {ρA σ : Valn} {rkA rkN : Bool → Nat → Nat} (hCA : Cons A ρA) (hRA : Rk A rkA)
    (hCN : Cons N σ) (hRN : Rk N rkN) (hroots : roots N = roots A)
    {Rt : Nat} (hRA0 : Anc0 A Rt (A.length - 1)) (hR0 : col A Rt = (0, 0, 0))
    (hpre : ∀ c ∈ roots A, c < Rt → σ.o c = ρA.o c) {η : T}
    (hRt : fsD (ρA.o Rt) η ≤ σ.o Rt) : fsD (root A ρA) η ≤ root N σ := by
  have hpos : 0 < A.length := List.length_pos_of_ne_nil hNE
  have hx : A.length - 1 + 1 = A.length := by omega
  have hsplit := roots_split hx hRA0 hR0
  set pre := (roots A).filter (fun c => decide (c < Rt)) with hpreD
  have hpre_eq : ∀ c ∈ pre, σ.o c = ρA.o c := by
    intro c hc
    rw [hpreD, List.mem_filter] at hc
    exact hpre c hc.1 (by simpa using hc.2)
  have hMl : (roots A).map ρA.o = pre.map ρA.o ++ [ρA.o Rt] := by
    rw [hsplit, List.map_append, List.map_singleton]
  have hNl : (roots N).map σ.o = pre.map ρA.o ++ [σ.o Rt] := by
    rw [hroots, hsplit, List.map_append, List.map_singleton]
    congr 1
    exact List.map_congr_left hpre_eq
  obtain ⟨hsA, hpA⟩ := hRS A ρA rkA hAs hCA hRA
  obtain ⟨hsN, hpN⟩ := hRS N σ rkN hNs hCN hRN
  have hsAl : ∀ t ∈ pre.map ρA.o ++ [ρA.o Rt], Single t := by
    intro t ht'
    rw [← hMl] at ht'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht'
    exact hsA i hi
  have hsNl : ∀ t ∈ pre.map ρA.o ++ [σ.o Rt], Single t := by
    intro t ht'
    rw [← hNl] at ht'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht'
    exact hsN i hi
  have hrootA : root A ρA = app (sumN (pre.map ρA.o)) (ρA.o Rt) := by
    rw [root_eq_roots hsA hpA, hMl]
    rw [hMl] at hpA
    exact sumN_snoc_dec hsAl hpA
  have hrootN : root N σ = app (sumN (pre.map ρA.o)) (σ.o Rt) := by
    rw [root_eq_roots hsN hpN, hNl]
    rw [hNl] at hpN
    exact sumN_snoc_dec hsNl hpN
  have hRne : ρA.o Rt ≠ z := by
    obtain ⟨s, y, hsy⟩ := o_psi_form hCA (i := Rt) (by have := hRA0.le; omega)
    rw [hsy]; simp
  rw [hrootA, hrootN, fsD_app _ hRne]
  exact app_le_app_left _ hRt

/-- `t = 1` has no successor-argument point. -/
def HNoSucc1 : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) → lastTy A = 1 →
    ∀ tA, Val A tA → ∀ a b, ¬ SuccAt a b tA

/-- `t = 2`: `A[k+2]` has the roots of `A`, and the roots before the last root keep their values. -/
def HRootKeep2 : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) → lastTy A = 2 →
    ∀ tA, Val A tA → ∀ a b, SuccAt a b tA → ∀ ρA rkA, Cons A ρA → Rk A rkA →
    ∀ k σ rk, Cons (expand A (k + 2)) σ → Rk (expand A (k + 2)) rk →
    roots (expand A (k + 2)) = roots A ∧
    ∀ Rt, Anc0 A Rt (A.length - 1) → col A Rt = (0, 0, 0) → ∀ c ∈ roots A, c < Rt → σ.o c = ρA.o c

/-- `t = 2`: **the count bound at the last root**. -/
def HCntRoot2 : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) → lastTy A = 2 →
    ∀ tA, Val A tA → ∀ a b, SuccAt a b tA → ∀ ρA rkA, Cons A ρA → Rk A rkA →
    ∀ k σ rk, Cons (expand A (k + 2)) σ → Rk (expand A (k + 2)) rk →
    ∀ Rt, Anc0 A Rt (A.length - 1) → col A Rt = (0, 0, 0) → (∀ j, Rt < j → j ≤ A.length - 1 → entry A 0 j ≠ 0) →
      fsD (ρA.o Rt) (natT k) ≤ σ.o Rt

/-- Row-1 ancestors (the row-1 parent chain). -/
inductive Anc1 (M : Mat) : Nat → Nat → Prop
  | refl (b : Nat) : Anc1 M b b
  | step {a b c : Nat} : par M 1 c = some b → Anc1 M a b → Anc1 M a c

/-- The design of the `t = 2` count (named, measured; not used): the `ω`-bump of `v` along the row-1 path. -/
def HCntV2 : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) → lastTy A = 2 →
    ∀ tA, Val A tA → ∀ a b, SuccAt a b tA → ∀ ρA rkA, Cons A ρA → Rk A rkA →
    ∀ k σ rk, Cons (expand A (k + 2)) σ → Rk (expand A (k + 2)) rk →
    ∀ c, c < A.length - 1 → Anc1 A c (A.length - 1) → ∀ a' b', SuccAt a' b' (ρA.v c) →
      fsD (ρA.v c) (natT k) ≤ σ.v c

theorem hCountS12_of (hRS : HRootSP) (h1 : HNoSucc1) (hK : HRootKeep2) (hC : HCntRoot2) : HCountS12 := by
  intro A hAs hS hNE hz ht tA hv a b hSA k tN hvN
  have hty : lastTy A = 1 ∨ lastTy A = 2 := by
    unfold lastTy at ht ⊢
    split_ifs at ht ⊢ <;> simp_all
  rcases hty with ht1 | ht2
  · exact absurd hSA (h1 A hAs hS hNE hz ht1 tA hv a b)
  have I := sInv_std hAs hS
  obtain ⟨ρA, rkA, hCA, hRA, rfl⟩ := hv
  obtain ⟨σ, rkN, hCN, hRN, rfl⟩ := hvN
  obtain ⟨Rt, hRA0, hR0, hRl⟩ := root_t1 I.r01 I.r12 I.e00 (A.length - 1)
  obtain ⟨hroots, hpre⟩ := hK A hAs hS hNE hz ht2 _ ⟨ρA, rkA, hCA, hRA, rfl⟩ a b hSA ρA rkA hCA hRA k σ rkN
    hCN hRN
  have hRt := hC A hAs hS hNE hz ht2 _ ⟨ρA, rkA, hCA, hRA, rfl⟩ a b hSA ρA rkA hCA hRA k σ rkN hCN hRN
    Rt hRA0 hR0 hRl
  exact count_at_last_root hRS hAs (Std.exp _ hAs) hNE hCA hRA hCN hRN hroots hRA0 hR0
    (hpre Rt hRA0 hR0) hRt

/-- **`EvalFSNZ 2`** from the WfCofH chain with `HCID` and all of `HCountS` reduced. -/
theorem evalFSNZ2_of_C3 (hD : Desc3) (hG : HGood3) (hT : HDiagT1) (hE : HEngPath) (hRS : HRootSP)
    (hDL : WfCofC2.HDiagLoc) (hDS : WfCofC2.HDiagStep) (hP : HCntPath0)
    (h1 : HNoSucc1) (hK : HRootKeep2) (hC : HCntRoot2) : EvalFSNZ 2 :=
  evalFSNZ2_of_C hD hG hT hE hRS (WfCofC2.hCID_of hRS hDL hDS) hP (hCountS12_of hRS h1 hK hC)

/-- **Surjectivity** with the same hypotheses. -/
theorem surj_of_C3 (hD : Desc3) (hG : HGood3) (hT : HDiagT1) (hE : HEngPath) (hRS : HRootSP)
    (hDL : WfCofC2.HDiagLoc) (hDS : WfCofC2.HDiagStep) (hP : HCntPath0)
    (h1 : HNoSucc1) (hK : HRootKeep2) (hC : HCntRoot2) {t : T}
    (hot : isOT t = true) {n : Nat} {tN : T} (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj_of_evalFSNZ hD (evalFSNZ2_of_C3 hD hG hT hE hRS hDL hDS hP h1 hK hC) hot hvN hlt

end Ytosk.WfCofC3
