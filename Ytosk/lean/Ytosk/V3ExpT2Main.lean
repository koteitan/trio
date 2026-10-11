/-
**3 行・t = 2: hExp の t = 2 の部分の組み立て（`hExp_t2_main`）。**

`T2ExpRes`（V3ExpT2I）を、Good3 の 2 つの残り（`T2BelowXE`・`T2CopyResE`、V3ExpT2W）と、欄ごとの残り
`T2Rest`（t = 0 の `T0Rest` と同じ形）から組み立てる。
- 文脈 `T2Ctx`: M の不変条件、N = M[n]（n ≥ 2）の評価・順位・Good3。
- Good3 N は `good3_expand_t2`、rootS は Good3 から（`rootS_of_good`）。
-/
import Ytosk.V3ExpT2W
import Ytosk.V3ExpT2F

namespace Ytosk

open T

/-- **The context of a residual field of `N = M[n]`** (`t = 2`): `M` with its invariants, and the
valuation of `N` with its ranking and `Good3`. -/
def T2Ctx (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (n : Nat) (σ : Valn)
    (rkN : Bool → Nat → Nat) : Prop :=
  Std M ∧ M ≠ SRO ∧ Inv3 M ρ rk ∧ Res3A M ρ rk ∧ col M (M.length - 1) ≠ (0, 0, 0) ∧
    TRIO.srow M (M.length - 1) = 2 ∧ 2 ≤ n ∧ Cons (expand M n) σ ∧ Rk (expand M n) rkN ∧
    Good3 (expand M n) σ

/-- **A residual value field `F` of `N = M[n]`** (`t = 2`), in the context `T2Ctx`. -/
def T2Field (F : Mat → Valn → Prop) : Prop :=
  ∀ M ρ rk n σ rkN, T2Ctx M ρ rk n σ rkN → F (expand M n) σ

/-- **The residual `Res3A` of `N = M[n]`** (`t = 2`). -/
def T2Res3A : Prop :=
  ∀ M ρ rk n σ rkN, T2Ctx M ρ rk n σ rkN → Res3A (expand M n) σ rkN

/-- **The remaining value fields of `N = M[n]`** (`t = 2`) and its `Res3A`, one named residual each. -/
structure T2Rest : Prop where
  vs : T2Field VSmallF
  fc : T2Field FrameClosed
  fo : T2Field FrameOT
  kd : T2Field BumpKidsDec
  td : T2Field BumpTermDec
  ad : T2Field AbsD
  au : T2Field AbsU
  tp1 : T2Field TP1C
  tplo : T2Field TPLo
  tp1w : T2Field TP1WC
  tplow : T2Field TPLoW
  auw : T2Field AbsUW
  adw : T2Field AbsDW
  trig : T2Field TrigOmC
  tplon : T2Field TPLoN
  adn : T2Field AbsDN
  rootP : T2Field RootP
  res : T2Res3A

/-- The part of `Good3` before `x`, for every `M` of type `t = 2`. -/
def T2BelowXAll : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → T2BelowXE M

/-- The boundary facts of the copies, for every `M` of type `t = 2`. -/
def T2CopyResAll : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
    TRIO.srow M (M.length - 1) = 2 → T2CopyResE M

/-- **`T2ExpRes` from the residuals**: `Good3` of `M[n]` from `T2BelowXAll` and `T2CopyResAll`, `rootS`
from `Good3`, the other fields from `T2Rest`. -/
theorem t2ExpRes_of (hBX : T2BelowXAll) (hCR : T2CopyResAll) (hRest : T2Rest) : T2ExpRes := by
  intro M ρ rk hM hS I R hz h2 n hn σ rkN hCN hRN
  have hGN : Good3 (expand M n) σ :=
    good3_expand_t2 hM hS I R hz h2 (hBX M ρ rk hM hS I R hz h2) (hCR M ρ rk hM hS I R hz h2) n
      (by omega) σ hCN
  have hctx : T2Ctx M ρ rk n σ rkN := ⟨hM, hS, I, R, hz, h2, hn, hCN, hRN, hGN⟩
  have F := fun {G : Mat → Valn → Prop} (h : T2Field G) => h M ρ rk n σ rkN hctx
  exact ⟨⟨hCN, hGN, hRN, F hRest.vs, F hRest.fc, F hRest.fo, F hRest.kd, F hRest.td, F hRest.ad,
    F hRest.au, F hRest.tp1, F hRest.tplo, F hRest.tp1w, F hRest.tplow, F hRest.auw, F hRest.adw,
    F hRest.trig, F hRest.tplon, F hRest.adn, rootS_of_good hCN hGN, F hRest.rootP⟩,
    hRest.res M ρ rk n σ rkN hctx⟩

/-- **`hExp` for `t = 2` from the residuals.** -/
theorem hExp_t2_main (hBX : T2BelowXAll) (hCR : T2CopyResAll) (hRest : T2Rest) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
      ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN :=
  hExp_t2 (t2ExpRes_of hBX hCR hRest)

end Ytosk
