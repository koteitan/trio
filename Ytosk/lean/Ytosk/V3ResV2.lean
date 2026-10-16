/-
**Inv3V2 の上の最上位の残りの仮定（2026-10-16、top）。**

最上位の定理 `trio_terminates_main_V2`（V3MainV2）の仮定を、ここで 1 つずつ名前つきの Prop にする。
どの仮定も旧 `Inv3`・`Inv3V`（標準形で偽の欄 AbsD・TPLo・AbsUW・TrigOmC を含む）を使わない。

行列ごとの残り（どの標準形でも、Inv3V2 から言う）:
- `HDropV2`: 1 列落としの残り `DropResH`（drop）。
- `HSeedV2`: t = 1・q = r の始点の条件 `SeedR`（drop）。
- `HAbSV2`: t = 0 の強い吸収 `AbsSR`（drop）。t = 2 の欄は使われておらず偽だったので外した（2026-10-16）。

各段の残り:
- `HTakeV2`: 1 列落とし。`inv3V2_take` の残り `TakeResV2`（落とした行列の枠の欄・葉）（drop）。根の RootP は証明済み。
- `ExpT0V2`: t = 0、n ≥ 2 の展開の Inv3V2（t0）。下降は最上位で t0_main' から出す。
- `ExpT1V2`: t = 1 の 1 コピーごとの Inv3V2 の保存 `ExpStepT1`（t1）。
  `qr_final_inv3V2`・`qn_final_inv3V2` に渡し、展開の Inv3V2 と下降の両方を出す（`expT1Out_of_step`）。
  別の道で示すなら、結論の形 `ExpT1OutV2` を直接示してもよい。
- `ExpT2V2`: t = 2、n ≥ 2 の展開の Inv3V2（t2）。
- `R2V2`: t = 2 の下降の残り `Res3T2`（t2）。

展開の仮定は文脈 `StepCtxV2` を受け取る: M の SInv・Inv3V2・Res3A と、全ての接頭辞 M.take j（1 ≤ j < |M|）の
Inv3V2・Res3A。接頭辞の評価は `drop1 M j rk`、順位は M と同じ rk（評価を取り替えないので合同の補題は要らない）。
-/
import Ytosk.V3TakeInv2
import Ytosk.V3DropRH
import Ytosk.V3T2Top

namespace Ytosk

open T

/-! ## 行列ごとの残り -/

/-- **R-drop**: the one-column drop residual of every standard matrix with the redesigned invariant. -/
def HDropV2 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V2 M ρ rk →
    DropResH M (M.length - 1) ρ (drop1 M (M.length - 1) rk)

/-- **R-seed**: the seed condition (`hcs` of `t = 1`, `q = r`) of every standard matrix. -/
def HSeedV2 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V2 M ρ rk → SeedR M ρ rk

/-- **R-abs**: the strong absorption `AbsSR` (`t = 0`) of every standard matrix. -/
def HAbSV2 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V2 M ρ rk → AbsSR M ρ

/-! ## 1 列落とし -/

/-- The residual of `inv3V2_take`: the frame fields and the two leaf conditions of the dropped matrix
`M.take x` with the drop valuation `drop1 M x rk`. (`RootP` at a root column `x` is proved,
`rootP0_take` in V3MainV2.) -/
structure TakeResV2 (M : Mat) (rk : Bool → Nat → Nat) : Prop where
  frame : TakeFrameV2 (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) rk
  leaf : TP1LeafG (M.take (M.length - 1)) (drop1 M (M.length - 1) rk)
  leafW : TP1WLeafG (M.take (M.length - 1)) (drop1 M (M.length - 1) rk)

/-- **R-take**: the one-column drop step. -/
def HTakeV2 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3V2 M ρ rk → Res3A M ρ rk → TakeResV2 M rk

/-! ## 展開 -/

/-- **What an expansion step knows about `M`**: its invariants and those of all its prefixes, with the drop
valuations and the same ranking. -/
structure StepCtxV2 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  std : Std M
  ne : M ≠ SRO
  S : SInv M
  I : Inv3V2 M ρ rk
  R : Res3A M ρ rk
  pre : ∀ j, 1 ≤ j → j < M.length →
    Inv3V2 (M.take j) (drop1 M j rk) rk ∧ Res3A (M.take j) (drop1 M j rk) rk

/-- **R-t0**: the expansions `M[n]` (`n ≥ 2`) with a last column of type `t = 0` have the invariant. -/
def ExpT0V2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (expand M n) ρN rkN

/-- **R-t1**: at `t = 1` (`x = r + L`, `r = P_1(x)`), one added copy keeps the invariant (`ExpStepT1`). -/
def ExpT1V2 : Prop :=
  ∀ M ρ rk r L d0, StepCtxV2 M ρ rk → r + L + 1 = M.length → 0 < L →
    entry M 0 (r + L) = entry M 0 r + d0 → par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
    ExpStepT1 (fun N σ => ∃ rkN, Inv3V2 N σ rkN) M r L d0 ρ

/-- The conclusion that the `t = 1` engines give: the invariant of `M[n]` and the descent of the root. -/
def ExpT1OutV2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 →
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (expand M n) ρN rkN ∧
      isOT (root (expand M n) ρN) = true ∧ root (expand M n) ρN < root M ρ

/-- **R-t2**: the expansions `M[n]` (`n ≥ 2`) with a last column of type `t = 2` have the invariant. -/
def ExpT2V2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (expand M n) ρN rkN

/-- **R-t2d**: the remaining facts `Res3T2` of the descent at `t = 2`. -/
def R2V2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    Res3T2 M ρ rk

end Ytosk
