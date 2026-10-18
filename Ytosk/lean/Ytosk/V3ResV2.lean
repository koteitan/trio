/-
**Inv3V2 の上の最上位の残りの仮定（2026-10-16、top）。**

最上位の定理 `trio_terminates_main_V2`（V3MainV2）の仮定を、ここで 1 つずつ名前つきの Prop にする。
どの仮定も旧 `Inv3`・`Inv3V`（標準形で偽の欄 AbsD・TPLo・AbsUW・TrigOmC を含む）を使わない。

行列ごとの残り（どの標準形でも、Inv3V2 から言う）:
- `HDropV2`: 1 列落としの残り `DropResH`（drop）。
- `HSeedV2`: t = 1・q = r の始点の条件 `SeedR`（drop）。
- `HAbSV2`: 展開が使う強い吸収 `AbsSR`（drop）。欄 lo（t = 0 の BumpAbsLo）と欄 upg（t = 1・q = r = x − 1 の強い
  UpgAbsX）。どちらも標準形で偽（drop、2026-10-17）。最上位はもう使わない（文脈の `Res3AW` は abS を持たない、
  2026-10-17）。古い t0 の入口（expT0V2_of・of2・of3）だけが引数で受ける。

各段の残り:
- `HTakeV2`: 1 列落とし。`inv3V2_take` の残り `TakeResV2`（落とした行列の枠の欄・葉）（drop）。根の RootP は証明済み。
- `ExpT0V2`: t = 0、n ≥ 2 の展開の Inv3V2（t0）。下降は最上位で t0_main' から出す。
- `ExpT1V2`: t = 1 の 1 コピーごとの Inv3V2 の保存 `ExpStepT1`（t1）。
  `qr_final_inv3V2`・`qn_final_inv3V2` に渡し、展開の Inv3V2 と下降の両方を出す（`expT1Out_of_step`）。
  別の道で示すなら、結論の形 `ExpT1OutV2` を直接示してもよい。
- `ExpT2V2`: t = 2、n ≥ 2 の展開の Inv3V2（t2）。
- `R2V2`: t = 2 の下降の残り `Res3T2`（t2）。

展開の仮定は文脈 `StepCtxV2` を受け取る: M の SInv・Inv3V2・Res3AW と、全ての接頭辞 M.take j（1 ≤ j < |M|）の
Inv3V2・Res3AW。Res3AW は Res3A から偽の強い吸収 abS を外したもの（drop・seed）。接頭辞の評価は `drop1 M j rk`、順位は M と同じ rk（評価を取り替えないので合同の補題は要らない）。
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

/-- **R-drop without the row-1 condition** (2026-10-17): `DropResH0` of every standard matrix. -/
def HDropV2W : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V2 M ρ rk →
    DropResH0 M (M.length - 1) ρ (drop1 M (M.length - 1) rk)

/-- **The strong absorption at `x − 1` for `t = 0` outside the easy shape** (2026-10-17): the parent `r` of
`x` is a bump child, or `r = x − 1` and its parent is a bump child (`¬ T0Easy`). The strong form fails on 2
standard matrices of std_a and 240 of std_b, all in the easy shape (the `t = 0` engines handle it: `r ≠ x − 1` by
`PO.zero_of_ne`, `r = x − 1` by the weak leaf, `t0_S1W`・`t0_S1AW`); outside it no counterexample. -/
def T0UpgAbsV2 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V2 M ρ rk → entry M 1 (M.length - 1) = 0 →
    ¬ T0Easy M (M.length - 1) → UpgAbsX M (M.length - 1) ρ

theorem hDropV2_of (hD : HDropV2W) (h0 : T0UpgAbsV2) : HDropV2 := fun M ρ rk hM hS hE I =>
  (hD M ρ rk hM hS hE I).toH (h0 M ρ rk hM hS hE I)

/-- **R-seed**: the seed condition (`hcs` of `t = 1`, `q = r`) of every standard matrix. -/
def HSeedV2 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V2 M ρ rk → SeedR M ρ rk

/-- **R-abs**: the strong absorptions `AbsSR` (`t = 0` and `t = 1`, `q = r = x − 1`) of every standard matrix. -/
def HAbSV2 : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V2 M ρ rk → AbsSR M ρ

/-- **`Res3A` without the strong absorption** (`drop`, `seed`): the context of the steps (2026-10-17). -/
structure Res3AW (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  drop : DropRes M (M.length - 1) ρ (drop1 M (M.length - 1) rk)
  seed : ∀ r, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    lt (sf ((drop1 M (M.length - 1) rk).v r)) (ρ.v r) = true →
    ∀ a', ¬ lt (ρ.v r) a' = true →
    isOT (psi a' (app (qrB M ρ r (M.length - 1)) (psi (succ (ρ.v r)) z z)) z) = true →
    ∀ g ∈ comps a' ((drop1 M (M.length - 1) rk).o r),
      g < app (qrB M ρ r (M.length - 1)) ((drop1 M (M.length - 1) rk).o r)

theorem Res3A.toAW {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (R : Res3A M ρ rk) : Res3AW M ρ rk :=
  ⟨R.drop, R.seed⟩

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
  ∀ M ρ rk, Std M → M ≠ SRO → 2 ≤ M.length → Inv3V2 M ρ rk → Res3AW M ρ rk → TakeResV2 M rk

/-! ## 展開 -/

/-- **What an expansion step knows about `M`**: its invariants and those of all its prefixes, with the drop
valuations and the same ranking. -/
structure StepCtxV2 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop where
  std : Std M
  ne : M ≠ SRO
  S : SInv M
  I : Inv3V2 M ρ rk
  R : Res3AW M ρ rk
  pre : ∀ j, 1 ≤ j → j < M.length →
    Inv3V2 (M.take j) (drop1 M j rk) rk ∧ Res3AW (M.take j) (drop1 M j rk) rk

/-- **The bad shape of the C case at `t = 2`** (2026-10-17): `q = P_0(x) ≠ r`, `q` is not the last counted child of `r`,
and `x − 1` upgrades (to an ancestor of `r`). The seed residual `T2SeedCResR.un` is false here (ext2: 6 standard matrices);
the `t = 2` engines assume its absence (`StepCtxT2`), and the shape is the separate residual `T2CBadOut`. -/
def T2CBad (M : Mat) : Prop :=
  ∃ r L q, r + L + 1 = M.length ∧ par M 2 (r + L) = some r ∧ par M 0 (r + L) = some q ∧ q ≠ r ∧
    (¬ ∃ Lc, CL M r = Lc ++ [q]) ∧ upg M (r + L - 1) ≠ none

/-- **The step context of the `t = 2` engines**: `StepCtxV2` outside the bad C shape. -/
structure StepCtxT2 (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) : Prop extends StepCtxV2 M ρ rk where
  good : ¬ T2CBad M

/-- **R-t0**: the expansions `M[n]` (`n ≥ 2`) with a last column of type `t = 0` have the invariant. -/
def ExpT0V2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (expand M n) ρN rkN

/-- **R-t0, with the descent**: the conclusion that t0's engine `t0_final_inv3V2D` gives (2026-10-17). -/
def ExpT0OutV2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (expand M n) ρN rkN ∧
      isOT (root (expand M n) ρN) = true ∧ root (expand M n) ρN < root M ρ

theorem expT0V2_of_out (h : ExpT0OutV2) : ExpT0V2 := fun M ρ rk C hz hs n hn => by
  obtain ⟨ρN, rkN, IN, _⟩ := h M ρ rk C hz hs n hn
  exact ⟨ρN, rkN, IN⟩

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
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (expand M n) ρN rkN

/-! ## RwClosed を運ぶ形（2026-10-17） -/

/-- **R-t0 with `RwClosed`**: `ExpT0OutV2` and `RwClosed` of the expansion. -/
def ExpT0OutR : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 0 →
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (expand M n) ρN rkN ∧
      isOT (root (expand M n) ρN) = true ∧ root (expand M n) ρN < root M ρ ∧ RwClosed (expand M n) ρN

/-- **R-t1 with `RwClosed`**. -/
def ExpT1OutR : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 →
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (expand M n) ρN rkN ∧
      isOT (root (expand M n) ρN) = true ∧ root (expand M n) ρN < root M ρ ∧ RwClosed (expand M n) ρN

/-- **R-t2 with `RwClosed`**. -/
def ExpT2R : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (expand M n) ρN rkN ∧ RwClosed (expand M n) ρN

/-- **`RwClosed` of a `t = s` expansion with the invariant** (the residual of the carrying, per type `s`). -/
def TRwOut (t : Nat) : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = t →
    ∀ n, 2 ≤ n → ∀ ρN rkN, Inv3V2 (expand M n) ρN rkN → RwClosed (expand M n) ρN

/-- **Residual: the weak closedness `RwClosedL` of every standard matrix with the invariant** (2026-10-17). The
strong `RwClosed` is false on standard matrices (an sv seed frame of an `M[3]`, desc.md); the engines need only the
weak form at the shadow frames (`relR_frameUL`). -/
def HRwClL : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V2 M ρ rk → RwClosedL M ρ

/-- **Residual: the `t = 2` step at the bad C shape** (the output of the `t = 2` engines there). -/
def T2CBadOut : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → T2CBad M → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    (∀ n, 2 ≤ n → ∃ ρN rkN, Inv3V2 (expand M n) ρN rkN) ∧ Res3T2 M ρ rk

/-- `TRwOut 2` in the context of the `t = 2` engines. -/
def TRwOutT2 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ n, 2 ≤ n → ∀ ρN rkN, Inv3V2 (expand M n) ρN rkN → RwClosed (expand M n) ρN

theorem expT0OutR_of (h : ExpT0OutV2) (hR : TRwOut 0) : ExpT0OutR := fun M ρ rk C hz hs n hn => by
  obtain ⟨ρN, rkN, IN, hot, hlt⟩ := h M ρ rk C hz hs n hn
  exact ⟨ρN, rkN, IN, hot, hlt, hR M ρ rk C hz hs n hn ρN rkN IN⟩

theorem expT1OutR_of (h : ExpT1OutV2) (hR : TRwOut 1) : ExpT1OutR := fun M ρ rk C hz hs n hn => by
  obtain ⟨ρN, rkN, IN, hot, hlt⟩ := h M ρ rk C hz hs n hn
  exact ⟨ρN, rkN, IN, hot, hlt, hR M ρ rk C hz hs n hn ρN rkN IN⟩

theorem expT2R_of (h : ExpT2V2) (hR : TRwOutT2) : ExpT2R := fun M ρ rk C hz hs n hn => by
  obtain ⟨ρN, rkN, IN⟩ := h M ρ rk C hz hs n hn
  exact ⟨ρN, rkN, IN, hR M ρ rk C hz hs n hn ρN rkN IN⟩

/-- **R-t2d**: the remaining facts `Res3T2` of the descent at `t = 2`. -/
def R2V2 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    Res3T2 M ρ rk

end Ytosk
