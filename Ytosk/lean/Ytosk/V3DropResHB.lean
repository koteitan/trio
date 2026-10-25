/-
**落とす補題の仮定の形 B（DropResHB）と、その残り HDropU（2026-10-25、V3GlobV2 から移した）。**

t = 2 のエンジンの束 Res3W や文脈 StepCtxV2 からも使えるように、前のファイルに置く。
-/
import Ytosk.V3BumpDropB
import Ytosk.V3Inv2

namespace Ytosk

open T

/-- **The hypotheses of the drop lemma in the `Bad2` form with `HardArg`** (2026-10-25). -/
structure DropResHB (N : Mat) (x : Nat) (σ σ' : Valn) : Prop where
  hard : HardArg N x σ σ'
  vst : VSmallNew N x σ σ'
  ws : BumpWeakSrcB N x σ σ'
  ua : ∀ i k W, i + 1 = x → upg N i = some k → σ.v k = add (vOpt σ (par N 1 i)) W → W ≠ z →
    (∀ r ∈ summands (vOpt σ (par N 1 i)), r < W → Lhd z r W) ∨
      (WCSP N σ i (add (vOpt σ (par N 1 i)) one) ∧
        (∀ g ∈ comps z (add (vOpt σ (par N 1 i)) one), g < psi (add (vOpt σ (par N 1 i)) one) z z))
  ab : BumpAbsCB N x σ

/-- **Residual: the drop hypotheses of every standard matrix** (2026-10-25): the `Bad2` form `DropResHB` everywhere,
and `BumpAbsC` outside `Bad2`. Measured on the 11 sets and the grafted sets with no exception (desc). It replaces
`HDropV2W` (outside `Bad2`) and the drop part of `DropBadV2B` (on `Bad2`). -/
def HDropU : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3V2 M ρ rk →
    DropResHB M (M.length - 1) ρ (drop1 M (M.length - 1) rk) ∧
      (¬ Bad2 M ∨ entry M 1 (M.length - 1) = 0 → BumpAbsC M (M.length - 1) ρ)

end Ytosk
