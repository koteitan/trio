/-
**難しい枠の残り（t = 0・t = 2 で共通、2026-10-12）。**

N の枠 i（i < bnd）の最後の数える子 c（c < bnd）で、古い値 ρ と新しい値 σ の添字が同じ s、v(i) < s、
両方書き換え、高い部分が下がる（hi(y′) < hi(y)）とき、新しい引数の段 v(i) の成分は H s y′ 以下。
node_ot_hard の仮定 hy そのもの。VSmallR（標準形で偽）と RClaim の代わり。t2 の T2Hard に c < bnd を足した形。
-/
import Ytosk.V3RelR

namespace Ytosk

open T

/-- **The hard-frame residual** shared by `t = 0` and `t = 2`. -/
def HardArgN (N : Mat) (bnd : Nat) (ρ σ : Valn) : Prop :=
  ∀ i (Lc : List Nat) c s y y', i < bnd → c < bnd → CL N i = Lc ++ [c] → ρ.o c = psi s y z →
    σ.o c = psi s y' z → lt (ρ.v i) s = true →
    (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true ∧ lt (psi (ρ.v i) z z) (psi s y' z) = true) →
    (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
    (split y' (psi (succ s) z z)).1 < (split y (psi (succ s) z z)).1 →
    ∀ g ∈ comps (ρ.v i) y', g ≤ H s y'

end Ytosk
