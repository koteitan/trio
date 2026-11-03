/-
The repaired t = 0 absorption input, matching the widened t = 2 boundary.

This first layer packages AbsWNxU together with the upgrade-closed bad-column
condition used by the t = 0 dependency engine.
-/
import Ytosk.V3T0D
import Ytosk.V3AbsUpgShape

namespace Ytosk

open T Ytosk.WfT2X

set_option linter.unusedSectionVars false

/-- The t = 0 absorption input with the widened bad-shape alternatives. -/
def T0AbsWU (M : Mat) (r L : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
    AbsWNxU M (TRIO.gexp M r L 0 0 n) r ρ σ ∧
      NotBumpKidXU M (TRIO.gexp M r L 0 0 n) r ρ σ

/-- The old strong t = 0 input implies the widened one. -/
theorem T0AbsW.toU {M : Mat} {r L : Nat} {ρ : Valn} (h : T0AbsW M r L ρ) :
    T0AbsWU M r L ρ := by
  intro n hn σ hCN
  have hAbs := h n hn σ hCN
  exact ⟨AbsWNx.toU (WfAbsW.AbsWN.toX hAbs),
    notBumpKidXU_of (NotBumpKidX.of_absWN hAbs)⟩

end Ytosk
