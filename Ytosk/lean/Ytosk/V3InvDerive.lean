/-
**Inv3 の値の欄のうち、Good3 と構造の不変条件から出るもの。**

実測（到達しない行列も含む: 3 行・長さ ≤ 8 で、構造の不変条件を満たし Good3 の 66 万個）:
VSmallF・AbsD・AbsU・TPLo・TPLoW・AbsUW・AbsDW・TPLoN・AbsDN・rootS は例外 0。
FrameOT・FrameClosed・BumpKidsDec・BumpTermDec・TP1・TP1W・TrigOm・rootP は非標準形で崩れる（Good3 だけでは出ない）。
ここでは自明な rootS（根の値は 1 項）から。
-/
import Ytosk.V3Good3N

namespace Ytosk

open T

/-- **Root values are single summands** (from `Cons` and `Good3`). -/
theorem rootS_of_good {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) :
    ∀ i ∈ roots M, Single (ρ.o i) := by
  intro i hi
  have hiM := (mem_roots.mp hi).1
  exact ⟨hG.ot_o i hiM, o_psi_form hC hiM⟩

end Ytosk
