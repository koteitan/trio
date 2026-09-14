/-
HaQ.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。
-/
import GzJ
import GzS
import HaJ
import HaL
import HaP

namespace TRIO
namespace HaQ

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN GzP GzS GzU GzV GzW GzY HaA HaC HaD HaE HaF HaG HaJ HaL HaN HaP

/-- ★ シート行 1501。 -/
theorem R1501_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_tieFarFlat 0 (v := 0) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate] using h

end HaQ
end TRIO
