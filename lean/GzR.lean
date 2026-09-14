/-
GzR.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。
-/
import GzJ
import GzP

namespace TRIO
namespace GzR

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN GzP

/-- ★ シート行 1459。 -/
theorem R1459_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_farW_bot2 (o := 1) (by decide) le_rfl (OkWs_nil 0) (okWF_nil 0)) (GPF_farW_bot2 (o := 2) (by decide) le_rfl (OkWs_nil 0) (okWF_nil 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

/-- ★ シート行 1460。 -/
theorem R1460_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_farW_bot2 (o := 1) (by decide) le_rfl (OkWs_nil 0) (okWF_nil 0)) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [] (by decide) (GPF_farW_bot2 (o := 2) (by decide) le_rfl (OkWs_nil 0) (okWF_nil 0)) (GPF_nil (A := []) (o := 3) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

end GzR
end TRIO
