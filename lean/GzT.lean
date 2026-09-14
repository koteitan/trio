/-
GzT.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。
-/
import GzJ
import GzS

namespace TRIO
namespace GzT

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN GzP GzS

/-- ★ シート行 1462。 -/
theorem R1462_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 2, 0), (4, 3, 1), (5, 3, 0), (6, 4, 1), (7, 4, 1), (7, 2, 0), (6, 4, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_farW_bot2A (A := []) (o := 1) (by decide) (by decide) (by decide) le_rfl (OkWs_nil 0) (okWF_nil 0)) (GPF_of_PVF (PVF_snoc (A := []) (o := 2) (by decide) (PVF_farW_bot2A (A := []) (o := 2) (by decide) (by decide) (by decide) le_rfl (OkWs_nil 0) (okWF_nil 0)) (RLF_child (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [2] (by decide) (by decide) (RLF_nil (A := []) (o := 2) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [2]) (o := 3) (by decide) (PVF_farW_bot2A (A := [2]) (o := 3) (by decide) (by decide) (by decide) le_rfl (OkWs_nil 0) (okWF_nil 0)) (RLF_nil (A := [2]) (o := 3) (by decide) (by decide) (by decide) 0))))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

end GzT
end TRIO
