/-
GzX.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。
-/
import GzJ
import GzS
import GzW

namespace TRIO
namespace GzX

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN GzP GzS GzU GzV GzW

/-- ★ シート行 1463。 -/
theorem R1463_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 2, 0), (4, 3, 1), (5, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_farW_bot2A (A := []) (o := 1) (by decide) (by decide) (by decide) le_rfl (OkWs_nil 0) (okWF_nil 0)) (GPF_of_PVF (PVF_farWsk (A := []) (o := 2) (by decide) (by decide) (by decide) (by decide) (by decide) 0 _ (OkWsk_cons le_rfl (okWkF_node (k := 2) (τ := 2) (by decide) (by decide) (okWkF_nil 2 0) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)) (OkWsk_cons le_rfl (okWkF_nil 2 0) (OkWsk_nil 2 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

/-- ★ シート行 1464。 -/
theorem R1464_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 2, 0), (4, 3, 1), (5, 3, 1), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_farW_bot2A (A := []) (o := 1) (by decide) (by decide) (by decide) le_rfl (OkWs_nil 0) (okWF_nil 0)) (GPF_of_PVF (PVF_farWsk (A := []) (o := 2) (by decide) (by decide) (by decide) (by decide) (by decide) 0 _ (OkWsk_cons le_rfl (okWkF_node (k := 2) (τ := 2) (by decide) (by decide) (okWkF_nil 2 0) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)) (OkWsk_cons le_rfl (okWkF_node (k := 2) (τ := 2) (by decide) (by decide) (okWkF_nil 2 0) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)) (OkWsk_nil 2 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

/-- ★ シート行 1465。 -/
theorem R1465_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 2, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_farW_bot2A (A := []) (o := 1) (by decide) (by decide) (by decide) le_rfl (OkWs_nil 0) (okWF_nil 0)) (GPF_of_PVF (PVF_farWsk (A := []) (o := 2) (by decide) (by decide) (by decide) (by decide) (by decide) 0 _ (OkWsk_cons le_rfl (okWkF_node (k := 2) (τ := 2) (by decide) (by decide) (okWkF_node (k := 2) (τ := 2) (by decide) (by decide) (okWkF_nil 2 0) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)) (OkWsk_nil 2 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

/-- ★ シート行 1466。 -/
theorem R1466_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 2, 0), (6, 3, 1), (7, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_farW_bot2A (A := []) (o := 1) (by decide) (by decide) (by decide) le_rfl (OkWs_nil 0) (okWF_nil 0)) (GPF_of_PVF (PVF_farWsk (A := []) (o := 2) (by decide) (by decide) (by decide) (by decide) (by decide) 0 _ (OkWsk_cons le_rfl (okWkF_node (k := 2) (τ := 2) (by decide) (by decide) (okWkF_nil 2 0) (GPF_of_PVF (PVF_farU (A := []) (o := 2) (by decide) (by decide) (by decide) 0 ([([] : List (Option TrioSeq))] : List (List (Option TrioSeq))) (RawUs_cons (RawU_nil 0) (RawUs_nil 0))))) (OkWsk_nil 2 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

end GzX
end TRIO
