/-
GzL.lean: tools/gen_given.py が生成。シートの行の間の行列。
-/
import GzJ
import GzN

namespace TRIO
namespace GzL

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN

/-- ★ (0,0,0)(1,1,1)(2,1,1)(2,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(4,1,0)(4,1,0)(4,1,0) -/
theorem Q1_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 1, 0), (4, 1, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farU (A := []) (o := 1) (by decide) (by decide) (by decide) 0 ([([none, none, none] : List (Option TrioSeq))] : List (List (Option TrioSeq))) (RawUs_cons (RawU_cons_none (RawU_cons_none (RawU_cons_none (RawU_nil 0)))) (RawUs_nil 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

/-- ★ (0,0,0)(1,1,1)(2,1,1)(2,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(4,1,0)(4,1,0)(4,1,0)(4,1,0) -/
theorem Q2_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 1, 0), (4, 1, 0), (4, 1, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farU (A := []) (o := 1) (by decide) (by decide) (by decide) 0 ([([none, none, none, none] : List (Option TrioSeq))] : List (List (Option TrioSeq))) (RawUs_cons (RawU_cons_none (RawU_cons_none (RawU_cons_none (RawU_cons_none (RawU_nil 0))))) (RawUs_nil 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

/-- ★ (0,0,0)(1,1,1)(2,1,1)(2,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(4,1,0)(5,0,0)(6,1,1)(7,1,1)(7,1,0)(6,1,1)(7,1,0)(8,2,1)(9,2,1)(9,1,0) -/
theorem Q3_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 1, 0), (5, 0, 0), (6, 1, 1), (7, 1, 1), (7, 1, 0), (6, 1, 1), (7, 1, 0), (8, 2, 1), (9, 2, 1), (9, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farWs (A := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWs_cons le_rfl (okWF_tie (okWF_nil 0) (GF_of_GPF (GPF_load (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (GPF_nil1 0) (Wg_up (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farU (A := []) (o := 1) (by decide) (by decide) (by decide) 0 ([([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))) (RawUs_cons (RawU_cons_none (RawU_nil 0)) (RawUs_nil 0)))))) (WordsG_nil 0)))) (by omega)) rfl))) (OkWs_nil 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

/-- ★ (0,0,0)(1,1,1)(2,1,1)(2,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(4,1,0)(5,1,0) -/
theorem Q4_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 1, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farWs (A := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWs_cons le_rfl (okWF_tie (okWF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 1) [] (by decide) (GPF_nil1 0) (GPF_nil1 0)))) (OkWs_nil 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

end GzL
end TRIO
