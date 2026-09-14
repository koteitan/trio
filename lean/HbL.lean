/-
HbL.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。
-/
import GzJ
import GzS
import HaJ
import HaL
import HaP
import HaT
import HaV
import HaZ
import HbB
import HbK

namespace TRIO
namespace HbL

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN GzP GzS GzU GzV GzW GzY HaA HaC HaD HaE HaF HaG HaJ HaL HaN HaP HaR HaS HaT HaV HaZ HbB HbJ HbK

/-- ★ シート行 1525。 -/
theorem R1525_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(1, ([some ([(0, 0, 0)] : TrioSeq)] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 1) (by simp [NoTie]) (RawU_cons_some (show ([(0, 0, 0)] : TrioSeq) ∈ Wg (2 * 0) by have h := Wg_up (w := 2 * 0) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega); simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h) rfl (RawU_nil 0)) (PsOK_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1526。 -/
theorem R1526_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1527。 -/
theorem R1527_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 1), (3, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_nil 0)) (Wg_of_starOK (starOK_CN (v := 1) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 1) (PsOK_nil 1)) (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1528。 -/
theorem R1528_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1529。 -/
theorem R1529_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farU (A := []) (o := 1) (by decide) (by decide) (by decide) 0 ([([] : List (Option TrioSeq))] : List (List (Option TrioSeq))) (RawUs_cons (RawU_nil 0) (RawUs_nil 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1530。 -/
theorem R1530_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_QFn 1 (A := []) (o := 1) (by decide) (by decide) (by decide) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1531。 -/
theorem R1531_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_node (A0 := []) (o := 1) (τ := 1) (by decide) (by decide) (by decide) (by decide) [] (by decide) (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 1 0) (GPF_nil1 0)) (OkWsAn_nil [] 1 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1532。 -/
theorem R1532_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_node (A0 := []) (o := 1) (τ := 1) (by decide) (by decide) (by decide) (by decide) [] (by decide) (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 1 0) (GPF_nil1 0)) (OkWsAn_nil [] 1 0)))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1533。 -/
theorem R1533_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_node (A0 := []) (o := 1) (τ := 1) (by decide) (by decide) (by decide) (by decide) [] (by decide) (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 1 0) (GPF_nil1 0)) (OkWsAn_nil [] 1 0)))) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1534。 -/
theorem R1534_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_node (A0 := []) (o := 1) (τ := 1) (by decide) (by decide) (by decide) (by decide) [] (by decide) (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 1 0) (GPF_nil1 0)) (OkWsAn_nil [] 1 0))) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1535。 -/
theorem R1535_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 1, 0), (3, 2, 1), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_node (A0 := []) (o := 1) (τ := 1) (by decide) (by decide) (by decide) (by decide) [] (by decide) (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 1 0) (GPF_nil1 0)) (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 0 0) (OkWsAn_nil [] 1 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1536。 -/
theorem R1536_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_node (A0 := []) (o := 1) (τ := 1) (by decide) (by decide) (by decide) (by decide) [] (by decide) (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 1 0) (GPF_nil1 0)) (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 1 0) (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 0 0) (OkWsAn_nil [] 1 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1537。 -/
theorem R1537_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_node (A0 := []) (o := 1) (τ := 1) (by decide) (by decide) (by decide) (by decide) [] (by decide) (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 1 0) (GPF_nil1 0)) (OkWsAn_cons le_rfl (okRAn_node (A0 := []) (o := 1) (τ := 1) (by decide) (by decide) (by decide) (by decide) [] (by decide) (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 1 0) (GPF_nil1 0)) (OkWsAn_nil [] 1 0))))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1538。 -/
theorem R1538_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 1, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_node (A0 := []) (o := 1) (τ := 1) (by decide) (by decide) (by decide) (by decide) [] (by decide) (okRAn_node (A0 := []) (o := 1) (τ := 1) (by decide) (by decide) (by decide) (by decide) [] (by decide) (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 1 0) (GPF_nil1 0)) (GPF_nil1 0)) (OkWsAn_nil [] 1 0)))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1539。 -/
theorem R1539_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 1, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_node (A0 := []) (o := 1) (τ := 1) (by decide) (by decide) (by decide) (by decide) [] (by decide) (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 1 0) (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_nil1 0) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0))) (OkWsAn_nil [] 1 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1540。 -/
theorem R1540_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 1, 0), (5, 2, 1), (6, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_node (A0 := []) (o := 1) (τ := 1) (by decide) (by decide) (by decide) (by decide) [] (by decide) (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 1 0) (GPF_of_PVF (PVF_farU (A := []) (o := 1) (by decide) (by decide) (by decide) 0 ([([] : List (Option TrioSeq))] : List (List (Option TrioSeq))) (RawUs_cons (RawU_nil 0) (RawUs_nil 0))))) (OkWsAn_nil [] 1 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1541。 -/
theorem R1541_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 2 0) (OkWsAn_nil [] 1 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1542。 -/
theorem R1542_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 2 0) (OkWsAn_nil [] 1 0)))) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1543。 -/
theorem R1543_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 2 0) (OkWsAn_nil [] 1 0)))) (GPF_of_PVF (PVF_farU (A := []) (o := 2) (by decide) (by decide) (by decide) 0 ([([] : List (Option TrioSeq))] : List (List (Option TrioSeq))) (RawUs_cons (RawU_nil 0) (RawUs_nil 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1544。 -/
theorem R1544_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 3, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 2 0) (OkWsAn_nil [] 1 0)))) (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 2) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_node (A0 := []) (o := 2) (τ := 2) (by decide) (by decide) (by decide) (by decide) [] (by decide) (okRAn_nil (A0 := []) (o := 2) (by decide) (by decide) 1 0) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)) (OkWsAn_nil [] 2 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1545。 -/
theorem R1545_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 3, 0), (5, 2, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 2 0) (OkWsAn_nil [] 1 0)))) (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 2) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_node (A0 := []) (o := 2) (τ := 2) (by decide) (by decide) (by decide) (by decide) [] (by decide) (okRAn_node (A0 := []) (o := 2) (τ := 2) (by decide) (by decide) (by decide) (by decide) [] (by decide) (okRAn_nil (A0 := []) (o := 2) (by decide) (by decide) 1 0) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)) (OkWsAn_nil [] 2 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1546。 -/
theorem R1546_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 3, 0), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 2 0) (OkWsAn_nil [] 1 0)))) (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 2) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 2) (by decide) (by decide) 2 0) (OkWsAn_nil [] 2 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1547。 -/
theorem R1547_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 3, 0), (5, 3, 0), (4, 3, 0), (5, 4, 1), (6, 4, 1), (6, 4, 0), (6, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 2 0) (OkWsAn_nil [] 1 0)))) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [] (by decide) (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 2) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 2) (by decide) (by decide) 2 0) (OkWsAn_nil [] 2 0)))) (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 3) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 3) (by decide) (by decide) 2 0) (OkWsAn_nil [] 3 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1548。 -/
theorem R1548_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 2 0) (OkWsAn_nil [] 1 0))) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1549。 -/
theorem R1549_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (6, 3, 0), (6, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 2 0) (OkWsAn_nil [] 1 0))) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_farWAn (A0 := [1]) (o := 2) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := [1]) (o := 2) (by decide) (by decide) 2 0) (OkWsAn_nil [1] 2 0))))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1550。 -/
theorem R1550_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (6, 3, 0), (6, 3, 0), (5, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 2 0) (OkWsAn_nil [] 1 0))) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [1]) (o := 2) (by decide) (PVF_farWAn (A0 := [1]) (o := 2) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := [1]) (o := 2) (by decide) (by decide) 2 0) (OkWsAn_nil [1] 2 0))) (RLF_nil (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1551。 -/
theorem R1551_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1552。 -/
theorem R1552_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1553。 -/
theorem R1553_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 2 0) (OkWsAn_nil [] 1 0))) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_nil (A := [1]) (o := 2) (by decide) (by decide) 0))) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1554。 -/
theorem R1554_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1555。 -/
theorem R1555_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq))), (1, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 1) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1556。 -/
theorem R1556_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq))), (1, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 1) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1557。 -/
theorem R1557_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq))), (1, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 1) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1558。 -/
theorem R1558_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq))), (2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1559。 -/
theorem R1559_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq))), (2, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1560。 -/
theorem R1560_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq))), (2, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1561。 -/
theorem R1561_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([] : List (Option TrioSeq))), (2, ([] : List (Option TrioSeq))), (2, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0))))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1562。 -/
theorem R1562_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(2, ([some ([(0, 0, 0)] : TrioSeq)] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_cons_some (show ([(0, 0, 0)] : TrioSeq) ∈ Wg (2 * 0) by have h := Wg_up (w := 2 * 0) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega); simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h) rfl (RawU_nil 0)) (PsOK_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1563。 -/
theorem R1563_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(3, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 3) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1564。 -/
theorem R1564_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 1), (3, 2, 0), (3, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_CN (v := 0) ([(3, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 3) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_nil 0)) (Wg_of_starOK (starOK_CN (v := 1) ([(3, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 3) (by simp [NoTie]) (RawU_nil 1) (PsOK_nil 1)) (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1565。 -/
theorem R1565_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(3, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 3) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1566。 -/
theorem R1566_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(3, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 3) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 3 0) (OkWsAn_nil [] 1 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1567。 -/
theorem R1567_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (4, 2, 0), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(3, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 3) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farWAn (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (OkWsAn_cons le_rfl (okRAn_nil (A0 := []) (o := 1) (by decide) (by decide) 3 0) (OkWsAn_nil [] 1 0))) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1568。 -/
theorem R1568_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(3, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 3) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1569。 -/
theorem R1569_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(3, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 3) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1570。 -/
theorem R1570_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(3, ([] : List (Option TrioSeq))), (1, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 3) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 1) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1571。 -/
theorem R1571_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(3, ([] : List (Option TrioSeq))), (2, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 3) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 2) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1572。 -/
theorem R1572_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(3, ([] : List (Option TrioSeq))), (3, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 3) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 3) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1573。 -/
theorem R1573_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(4, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 4) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1574。 -/
theorem R1574_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(4, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 4) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1575。 -/
theorem R1575_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(4, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 4) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

/-- ★ シート行 1576。 -/
theorem R1576_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_CN (v := 0) ([(5, ([] : List (Option TrioSeq))), (0, ([] : List (Option TrioSeq)))] : List (ℕ × List (Option TrioSeq))) (PsOK_cons (n := 5) (by simp [NoTie]) (RawU_nil 0) (PsOK_cons (n := 0) (by simp [NoTie]) (RawU_nil 0) (PsOK_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT] using h

end HbL
end TRIO
