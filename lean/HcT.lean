/-
HcT.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。
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
import HbV
import HbX
import HcG
import HcS

namespace TRIO
namespace HcT

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN GzP GzS GzU GzV GzW GzY HaA HaC HaD HaE HaF HaG HaJ HaL HaN HaP HaR HaS HaT HaV HaZ HbB HbJ HbK

/-- ★ シート行 1615。 -/
theorem R1615_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_nil 0) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1616。 -/
theorem R1616_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_nil 0) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1617。 -/
theorem R1617_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_nil 0) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_nil 0) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0)))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1618。 -/
theorem R1618_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([([] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_nil 0) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1619。 -/
theorem R1619_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([([] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_nil 0) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_nil 0) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0)))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1620。 -/
theorem R1620_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([([some ([(0, 0, 0)] : TrioSeq)] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_some (show ([(0, 0, 0)] : TrioSeq) ∈ Wg (2 * 0) by have h := Wg_up (w := 2 * 0) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega); simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h) rfl (RawU_nil 0)) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1621。 -/
theorem R1621_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1622。 -/
theorem R1622_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1623。 -/
theorem R1623_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_nil 0) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0)))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1624。 -/
theorem R1624_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq)), ([] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_cons (RawU_nil 0) (HcS.RawUs_nil 0))) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1625。 -/
theorem R1625_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq)), ([] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_cons (RawU_nil 0) (HcS.RawUs_nil 0))) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1626。 -/
theorem R1626_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq)), ([] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_cons (RawU_nil 0) (HcS.RawUs_nil 0))) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_nil 0) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1627。 -/
theorem R1627_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq)), ([] : List (Option TrioSeq)), ([] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_cons (RawU_nil 0) (HcS.RawUs_cons (RawU_nil 0) (HcS.RawUs_nil 0)))) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_nil 0) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1628。 -/
theorem R1628_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq)), ([some ([(0, 0, 0)] : TrioSeq)] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_cons (RawU_cons_some (show ([(0, 0, 0)] : TrioSeq) ∈ Wg (2 * 0) by have h := Wg_up (w := 2 * 0) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega); simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h) rfl (RawU_nil 0)) (HcS.RawUs_nil 0))) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1629。 -/
theorem R1629_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq)), ([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0))) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1630。 -/
theorem R1630_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq)), ([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0))) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1631。 -/
theorem R1631_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq)), ([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0))) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_nil 0) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1632。 -/
theorem R1632_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq)), ([none] : List (Option TrioSeq)), ([] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_cons (RawU_nil 0) (HcS.RawUs_nil 0)))) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_nil 0) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1633。 -/
theorem R1633_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none] : List (Option TrioSeq)), ([none] : List (Option TrioSeq)), ([none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_cons (RawU_cons_none (RawU_nil 0)) (HcS.RawUs_nil 0)))) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_nil 0) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1634。 -/
theorem R1634_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none, some ([(0, 0, 0)] : TrioSeq)] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_cons_some (show ([(0, 0, 0)] : TrioSeq) ∈ Wg (2 * 0) by have h := Wg_up (w := 2 * 0) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega); simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h) rfl (RawU_nil 0))) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1635。 -/
theorem R1635_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none, none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_cons_none (RawU_nil 0))) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1636。 -/
theorem R1636_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none, none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_cons_none (RawU_nil 0))) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1637。 -/
theorem R1637_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none, none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_cons_none (RawU_nil 0))) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_nil 0) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1638。 -/
theorem R1638_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none, none] : List (Option TrioSeq)), ([] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_cons_none (RawU_nil 0))) (HcS.RawUs_cons (RawU_nil 0) (HcS.RawUs_nil 0))) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_nil 0) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1639。 -/
theorem R1639_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none, none] : List (Option TrioSeq)), ([none, none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_cons_none (RawU_nil 0))) (HcS.RawUs_cons (RawU_cons_none (RawU_cons_none (RawU_nil 0))) (HcS.RawUs_nil 0))) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_nil 0) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

/-- ★ シート行 1640。 -/
theorem R1640_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HcS.starOK_CLU (v := 0) ([(([([none, none, none] : List (Option TrioSeq))] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq))), (([] : List (List (Option TrioSeq))), ([] : List (Option TrioSeq)))] : List (List (List (Option TrioSeq)) × List (Option TrioSeq))) (HcS.PsLU_cons (HcS.RawUs_cons (RawU_cons_none (RawU_cons_none (RawU_cons_none (RawU_nil 0)))) (HcS.RawUs_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_cons (HcS.RawUs_nil 0) (by simp [NoTie]) (RawU_nil 0) (HcS.PsLU_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU] using h

end HcT
end TRIO
