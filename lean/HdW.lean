/-
HdW.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。
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
import HdV

namespace TRIO
namespace HdW

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN GzP GzS GzU GzV GzW GzY HaA HaC HaD HaE HaF HaG HaJ HaL HaN HaP HaR HaS HaT HaV HaZ HbB HbJ HbK

/-- ★ シート行 1641。 -/
theorem R1641_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HdS.starOK_CLT (v := 0) ([(([([HdA.UT.tie 0 ([HdA.UT.ch ([(0, 0, 0)] : TrioSeq)] : List HdA.UT)] : List HdA.UT)] : List (List HdA.UT)), ([] : List (Option TrioSeq)))] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_cons (HdV.RawssT_cons (HdV.TRaws_cons_tie (HdV.TRaws_cons_ch (show ([(0, 0, 0)] : TrioSeq) ∈ Wg (2 * 0) by have h := Wg_up (w := 2 * 0) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega); simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT] using h) rfl (HdV.TRaws_nil 0)) (HdV.TRaws_nil 0)) (HdV.RawssT_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HdQ.PsLT_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT] using h

/-- ★ シート行 1642。 -/
theorem R1642_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HdS.starOK_CLT (v := 0) ([(([([HdA.UT.tie 0 ([HdA.UT.tie 0 ([] : List HdA.UT)] : List HdA.UT)] : List HdA.UT)] : List (List HdA.UT)), ([] : List (Option TrioSeq)))] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_cons (HdV.RawssT_cons (HdV.TRaws_cons_tie (HdV.TRaws_cons_tie (HdV.TRaws_nil 0) (HdV.TRaws_nil 0)) (HdV.TRaws_nil 0)) (HdV.RawssT_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HdQ.PsLT_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT] using h

/-- ★ シート行 1643。 -/
theorem R1643_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HdS.starOK_CLT (v := 0) ([(([([HdA.UT.tie 0 ([HdA.UT.tie 0 ([] : List HdA.UT)] : List HdA.UT)] : List HdA.UT)] : List (List HdA.UT)), ([] : List (Option TrioSeq)))] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_cons (HdV.RawssT_cons (HdV.TRaws_cons_tie (HdV.TRaws_cons_tie (HdV.TRaws_nil 0) (HdV.TRaws_nil 0)) (HdV.TRaws_nil 0)) (HdV.RawssT_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HdQ.PsLT_nil 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT] using h

/-- ★ シート行 1644。 -/
theorem R1644_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HdS.starOK_CLT (v := 0) ([(([([HdA.UT.tie 0 ([HdA.UT.tie 0 ([] : List HdA.UT)] : List HdA.UT)] : List HdA.UT)] : List (List HdA.UT)), ([] : List (Option TrioSeq))), (([] : List (List HdA.UT)), ([] : List (Option TrioSeq)))] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_cons (HdV.RawssT_cons (HdV.TRaws_cons_tie (HdV.TRaws_cons_tie (HdV.TRaws_nil 0) (HdV.TRaws_nil 0)) (HdV.TRaws_nil 0)) (HdV.RawssT_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HdQ.PsLT_cons (HdV.RawssT_nil 0) (by simp [NoTie]) (RawU_nil 0) (HdQ.PsLT_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT] using h

/-- ★ シート行 1645。 -/
theorem R1645_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (4, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HdS.starOK_CLT (v := 0) ([(([([HdA.UT.tie 0 ([HdA.UT.tie 0 ([] : List HdA.UT), HdA.UT.tie 0 ([] : List HdA.UT)] : List HdA.UT)] : List HdA.UT)] : List (List HdA.UT)), ([] : List (Option TrioSeq))), (([] : List (List HdA.UT)), ([] : List (Option TrioSeq)))] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_cons (HdV.RawssT_cons (HdV.TRaws_cons_tie (HdV.TRaws_cons_tie (HdV.TRaws_nil 0) (HdV.TRaws_cons_tie (HdV.TRaws_nil 0) (HdV.TRaws_nil 0))) (HdV.TRaws_nil 0)) (HdV.RawssT_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HdQ.PsLT_cons (HdV.RawssT_nil 0) (by simp [NoTie]) (RawU_nil 0) (HdQ.PsLT_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT] using h

/-- ★ シート行 1646。 -/
theorem R1646_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (5, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HdS.starOK_CLT (v := 0) ([(([([HdA.UT.tie 0 ([HdA.UT.tie 0 ([HdA.UT.tie 0 ([] : List HdA.UT)] : List HdA.UT)] : List HdA.UT)] : List HdA.UT)] : List (List HdA.UT)), ([] : List (Option TrioSeq))), (([] : List (List HdA.UT)), ([] : List (Option TrioSeq)))] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_cons (HdV.RawssT_cons (HdV.TRaws_cons_tie (HdV.TRaws_cons_tie (HdV.TRaws_cons_tie (HdV.TRaws_nil 0) (HdV.TRaws_nil 0)) (HdV.TRaws_nil 0)) (HdV.TRaws_nil 0)) (HdV.RawssT_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HdQ.PsLT_cons (HdV.RawssT_nil 0) (by simp [NoTie]) (RawU_nil 0) (HdQ.PsLT_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT] using h

/-- ★ シート行 1647。 -/
theorem R1647_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HdV.starOK_N2 (v := 0) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_nil 0) (Uss := ([] : List (List HdA.UT))) (HdV.RawssT_nil 0) (us := ([] : List HdA.UT)) (HdV.TRaws_nil 0) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT] using h

/-- ★ シート行 1649。 -/
theorem R1649_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (HdV.starOK_N2 (v := 0) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_nil 0) (Uss := ([] : List (List HdA.UT))) (HdV.RawssT_nil 0) (us := ([] : List HdA.UT)) (HdV.TRaws_nil 0) (WordsG_nil 0)) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT] using h

/-- ★ シート行 1650。 -/
theorem R1650_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 0), (2, 2, 1), (3, 2, 1), (3, 2, 0), (4, 3, 0), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (HdV.starOK_N2 (v := 0) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_nil 0) (Uss := ([] : List (List HdA.UT))) (HdV.RawssT_nil 0) (us := ([] : List HdA.UT)) (HdV.TRaws_nil 0) (WordsG_nil 0)) (Wg_of_starOK (starOK_hang (HdV.starOK_N2 (v := 1) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_nil 1) (Uss := ([] : List (List HdA.UT))) (HdV.RawssT_nil 1) (us := ([] : List HdA.UT)) (HdV.TRaws_nil 1) (WordsG_nil 1)) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT] using h

/-- ★ シート行 1651。 -/
theorem R1651_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HdV.starOK_N2 (v := 0) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_nil 0) (Uss := ([] : List (List HdA.UT))) (HdV.RawssT_nil 0) (us := ([] : List HdA.UT)) (HdV.TRaws_nil 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT] using h

/-- ★ シート行 1652。 -/
theorem R1652_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HdV.starOK_N2 (v := 0) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_nil 0) (Uss := ([] : List (List HdA.UT))) (HdV.RawssT_nil 0) (us := ([] : List HdA.UT)) (HdV.TRaws_nil 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_nil1 0) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT] using h

/-- ★ シート行 1653。 -/
theorem R1653_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HdV.starOK_N2 (v := 0) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_nil 0) (Uss := ([] : List (List HdA.UT))) (HdV.RawssT_nil 0) (us := ([] : List HdA.UT)) (HdV.TRaws_nil 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farU (A := []) (o := 1) (by decide) (by decide) (by decide) 0 ([([] : List (Option TrioSeq))] : List (List (Option TrioSeq))) (RawUs_cons (RawU_nil 0) (RawUs_nil 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT] using h

end HdW
end TRIO
