/-
HbW.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。
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

namespace TRIO
namespace HbW

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN GzP GzS GzU GzV GzW GzY HaA HaC HaD HaE HaF HaG HaJ HaL HaN HaP HaR HaS HaT HaV HaZ HbB HbJ HbK

/-- ★ シート行 1577。 -/
theorem R1577_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbV.starOK_CL (v := 0) ([(([unitsC 0 ([some ([(0, 0, 0)] : TrioSeq)] : List (Option TrioSeq))] : List TrioSeq), ([] : List (Option TrioSeq)))] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_cons (HbV.DsOK_cons (HbV.LoadSeq_of (by simp [NoTie]) (RawU_cons_some (show ([(0, 0, 0)] : TrioSeq) ∈ Wg (2 * 0) by have h := Wg_up (w := 2 * 0) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega); simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0] using h) rfl (RawU_nil 0))) (HbV.DsOK_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HbV.PsL_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0] using h

/-- ★ シート行 1578。 -/
theorem R1578_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 0, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbV.starOK_CL (v := 0) ([(([unitsC 0 ([some ([(0, 0, 0)] : TrioSeq)] : List (Option TrioSeq)), unitsC 0 ([] : List (Option TrioSeq))] : List TrioSeq), ([] : List (Option TrioSeq)))] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_cons (HbV.DsOK_cons (HbV.LoadSeq_of (by simp [NoTie]) (RawU_cons_some (show ([(0, 0, 0)] : TrioSeq) ∈ Wg (2 * 0) by have h := Wg_up (w := 2 * 0) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega); simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0] using h) rfl (RawU_nil 0))) (HbV.DsOK_cons (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (HbV.DsOK_nil 0))) (by simp [NoTie]) (RawU_nil 0) (HbV.PsL_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0] using h

/-- ★ シート行 1579。 -/
theorem R1579_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 0, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbV.starOK_CL (v := 0) ([(([unitsC 0 ([some ([(0, 0, 0)] : TrioSeq)] : List (Option TrioSeq)), unitsC 0 ([] : List (Option TrioSeq))] : List TrioSeq), ([] : List (Option TrioSeq))), (([] : List TrioSeq), ([] : List (Option TrioSeq)))] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_cons (HbV.DsOK_cons (HbV.LoadSeq_of (by simp [NoTie]) (RawU_cons_some (show ([(0, 0, 0)] : TrioSeq) ∈ Wg (2 * 0) by have h := Wg_up (w := 2 * 0) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega); simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0] using h) rfl (RawU_nil 0))) (HbV.DsOK_cons (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (HbV.DsOK_nil 0))) (by simp [NoTie]) (RawU_nil 0) (HbV.PsL_cons (HbV.DsOK_nil 0) (by simp [NoTie]) (RawU_nil 0) (HbV.PsL_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0] using h

/-- ★ シート行 1580。 -/
theorem R1580_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 0, 0), (2, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbV.starOK_CL (v := 0) ([(([unitsC 0 ([some ([(0, 0, 0)] : TrioSeq)] : List (Option TrioSeq)), unitsC 0 ([some ([(0, 0, 0)] : TrioSeq)] : List (Option TrioSeq))] : List TrioSeq), ([] : List (Option TrioSeq)))] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_cons (HbV.DsOK_cons (HbV.LoadSeq_of (by simp [NoTie]) (RawU_cons_some (show ([(0, 0, 0)] : TrioSeq) ∈ Wg (2 * 0) by have h := Wg_up (w := 2 * 0) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega); simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0] using h) rfl (RawU_nil 0))) (HbV.DsOK_cons (HbV.LoadSeq_of (by simp [NoTie]) (RawU_cons_some (show ([(0, 0, 0)] : TrioSeq) ∈ Wg (2 * 0) by have h := Wg_up (w := 2 * 0) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega); simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0] using h) rfl (RawU_nil 0))) (HbV.DsOK_nil 0))) (by simp [NoTie]) (RawU_nil 0) (HbV.PsL_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0] using h

/-- ★ シート行 1581。 -/
theorem R1581_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 0, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbV.starOK_CL (v := 0) ([(([unitsC 0 ([some ([(0, 0, 0)] : TrioSeq), some ([(0, 0, 0)] : TrioSeq)] : List (Option TrioSeq))] : List TrioSeq), ([] : List (Option TrioSeq)))] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_cons (HbV.DsOK_cons (HbV.LoadSeq_of (by simp [NoTie]) (RawU_cons_some (show ([(0, 0, 0)] : TrioSeq) ∈ Wg (2 * 0) by have h := Wg_up (w := 2 * 0) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega); simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0] using h) rfl (RawU_cons_some (show ([(0, 0, 0)] : TrioSeq) ∈ Wg (2 * 0) by have h := Wg_up (w := 2 * 0) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega); simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0] using h) rfl (RawU_nil 0)))) (HbV.DsOK_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HbV.PsL_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0] using h

/-- ★ シート行 1582。 -/
theorem R1582_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 0, 0), (4, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbV.starOK_CL (v := 0) ([(([unitsC 0 ([some ([(0, 0, 0), (1, 1, 1)] : TrioSeq)] : List (Option TrioSeq))] : List TrioSeq), ([] : List (Option TrioSeq)))] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_cons (HbV.DsOK_cons (HbV.LoadSeq_of (by simp [NoTie]) (RawU_cons_some (show ([(0, 0, 0), (1, 1, 1)] : TrioSeq) ∈ Wg (2 * 0) by have h := Wg_up (w := 2 * 0) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))) (by omega); simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0] using h) rfl (RawU_nil 0))) (HbV.DsOK_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HbV.PsL_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0] using h

end HbW
end TRIO
