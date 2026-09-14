/-
HcQ.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。
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
import HcP

namespace TRIO
namespace HcQ

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN GzP GzS GzU GzV GzW GzY HaA HaC HaD HaE HaF HaG HaJ HaL HaN HaP HaR HaS HaT HaV HaZ HbB HbJ HbK

/-- ★ シート行 1607。 -/
theorem R1607_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (HcP.PVF_farWAu (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcP.OkWsAu_cons le_rfl (HcP.GoodChuX_snocU (A0 := []) (o := 1) (by decide) (by decide) (by decide) (HcM.GoodChuX_nil [] 1 (fun _ => 0) 0) (HcP.GoodLow_none (HcN.GoodLow_nil 0))) (HcP.okRAu_nil [] 1 0) (HcP.OkWsAu_nil [] 1 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF] using h

/-- ★ シート行 1612。 -/
theorem R1612_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (HcP.PVF_farWAu (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcP.OkWsAu_cons le_rfl (HcP.GoodChuX_snocU (A0 := []) (o := 1) (by decide) (by decide) (by decide) (HcM.GoodChuX_nil [] 1 (fun _ => 0) 0) (HcP.GoodLow_none (HcN.GoodLow_nil 0))) (HcP.okRAu_nil [] 1 0) (HcP.OkWsAu_nil [] 1 0))) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF] using h

/-- ★ シート行 1613。 -/
theorem R1613_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 2, 0), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (6, 3, 0), (7, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (HcP.PVF_farWAu (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcP.OkWsAu_cons le_rfl (HcP.GoodChuX_snocU (A0 := []) (o := 1) (by decide) (by decide) (by decide) (HcM.GoodChuX_nil [] 1 (fun _ => 0) 0) (HcP.GoodLow_none (HcN.GoodLow_nil 0))) (HcP.okRAu_nil [] 1 0) (HcP.OkWsAu_nil [] 1 0))) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (HcP.PVF_farWAu (A0 := [1]) (o := 2) (by decide) (by decide) (by decide) 0 _ (HcP.OkWsAu_cons le_rfl (HcP.GoodChuX_snocU (A0 := [1]) (o := 2) (by decide) (by decide) (by decide) (HcM.GoodChuX_nil [1] 2 (fun _ => 0) 0) (HcP.GoodLow_none (HcN.GoodLow_nil 0))) (HcP.okRAu_nil [1] 2 0) (HcP.OkWsAu_nil [1] 2 0))))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF] using h

/-- ★ シート行 1614。 -/
theorem R1614_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 2, 0), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (6, 3, 0), (7, 3, 0), (5, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (HcP.PVF_farWAu (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcP.OkWsAu_cons le_rfl (HcP.GoodChuX_snocU (A0 := []) (o := 1) (by decide) (by decide) (by decide) (HcM.GoodChuX_nil [] 1 (fun _ => 0) 0) (HcP.GoodLow_none (HcN.GoodLow_nil 0))) (HcP.okRAu_nil [] 1 0) (HcP.OkWsAu_nil [] 1 0))) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [1]) (o := 2) (by decide) (HcP.PVF_farWAu (A0 := [1]) (o := 2) (by decide) (by decide) (by decide) 0 _ (HcP.OkWsAu_cons le_rfl (HcP.GoodChuX_snocU (A0 := [1]) (o := 2) (by decide) (by decide) (by decide) (HcM.GoodChuX_nil [1] 2 (fun _ => 0) 0) (HcP.GoodLow_none (HcN.GoodLow_nil 0))) (HcP.okRAu_nil [1] 2 0) (HcP.OkWsAu_nil [1] 2 0))) (RLF_nil (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF] using h

end HcQ
end TRIO
