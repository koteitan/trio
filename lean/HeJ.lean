/-
HeJ.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。
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
import HeI

namespace TRIO
namespace HeJ

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN GzP GzS GzU GzV GzW GzY HaA HaC HaD HaE HaF HaG HaJ HaL HaN HaP HaR HaS HaT HaV HaZ HbB HbJ HbK

/-- ★ シート行 1654。 -/
theorem R1654_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HdV.starOK_N2 (v := 0) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_nil 0) (Uss := ([] : List (List HdA.UT))) (HdV.RawssT_nil 0) (us := ([] : List HdA.UT)) (HdV.TRaws_nil 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (HdH.PVF_farWAt (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HdH.OkWsAt_cons le_rfl (HeI.GoodChtX_snocT (A0 := []) (o := 1) (by decide) (by decide) (by decide) (HdE.GoodChtX_nil [] 1 (fun _ => 0) 0) (HeI.TreeOKs_cons_up (l := 0) rfl (by decide) (HeI.TreeOKs_nil 0 1 false) (HeI.TreeOKs_nil 0 0 true))) (HdH.okRAt_nil [] 1 0) (HdH.OkWsAt_nil [] 1 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT] using h

/-- ★ シート行 1655。 -/
theorem R1655_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 3, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HdV.starOK_N2 (v := 0) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_nil 0) (Uss := ([] : List (List HdA.UT))) (HdV.RawssT_nil 0) (us := ([] : List HdA.UT)) (HdV.TRaws_nil 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (HdH.PVF_farWAt (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HdH.OkWsAt_cons le_rfl (HeI.GoodChtX_snocT (A0 := []) (o := 1) (by decide) (by decide) (by decide) (HdE.GoodChtX_nil [] 1 (fun _ => 0) 0) (HeI.TreeOKs_cons_up (l := 0) rfl (by decide) (HeI.TreeOKs_nil 0 1 false) (HeI.TreeOKs_nil 0 0 true))) (HdH.okRAt_nil [] 1 0) (HdH.OkWsAt_nil [] 1 0)))) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT] using h

/-- ★ シート行 1656。 -/
theorem R1656_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 3, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 3, 0), (6, 3, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HdV.starOK_N2 (v := 0) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_nil 0) (Uss := ([] : List (List HdA.UT))) (HdV.RawssT_nil 0) (us := ([] : List HdA.UT)) (HdV.TRaws_nil 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (HdH.PVF_farWAt (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HdH.OkWsAt_cons le_rfl (HeI.GoodChtX_snocT (A0 := []) (o := 1) (by decide) (by decide) (by decide) (HdE.GoodChtX_nil [] 1 (fun _ => 0) 0) (HeI.TreeOKs_cons_up (l := 0) rfl (by decide) (HeI.TreeOKs_nil 0 1 false) (HeI.TreeOKs_nil 0 0 true))) (HdH.okRAt_nil [] 1 0) (HdH.OkWsAt_nil [] 1 0)))) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [] (by decide) (GPF_of_PVF (HcP.PVF_farWAu (A0 := []) (o := 2) (by decide) (by decide) (by decide) 0 _ (HcP.OkWsAu_cons le_rfl (HcP.GoodChuX_snocU (A0 := []) (o := 2) (by decide) (by decide) (by decide) (HcM.GoodChuX_nil [] 2 (fun _ => 0) 0) (HcP.GoodLow_none (HcN.GoodLow_nil 0))) (HcP.okRAu_nil [] 2 0) (HcP.OkWsAu_nil [] 2 0)))) (GPF_nil (A := []) (o := 3) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT] using h

/-- ★ シート行 1657。 -/
theorem R1657_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 3, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HdV.starOK_N2 (v := 0) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_nil 0) (Uss := ([] : List (List HdA.UT))) (HdV.RawssT_nil 0) (us := ([] : List HdA.UT)) (HdV.TRaws_nil 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (HdH.PVF_farWAt (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HdH.OkWsAt_cons le_rfl (HeI.GoodChtX_snocT (A0 := []) (o := 1) (by decide) (by decide) (by decide) (HdE.GoodChtX_nil [] 1 (fun _ => 0) 0) (HeI.TreeOKs_cons_up (l := 0) rfl (by decide) (HeI.TreeOKs_nil 0 1 false) (HeI.TreeOKs_nil 0 0 true))) (HdH.okRAt_nil [] 1 0) (HdH.OkWsAt_nil [] 1 0))) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT] using h

/-- ★ シート行 1658。 -/
theorem R1658_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 3, 0), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (6, 3, 0), (7, 4, 0), (5, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HdV.starOK_N2 (v := 0) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_nil 0) (Uss := ([] : List (List HdA.UT))) (HdV.RawssT_nil 0) (us := ([] : List HdA.UT)) (HdV.TRaws_nil 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (HdH.PVF_farWAt (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HdH.OkWsAt_cons le_rfl (HeI.GoodChtX_snocT (A0 := []) (o := 1) (by decide) (by decide) (by decide) (HdE.GoodChtX_nil [] 1 (fun _ => 0) 0) (HeI.TreeOKs_cons_up (l := 0) rfl (by decide) (HeI.TreeOKs_nil 0 1 false) (HeI.TreeOKs_nil 0 0 true))) (HdH.okRAt_nil [] 1 0) (HdH.OkWsAt_nil [] 1 0))) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [1]) (o := 2) (by decide) (HdH.PVF_farWAt (A0 := [1]) (o := 2) (by decide) (by decide) (by decide) 0 _ (HdH.OkWsAt_cons le_rfl (HeI.GoodChtX_snocT (A0 := [1]) (o := 2) (by decide) (by decide) (by decide) (HdE.GoodChtX_nil [1] 2 (fun _ => 0) 0) (HeI.TreeOKs_cons_up (l := 0) rfl (by decide) (HeI.TreeOKs_nil 0 1 false) (HeI.TreeOKs_nil 0 0 true))) (HdH.okRAt_nil [1] 2 0) (HdH.OkWsAt_nil [1] 2 0))) (RLF_nil (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT] using h

end HeJ
end TRIO
