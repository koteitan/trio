/-
HcH.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。
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

namespace TRIO
namespace HcH

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN GzP GzS GzU GzV GzW GzY HaA HaC HaD HaE HaF HaG HaJ HaL HaN HaP HaR HaS HaT HaV HaZ HbB HbJ HbK

/-- ★ シート行 1594。 -/
theorem R1594_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (HcG.PVF_farWAc (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_snoc (HcG.GoodLc_nil 0) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0)))) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_nil [] 1 0)))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc] using h

/-- ★ シート行 1595。 -/
theorem R1595_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (HcG.PVF_farWAc (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_snoc (HcG.GoodLc_nil 0) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0)))) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_nil [] 1 0)))) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc] using h

/-- ★ シート行 1596。 -/
theorem R1596_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (HcG.PVF_farWAc (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_snoc (HcG.GoodLc_nil 0) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0)))) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_nil [] 1 0))) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc] using h

/-- ★ シート行 1597。 -/
theorem R1597_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 1, 0), (3, 2, 1), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (HcG.PVF_farWAc (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_snoc (HcG.GoodLc_nil 0) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0)))) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_nil 0) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_nil [] 1 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc] using h

/-- ★ シート行 1598。 -/
theorem R1598_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (HcG.PVF_farWAc (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_snoc (HcG.GoodLc_nil 0) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0)))) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_snoc (HcG.GoodLc_nil 0) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0)))) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_nil [] 1 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc] using h

/-- ★ シート行 1599。 -/
theorem R1599_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (HcG.PVF_farWAc (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_snoc (HcG.GoodLc_nil 0) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0)))) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_snoc (HcG.GoodLc_nil 0) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0)))) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_nil [] 1 0))))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc] using h

/-- ★ シート行 1600。 -/
theorem R1600_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 1, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (HcG.PVF_farWAc (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_snoc (HcG.GoodLc_snoc (HcG.GoodLc_nil 0) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0)))) (HcG.okCh_nil 0)) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_nil [] 1 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc] using h

/-- ★ シート行 1601。 -/
theorem R1601_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 1, 0), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (HcG.PVF_farWAc (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_snoc (HcG.GoodLc_snoc (HcG.GoodLc_nil 0) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0)))) (HcG.okCh_nil 0)) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_nil [] 1 0))) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc] using h

/-- ★ シート行 1602。 -/
theorem R1602_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 1, 0), (4, 2, 0), (3, 2, 1), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (HcG.PVF_farWAc (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_snoc (HcG.GoodLc_snoc (HcG.GoodLc_nil 0) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0)))) (HcG.okCh_nil 0)) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_nil 0) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_nil [] 1 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc] using h

/-- ★ シート行 1603。 -/
theorem R1603_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 1, 0), (4, 2, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (HcG.PVF_farWAc (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_snoc (HcG.GoodLc_snoc (HcG.GoodLc_nil 0) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0)))) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0)))) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_nil [] 1 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc] using h

/-- ★ シート行 1604。 -/
theorem R1604_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 1, 0), (4, 2, 0), (5, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (HcG.PVF_farWAc (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_snoc (HcG.GoodLc_snoc (HcG.GoodLc_nil 0) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0)))) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0)))) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_nil [] 1 0)))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc] using h

/-- ★ シート行 1605。 -/
theorem R1605_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 1, 0), (5, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (HcG.PVF_farWAc (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_snoc (HcG.GoodLc_nil 0) (HcG.okCh_tie (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_nil1 0))) (GF_of_GPF (GPF_nil1 0)))) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_nil [] 1 0)))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc] using h

/-- ★ シート行 1606。 -/
theorem R1606_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 1, 0), (6, 2, 1), (7, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (HbX.starOK_CLF (v := 0) ([] : List (List TrioSeq × List (Option TrioSeq))) (HbV.PsL_nil 0) ([] : List TrioSeq) (HbV.DsOK_nil 0) (unitsC 0 ([] : List (Option TrioSeq))) (HbV.LoadSeq_of (by simp [NoTie]) (RawU_nil 0)) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (HcG.PVF_farWAc (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HcG.OkWsAc_cons le_rfl (HcG.GoodLc_snoc (HcG.GoodLc_nil 0) (HcG.okCh_tie (HcG.okCh_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farU (A := []) (o := 1) (by decide) (by decide) (by decide) 0 ([([] : List (Option TrioSeq))] : List (List (Option TrioSeq))) (RawUs_cons (RawU_nil 0) (RawUs_nil 0))))))) (HcG.okRAc_nil [] 1 0) (HcG.OkWsAc_nil [] 1 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc] using h

end HcH
end TRIO
