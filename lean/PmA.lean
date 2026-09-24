/-
PmA.lean: R_pm3（シート行 1690）の上、行 1691 の下を漸進で登る。
土台 = R_pm3 の StarOK（HeW.bwt_KK2）。そこに
- 遠い語を足す（BwT_append_words）、
- 荷を吊るす（starOK_hang）。
-/
import HeW
import GxB
import HdW
import HeJ
import HeP

namespace TRIO
namespace PmA

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdQ HeI HeK HeU HeV HeW
open GzS HaD HaJ HaL HaN HaP HaR HaS HaT HaV HaZ HbB HbJ HbK

/-- R_pm3 の語の並びに、遠い語の並び Ls を足しても StarOK。 -/
theorem starOK_pm3_words {Ls : List TrioSeq} (hW : WordsG 0 Ls) :
    StarOK 0 (rword 0 0 ([Kdeep, GzJ.fwTop 0 []] ++ Ls)) := by
  have hB2 := BwT_append_words (v := 0) (L := [Kdeep, GzJ.fwTop 0 []])
    (by
      intro X hX
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl
      · exact Fr_wLT 0 _
      · exact Fr_fwTop 0 [])
    bwt_KK2 Ls hW
  refine ⟨?_, fun p hp => rword_ge 0 0 _ p hp⟩
  have := hB2 0 le_rfl
  rw [Nat.sub_self] at this
  simpa only [mlift_zero, List.map_id', List.map_cons, List.map_nil] using this

/-- ★ 族: R_pm3 ＋ 遠い語の並び Ls ＋ 吊るした荷 Z。 -/
theorem pm3_words_hang {Ls : List TrioSeq} (hW : WordsG 0 Ls) {u : ℕ} {Z : TrioSeq}
    (hZ : Z ∈ Wg u) (hb : based Z) :
    (((0, 0, 0) : ℕ×ℕ×ℕ) :: (rword 0 0 ([Kdeep, GzJ.fwTop 0 []] ++ Ls) ++ shiftr01 1 0 Z))
      ∈ W 0 :=
  GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_pm3_words hW) hZ hb))

/-- ★ R_pm3 の上、シート行 1649 の形（行 1647 の上の 1649 と同じ足し方）。 -/
theorem Rp3_1649 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 1), (1, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_pm3_words (WordsG_nil 0)) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, Kdeep, HdQ.wLT] using h

/-- ★ R_pm3 の上、シート行 1650 の形（行 1647 の上の 1650 と同じ足し方）。 -/
theorem Rp3_1650 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 1), (3, 2, 0), (4, 3, 0), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_pm3_words (WordsG_nil 0)) (Wg_of_starOK (starOK_hang (HdV.starOK_N2 (v := 1) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HdQ.PsLT_nil 1) (Uss := ([] : List (List HdA.UT))) (HdV.RawssT_nil 1) (us := ([] : List HdA.UT)) (HdV.TRaws_nil 1) (WordsG_nil 1)) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, Kdeep, HdQ.wLT] using h

/-- ★ R_pm3 の上、シート行 1651 の形（行 1647 の上の 1651 と同じ足し方）。 -/
theorem Rp3_1651 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_pm3_words (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, Kdeep, HdQ.wLT] using h

/-- ★ R_pm3 の上、シート行 1652 の形（行 1647 の上の 1652 と同じ足し方）。 -/
theorem Rp3_1652 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_pm3_words (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_nil1 0) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, Kdeep, HdQ.wLT] using h

/-- ★ R_pm3 の上、シート行 1653 の形（行 1647 の上の 1653 と同じ足し方）。 -/
theorem Rp3_1653 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_pm3_words (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farU (A := []) (o := 1) (by decide) (by decide) (by decide) 0 ([([] : List (Option TrioSeq))] : List (List (Option TrioSeq))) (RawUs_cons (RawU_nil 0) (RawUs_nil 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, Kdeep, HdQ.wLT] using h

/-- ★ R_pm3 の上、シート行 1654 の形（行 1647 の上の 1654 と同じ足し方）。 -/
theorem Rp3_1654 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_pm3_words (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (HdH.PVF_farWAt (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HdH.OkWsAt_cons le_rfl (HeI.GoodChtX_snocT (A0 := []) (o := 1) (by decide) (by decide) (by decide) (HdE.GoodChtX_nil [] 1 (fun _ => 0) 0) (HeI.TreeOKs_cons_up (l := 0) rfl (by decide) (HeI.TreeOKs_nil 0 1 false) (HeI.TreeOKs_nil 0 0 true))) (HdH.okRAt_nil [] 1 0) (HdH.OkWsAt_nil [] 1 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT, Kdeep, HdQ.wLT] using h

/-- ★ R_pm3 の上、シート行 1655 の形（行 1647 の上の 1655 と同じ足し方）。 -/
theorem Rp3_1655 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 3, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_pm3_words (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (HdH.PVF_farWAt (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HdH.OkWsAt_cons le_rfl (HeI.GoodChtX_snocT (A0 := []) (o := 1) (by decide) (by decide) (by decide) (HdE.GoodChtX_nil [] 1 (fun _ => 0) 0) (HeI.TreeOKs_cons_up (l := 0) rfl (by decide) (HeI.TreeOKs_nil 0 1 false) (HeI.TreeOKs_nil 0 0 true))) (HdH.okRAt_nil [] 1 0) (HdH.OkWsAt_nil [] 1 0)))) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT, Kdeep, HdQ.wLT] using h

/-- ★ R_pm3 の上、シート行 1656 の形（行 1647 の上の 1656 と同じ足し方）。 -/
theorem Rp3_1656 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 3, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 3, 0), (6, 3, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_pm3_words (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (HdH.PVF_farWAt (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HdH.OkWsAt_cons le_rfl (HeI.GoodChtX_snocT (A0 := []) (o := 1) (by decide) (by decide) (by decide) (HdE.GoodChtX_nil [] 1 (fun _ => 0) 0) (HeI.TreeOKs_cons_up (l := 0) rfl (by decide) (HeI.TreeOKs_nil 0 1 false) (HeI.TreeOKs_nil 0 0 true))) (HdH.okRAt_nil [] 1 0) (HdH.OkWsAt_nil [] 1 0)))) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [] (by decide) (GPF_of_PVF (HcP.PVF_farWAu (A0 := []) (o := 2) (by decide) (by decide) (by decide) 0 _ (HcP.OkWsAu_cons le_rfl (HcP.GoodChuX_snocU (A0 := []) (o := 2) (by decide) (by decide) (by decide) (HcM.GoodChuX_nil [] 2 (fun _ => 0) 0) (HcP.GoodLow_none (HcN.GoodLow_nil 0))) (HcP.okRAu_nil [] 2 0) (HcP.OkWsAu_nil [] 2 0)))) (GPF_nil (A := []) (o := 3) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT, Kdeep, HdQ.wLT] using h

/-- ★ R_pm3 の上、シート行 1657 の形（行 1647 の上の 1657 と同じ足し方）。 -/
theorem Rp3_1657 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 3, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_pm3_words (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (HdH.PVF_farWAt (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HdH.OkWsAt_cons le_rfl (HeI.GoodChtX_snocT (A0 := []) (o := 1) (by decide) (by decide) (by decide) (HdE.GoodChtX_nil [] 1 (fun _ => 0) 0) (HeI.TreeOKs_cons_up (l := 0) rfl (by decide) (HeI.TreeOKs_nil 0 1 false) (HeI.TreeOKs_nil 0 0 true))) (HdH.okRAt_nil [] 1 0) (HdH.OkWsAt_nil [] 1 0))) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT, Kdeep, HdQ.wLT] using h

/-- ★ R_pm3 の上、シート行 1658 の形（行 1647 の上の 1658 と同じ足し方）。 -/
theorem Rp3_1658 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (5, 3, 0), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (6, 3, 0), (7, 4, 0), (5, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_pm3_words (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (HdH.PVF_farWAt (A0 := []) (o := 1) (by decide) (by decide) (by decide) 0 _ (HdH.OkWsAt_cons le_rfl (HeI.GoodChtX_snocT (A0 := []) (o := 1) (by decide) (by decide) (by decide) (HdE.GoodChtX_nil [] 1 (fun _ => 0) 0) (HeI.TreeOKs_cons_up (l := 0) rfl (by decide) (HeI.TreeOKs_nil 0 1 false) (HeI.TreeOKs_nil 0 0 true))) (HdH.okRAt_nil [] 1 0) (HdH.OkWsAt_nil [] 1 0))) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [1]) (o := 2) (by decide) (HdH.PVF_farWAt (A0 := [1]) (o := 2) (by decide) (by decide) (by decide) 0 _ (HdH.OkWsAt_cons le_rfl (HeI.GoodChtX_snocT (A0 := [1]) (o := 2) (by decide) (by decide) (by decide) (HdE.GoodChtX_nil [1] 2 (fun _ => 0) 0) (HeI.TreeOKs_cons_up (l := 0) rfl (by decide) (HeI.TreeOKs_nil 0 1 false) (HeI.TreeOKs_nil 0 0 true))) (HdH.okRAt_nil [1] 2 0) (HdH.OkWsAt_nil [1] 2 0))) (RLF_nil (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT, Kdeep, HdQ.wLT] using h

/-! ## 2 本目の collapse 語: 文脈 [Kdeep, fwTop 0 []] は GLctx -/

/-- 空の語のデータ（fwTop v [] = wLT v p0）。 -/
def p0 : List (List UT) × List (Option TrioSeq) := ([], [])

theorem psLT_p1p0 (u : ℕ) :
    psLT u [p1, p0] = [([[HdA.UT.tie 1 [HdA.UT.tie 1 []]]], u, ([] : TrioSeq)), ([], u, [])] := by
  simp [psLT, p1, p0, farTs, farT, unitsC]

theorem OkWsAt_KK {u b : ℕ} (hub : u ≤ b) : OkWsAt [] 1 b (psLT u [p1, p0]) := by
  rw [psLT_p1p0]
  exact HdH.OkWsAt_cons hub (HeU.GoodChtX_deep (by simp) (by simp) (by decide)) (HdH.okRAt_nil [] 1 u)
    (HdH.OkWsAt_cons hub (HdE.GoodChtX_nil [] 1 _ u) (HdH.okRAt_nil [] 1 u) (HdH.OkWsAt_nil [] 1 b))

/-- ★ 文脈 [Kdeep, fwTop 0 []] は GLctx。 -/
theorem GLctx_KK : GLctx 0 [Kdeep, GzJ.fwTop 0 []] := by
  have hraw : ∀ u, ∀ p ∈ [p1, p0], (∀ us ∈ p.1, TRawLs u us) ∧ GzJ.NoTie p.2 ∧ RawU u p.2 := by
    intro u p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨TRawLs_deep u, by simp [p1, GzJ.NoTie], RawU_nil u⟩
    · exact ⟨by simp [p0], by simp [p0, GzJ.NoTie], RawU_nil u⟩
  refine ⟨[p1, p0], hraw 0, fun u _ => ⟨RawWskt0_gen (hraw u),
    HdH.FarCAt_of_OkWsAt (by simp) (by simp) (by decide) _ (OkWsAt_KK le_rfl) u,
    HdH.RawWsAt_of_OkWsAt (OkWsAt_KK le_rfl)⟩, ?_⟩
  simp [Kdeep, p1, p0, wLT, GzJ.fwTop, FTL0]

/-- ★★ BwT 0 [Kdeep, fwTop, fwTop]（深い葉のあとに collapse 語を 2 本）。 -/
theorem bwt_KK3 : BwT 0 [Kdeep, GzJ.fwTop 0 [], GzJ.fwTop 0 []] := by
  have := GTC_far_gen 0 [Kdeep, GzJ.fwTop 0 []] GLctx_KK
    (by
      intro X hX
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl
      · exact Fr_wLT 0 _
      · exact Fr_fwTop 0 []) bwt_KK2
  simpa using this

/-- ★ (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(1,1,1)(2,1,1)(1,1,1)(2,1,1) ∈ W 0（行 1659 の形）。 -/
theorem Rp3_1659 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(1,1,1),(2,1,1),(1,1,1),(2,1,1)] : TrioSeq)
    ∈ W 0 := by
  have hS : StarOK 0 (rword 0 0 [Kdeep, GzJ.fwTop 0 [], GzJ.fwTop 0 []]) := by
    refine ⟨?_, fun p hp => rword_ge 0 0 _ p hp⟩
    have h2 := bwt_KK3 0 le_rfl
    rw [Nat.sub_self] at h2
    simpa only [mlift_zero, List.map_cons, List.map_nil] using h2
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK hS)
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01, Kdeep, GzJ.fwTop] using h

/-! ## 深い葉の語を先頭に持つ文脈（HeK.PsLd）: 後ろに F のタイの子が段つきの木の語を足す -/

/-- 深い葉の語 [p1] は一般化した文脈の条件 PsLd を満たす。 -/
theorem PsLd_p1 : PsLd 0 [p1] := by
  refine ⟨fun p hp => ?_, fun u _ => ?_⟩
  · simp only [List.mem_singleton] at hp; subst hp
    exact ⟨TRawLs_deep 0, by simp [p1, GzJ.NoTie], RawU_nil 0⟩
  · rw [psLT_p1]; exact HeV.OkWsAt_deep le_rfl

/-- ★★ 深い葉の語のあとに、F のタイの子が段つきの木の語の並び qs を足した BwT。 -/
theorem BwT_deep_CLTL : ∀ qs : List (List (List UT) × List (Option TrioSeq)),
    PsLTL 0 qs → BwT 0 ((p1 :: qs).map (wLT 0)) := by
  intro qs
  induction qs using List.reverseRecOn with
  | nil =>
      intro _
      have := HeT.hK_pm [] ⟨[], PsLd_of_PsLTL (PsLTL_nil 0), rfl⟩ (by simp) (BwT_nil 0)
      simpa [p1] using this
  | append_singleton qs q ih =>
      intro h
      have h' : PsLTL 0 qs := fun r hr => h r (List.mem_append_left _ hr)
      have hq := h q (List.mem_append_right _ (List.mem_singleton_self _))
      have hG := HeN.GTC_wLTL hq.1 (HeN.GoodTTL_all q.1 hq.1) q.2 hq.2.1 hq.2.2
      have hC : PsLd 0 (p1 :: qs) := by
        have := PsLd_append PsLd_p1 (PsLd_of_PsLTL h')
        simpa using this
      have := hG _ ⟨p1 :: qs, hC, rfl⟩ (Fr_CLT 0 (p1 :: qs)) (ih h')
      simpa [List.map_append] using this

/-- ★ 深い葉の語 ＋ 段つきの木の語の並び qs ＋ 遠い語の並び Ls は StarOK。 -/
theorem starOK_deep_CLTL (qs : List (List (List UT) × List (Option TrioSeq))) (h : PsLTL 0 qs)
    {Ls : List TrioSeq} (hW : WordsG 0 Ls) :
    StarOK 0 (rword 0 0 ((p1 :: qs).map (wLT 0) ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 0 _ p hp⟩
  have hB := BwT_append_words (Fr_CLT 0 (p1 :: qs)) (BwT_deep_CLTL qs h) Ls hW 0 le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

/-- ★ 族: 深い葉の語 ＋ 段つきの木の語 qs ＋ 遠い語 Ls ＋ 吊るした荷 Z。 -/
theorem deep_CLTL_hang (qs : List (List (List UT) × List (Option TrioSeq))) (h : PsLTL 0 qs)
    {Ls : List TrioSeq} (hW : WordsG 0 Ls) {u : ℕ} {Z : TrioSeq} (hZ : Z ∈ Wg u) (hb : based Z) :
    (((0, 0, 0) : ℕ×ℕ×ℕ) :: (rword 0 0 ((p1 :: qs).map (wLT 0) ++ Ls) ++ shiftr01 1 0 Z)) ∈ W 0 :=
  GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_deep_CLTL qs h hW) hZ hb))

/-- ★ R_pm ＋ シート行 1661 の尾（行 1647 の上の 1661 と同じ足し方）。 -/
theorem Rpm_1661 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_deep_CLTL ([(([([] : List HdA.UT)] : List (List HdA.UT)), ([] : List (Option TrioSeq)))] : List (List (List HdA.UT) × List (Option TrioSeq))) (HeK.PsLTL_cons (HeO.TreeTss_cons (HeK.TreeTs_nil 0 0 true) (HeO.TreeTss_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HeK.PsLTL_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT, p1, HdQ.wLT] using h

/-- ★ R_pm ＋ シート行 1662 の尾（行 1647 の上の 1662 と同じ足し方）。 -/
theorem Rpm_1662 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_deep_CLTL ([(([([] : List HdA.UT)] : List (List HdA.UT)), ([] : List (Option TrioSeq))), (([] : List (List HdA.UT)), ([] : List (Option TrioSeq)))] : List (List (List HdA.UT) × List (Option TrioSeq))) (HeK.PsLTL_cons (HeO.TreeTss_cons (HeK.TreeTs_nil 0 0 true) (HeO.TreeTss_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HeK.PsLTL_cons (HeO.TreeTss_nil 0) (by simp [NoTie]) (RawU_nil 0) (HeK.PsLTL_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT, p1, HdQ.wLT] using h

/-- ★ R_pm ＋ シート行 1663 の尾（行 1647 の上の 1663 と同じ足し方）。 -/
theorem Rpm_1663 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_deep_CLTL ([(([([] : List HdA.UT), ([] : List HdA.UT)] : List (List HdA.UT)), ([] : List (Option TrioSeq))), (([] : List (List HdA.UT)), ([] : List (Option TrioSeq)))] : List (List (List HdA.UT) × List (Option TrioSeq))) (HeK.PsLTL_cons (HeO.TreeTss_cons (HeK.TreeTs_nil 0 0 true) (HeO.TreeTss_cons (HeK.TreeTs_nil 0 0 true) (HeO.TreeTss_nil 0))) (by simp [NoTie]) (RawU_nil 0) (HeK.PsLTL_cons (HeO.TreeTss_nil 0) (by simp [NoTie]) (RawU_nil 0) (HeK.PsLTL_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT, p1, HdQ.wLT] using h

/-- ★ R_pm ＋ シート行 1664 の尾（行 1647 の上の 1664 と同じ足し方）。 -/
theorem Rpm_1664 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_deep_CLTL ([(([([HdA.UT.tie 0 ([] : List HdA.UT)] : List HdA.UT)] : List (List HdA.UT)), ([] : List (Option TrioSeq))), (([] : List (List HdA.UT)), ([] : List (Option TrioSeq)))] : List (List (List HdA.UT) × List (Option TrioSeq))) (HeK.PsLTL_cons (HeO.TreeTss_cons (HeK.TreeTs_cons_tie0 (HeK.TreeTs_nil 0 0 true) (HeK.TreeTs_nil 0 0 true)) (HeO.TreeTss_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HeK.PsLTL_cons (HeO.TreeTss_nil 0) (by simp [NoTie]) (RawU_nil 0) (HeK.PsLTL_nil 0))) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT, p1, HdQ.wLT] using h

/-- ★ R_pm ＋ シート行 1665 の尾（行 1647 の上の 1665 と同じ足し方）。 -/
theorem Rpm_1665 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_deep_CLTL ([(([([HdA.UT.tie 1 ([] : List HdA.UT)] : List HdA.UT)] : List (List HdA.UT)), ([] : List (Option TrioSeq)))] : List (List (List HdA.UT) × List (Option TrioSeq))) (HeK.PsLTL_cons (HeO.TreeTss_cons (HeK.TreeTs_cons_up (l := 0) rfl (by decide) (HeK.TreeTs_nil 0 1 false) (HeK.TreeTs_nil 0 0 true)) (HeO.TreeTss_nil 0)) (by simp [NoTie]) (RawU_nil 0) (HeK.PsLTL_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT, p1, HdQ.wLT] using h


/-! ## 深い葉の語に荷を吊るす -/

/-- 深い葉の語（荷 us つき）は PsLd を満たす。 -/
theorem PsLd_deepword {v : ℕ} {us : List (Option TrioSeq)} (hNT : GzJ.NoTie us) (hR : RawU v us) :
    PsLd v [(p1.1, us)] := by
  refine ⟨fun p hp => ?_, fun u hu w hw => ?_⟩
  · simp only [List.mem_singleton] at hp; subst hp
    exact ⟨TRawLs_deep v, hNT, hR⟩
  · simp only [psLT, List.map_cons, List.map_nil, List.mem_singleton] at hw; subst hw
    refine ⟨le_rfl, ?_, okRAt_units us hNT (RawU_mono hu hR)⟩
    simpa [p1, farTs, farT] using
      (HeU.GoodChtX_deep (A0 := []) (o := 1) (u := u) (by simp) (by simp) (by decide))

/-- ★ 深い葉の語に荷を 1 つ吊るす（GTC_load_CLTL の深い葉版）。 -/
theorem GTC_load_deep {v : ℕ} {us : List (Option TrioSeq)} (hNT : GzJ.NoTie us) (hRus : RawU v us)
    (hG : GTC CLTL v (wLT v (p1.1, us))) :
    ∀ T ∈ Wg (2 * v), based T → GTC CLTL v (wLT v (p1.1, us ++ [some T])) := by
  intro T hT hbT
  have e : ∀ T' : TrioSeq, wLT v (p1.1, us ++ [some T']) = wLT v (p1.1, us) ++ shiftr01 1 0 T' := by
    intro T'
    show FTL0 (v + 1) (p1.1.map (topTs v)) ++ unitsC v (us ++ [some T'])
      = FTL0 (v + 1) (p1.1.map (topTs v)) ++ unitsC v us ++ shiftr01 1 0 T'
    rw [unitsC_snoc, List.append_assoc]; rfl
  rw [e]
  refine GTC_loadTop (Fr_wLT v _) hG ?_ T hT hbT
  intro T' hT' hbT' L hC
  obtain ⟨ps, h, rfl⟩ := hC
  refine ⟨ps ++ [(p1.1, us ++ [some T'])], PsLd_append h (PsLd_deepword ?_ ?_), ?_⟩
  · intro hn
    rcases List.mem_append.mp hn with hn | hn
    · exact hNT hn
    · simp at hn
  · intro Z hZ
    rcases List.mem_append.mp hZ with hZ | hZ
    · exact hRus Z hZ
    · simp at hZ; subst hZ; exact ⟨hT', hbT'⟩
  · rw [List.map_append, List.map_singleton, e]

/-- ★ 深い葉の語に荷の並び us を吊るした語は、文脈 CLTL で良い。 -/
theorem GTC_deep_loads : ∀ us : List (Option TrioSeq), GzJ.NoTie us → RawU 0 us →
    GTC CLTL 0 (wLT 0 (p1.1, us)) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _; simpa [p1] using HeT.hK_pm
  | append_singleton us o ih =>
      intro hNT hR
      have hNT' : GzJ.NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z =>
          have hZ := hR Z (by simp)
          exact GTC_load_deep hNT' (RawU_prefix hR) (ih hNT' (RawU_prefix hR)) Z hZ.1 hZ.2

/-- ★★ 深い葉の語（荷 us0）のあとに段つきの木の語の並び qs。 -/
theorem BwT_deepL (us0 : List (Option TrioSeq)) (hNT : GzJ.NoTie us0) (hR : RawU 0 us0) :
    ∀ qs : List (List (List UT) × List (Option TrioSeq)),
    PsLTL 0 qs → BwT 0 (((p1.1, us0) :: qs).map (wLT 0)) := by
  intro qs
  induction qs using List.reverseRecOn with
  | nil =>
      intro _
      have := GTC_deep_loads us0 hNT hR [] ⟨[], PsLd_of_PsLTL (PsLTL_nil 0), rfl⟩ (by simp) (BwT_nil 0)
      simpa using this
  | append_singleton qs q ih =>
      intro h
      have h' : PsLTL 0 qs := fun r hr => h r (List.mem_append_left _ hr)
      have hq := h q (List.mem_append_right _ (List.mem_singleton_self _))
      have hG := HeN.GTC_wLTL hq.1 (HeN.GoodTTL_all q.1 hq.1) q.2 hq.2.1 hq.2.2
      have hC : PsLd 0 ((p1.1, us0) :: qs) := by
        have := PsLd_append (PsLd_deepword hNT hR) (PsLd_of_PsLTL h')
        simpa using this
      have := hG _ ⟨(p1.1, us0) :: qs, hC, rfl⟩ (Fr_CLT 0 ((p1.1, us0) :: qs)) (ih h')
      simpa [List.map_append] using this

/-- ★ 族: 深い葉の語（荷 us0）＋ 段つきの木の語 qs ＋ 遠い語 Ls ＋ 吊るした荷 Z。 -/
theorem deepL_hang (us0 : List (Option TrioSeq)) (hNT : GzJ.NoTie us0) (hR : RawU 0 us0)
    (qs : List (List (List UT) × List (Option TrioSeq))) (h : PsLTL 0 qs)
    {Ls : List TrioSeq} (hW : WordsG 0 Ls) {u : ℕ} {Z : TrioSeq} (hZ : Z ∈ Wg u) (hb : based Z) :
    (((0, 0, 0) : ℕ×ℕ×ℕ) :: (rword 0 0 (((p1.1, us0) :: qs).map (wLT 0) ++ Ls) ++ shiftr01 1 0 Z))
      ∈ W 0 := by
  have hS : StarOK 0 (rword 0 0 (((p1.1, us0) :: qs).map (wLT 0) ++ Ls)) := by
    refine ⟨?_, fun p hp => rword_ge 0 0 _ p hp⟩
    have hB := BwT_append_words (Fr_CLT 0 ((p1.1, us0) :: qs)) (BwT_deepL us0 hNT hR qs h) Ls hW 0 le_rfl
    rw [Nat.sub_self] at hB
    simpa only [mlift_zero, List.map_id'] using hB
  exact GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang hS hZ hb))

/-- ★ R_pm ＋ シート行 1666 の尾: (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(2,0,0) ∈ W 0。 -/
theorem Rpm_1666 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(2,0,0)] : TrioSeq) ∈ W 0 := by
  have hZ0 : ([(0, 0, 0)] : TrioSeq) ∈ Wg (2 * 0) := by
    simpa [rword] using Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))
  have hS : StarOK 0 (rword 0 0 [wLT 0 (p1.1, [some [(0, 0, 0)]])]) := by
    refine ⟨?_, fun p hp => rword_ge 0 0 _ p hp⟩
    have hB := GTC_deep_loads [some [(0, 0, 0)]] (by simp [GzJ.NoTie])
      (RawU_cons_some hZ0 rfl (RawU_nil 0)) [] ⟨[], PsLd_of_PsLTL (PsLTL_nil 0), rfl⟩ (by simp) (BwT_nil 0)
    have h2 := hB 0 le_rfl
    rw [Nat.sub_self] at h2
    simpa only [mlift_zero, List.map_cons, List.map_nil, List.nil_append] using h2
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK hS)
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, unitC, shiftr01, p1] using h

/-! ## 深い葉の語は全ての段で良い（hK_pm の段 u 版） -/

theorem topTs_dtreeQ (u : ℕ) : ∀ j, topTs 0 [HeU.dtreeQ u j] = topTs u [HeT.dtree j] := by
  intro j
  induction j with
  | zero =>
      simp only [HeU.dtreeQ, HeT.dtree, topTs, topT, List.append_nil]
      rw [show 0 + 1 + (u + 1) = u + 1 + 1 by omega]
  | succ j ih =>
      simp only [HeU.dtreeQ, HeT.dtree, topTs, topT, List.append_nil] at ih ⊢
      rw [ih, show 0 + 1 + (u + 1) = u + 1 + 1 by omega, show 0 + 1 + u = u + 1 + 0 by omega]

theorem TreeTs_dtree_u (u j : ℕ) : TreeTs u 0 true [HeT.dtree j] := by
  induction j with
  | zero => exact TreeTs_cons_up (l := 0) rfl (by decide) (TreeTs_nil u 1 false) (TreeTs_nil u 0 true)
  | succ j ih =>
    exact TreeTs_cons_up (l := 0) rfl (by decide)
      (TreeTs_cons_tie0 ih (TreeTs_nil u 1 false)) (TreeTs_nil u 0 true)

/-- ★★ 深い葉の語は全ての段 u で文脈 CLTL について良い。 -/
theorem hK_pm_u (u : ℕ) : GTC CLTL u (wLT u ([[HdA.UT.tie 1 [HdA.UT.tie 1 []]]], ([] : List (Option TrioSeq)))) := by
  have e : wLT u ([[HdA.UT.tie 1 [HdA.UT.tie 1 []]]], ([] : List (Option TrioSeq)))
      = ([(1,u+1,1)] : TrioSeq) ++ shiftr01 0 0 (shiftr01 1 0
        (((0, u+1, 0) : ℕ×ℕ×ℕ) :: ([((1,u+2,0):ℕ×ℕ×ℕ)] ++ [((2, u+2, 0) : ℕ×ℕ×ℕ)]))) := by
    simp [wLT, FTL0, topTs, topT, unitsC, shiftr01]
  rw [e]
  refine HeN.upleaf_deep_coreDT (C := CLTL) (u := u) (d := 0) (q := u+1) (d0 := 2) (m := u+2)
    (D := [(1,u+2,0)]) (by intro p hp; simp at hp; subst hp; simp)
    (by intro p hp; simp at hp; subst hp; simp) (by decide) (by omega) (by omega) (fun m' hm' => ?_)
  obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
  have ee : ([(1,u+1,1)] : TrioSeq) ++ shiftr01 0 0 (shiftr01 1 0
      (tow (u+1) 0 ([((1,u+2,0):ℕ×ℕ×ℕ)] ++ [((2,u+2,0):ℕ×ℕ×ℕ)]) (j+1)))
      = wLT u ([[HeT.dtree j]], ([] : List (Option TrioSeq))) := by
    rw [show ([((1,u+2,0):ℕ×ℕ×ℕ)] ++ [((2,u+2,0):ℕ×ℕ×ℕ)]) = [((1,u+2,0):ℕ×ℕ×ℕ),((2,u+2,0):ℕ×ℕ×ℕ)] from rfl,
      HeU.tow_dtreeQ u j, topTs_dtreeQ u j]
    simp [wLT, FTL0, topTs, unitsC, shiftr01]
  rw [ee]
  exact HeN.GTC_wLTL (fun us' hus' => by simp at hus'; subst hus'; exact TreeTs_dtree_u u j)
    (HeN.GoodTTL_all _ (fun us' hus' => by simp at hus'; subst hus'; exact TreeTs_dtree_u u j))
    [] (by simp [GzJ.NoTie]) (RawU_nil u)

/-! ## 深い葉の語に子の並びを足す（GdT の世界、HeK.WOK） -/

theorem WOK_deep (v : ℕ) : WOK v p1.1 := by
  refine ⟨TRawLs_deep v, fun u _ => ?_⟩
  simpa [p1, farTs, farT] using
    (HeU.GoodChtX_deep (A0 := []) (o := 1) (u := u) (by simp) (by simp) (by decide))

theorem WOK_deep_append (v : ℕ) : ∀ Uss : List (List UT), (∀ us ∈ Uss, TreeTs v 0 true us) →
    WOK v (p1.1 ++ Uss) := by
  intro Uss
  induction Uss using List.reverseRecOn with
  | nil => intro _; simpa using WOK_deep v
  | append_singleton Uss us ih =>
      intro h
      have h' : ∀ us' ∈ Uss, TreeTs v 0 true us' := fun us' hus' => h us' (List.mem_append_left _ hus')
      have hus := h us (List.mem_append_right _ (List.mem_singleton_self _))
      have := WOK_snoc (ih h') hus
      rwa [List.append_assoc] at this

/-- ★ 深い葉の子の並びのあとに段つきの木の子の並び Uss を足した語は良い。 -/
theorem GoodTTL_deep : ∀ Uss : List (List UT), (∀ us ∈ Uss, TreeTs 0 0 true us) →
    HeL.GoodTTL 0 (p1.1 ++ Uss) := by
  intro Uss
  induction Uss using List.reverseRecOn with
  | nil => intro _ u _; rw [List.append_nil]; exact hK_pm_u u
  | append_singleton Uss us ih =>
      intro h
      have h' : ∀ us' ∈ Uss, TreeTs 0 0 true us' := fun us' hus' => h us' (List.mem_append_left _ hus')
      have hus := h us (List.mem_append_right _ (List.mem_singleton_self _))
      have := HeL.GdT_good HeL.TPSOK_TP0 (HeN.GdT_treeTP0 hus) le_rfl (WOK_deep_append 0 Uss h') (ih h')
        (HeL.TPNil_TP0 0)
      have e : (p1.1 ++ Uss) ++ [HeB.plugQ [] us] = p1.1 ++ (Uss ++ [us]) := by simp [HeB.plugQ]
      rwa [e] at this

/-- GTC_wLTL の WOK 版（荷の並び us つき）。 -/
theorem GTC_wLTLw {v : ℕ} {Uss : List (List UT)} (hU : WOK v Uss) (hG : HeL.GoodTTL v Uss) :
    ∀ us : List (Option TrioSeq), GzJ.NoTie us → RawU v us → GTC CLTL v (wLT v (Uss, us)) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _; exact hG v le_rfl
  | append_singleton us o ih =>
      intro hNT hR
      have hNT' : GzJ.NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z =>
          have hZ := hR Z (by simp)
          exact GTC_load_CLTL hU hNT' (RawU_prefix hR) (ih hNT' (RawU_prefix hR)) Z hZ.1 hZ.2

/-- ★★ 先頭の語（深い葉 ＋ 子の並び Uss0、荷 us0）のあとに段つきの木の語の並び qs。 -/
theorem BwT_deepW (Uss0 : List (List UT)) (hU0 : ∀ us ∈ Uss0, TreeTs 0 0 true us)
    (us0 : List (Option TrioSeq)) (hNT : GzJ.NoTie us0) (hR : RawU 0 us0) :
    ∀ qs : List (List (List UT) × List (Option TrioSeq)),
    PsLTL 0 qs → BwT 0 (((p1.1 ++ Uss0, us0) :: qs).map (wLT 0)) := by
  intro qs
  induction qs using List.reverseRecOn with
  | nil =>
      intro _
      have := GTC_wLTLw (WOK_deep_append 0 Uss0 hU0) (GoodTTL_deep Uss0 hU0) us0 hNT hR
        [] ⟨[], PsLd_of_PsLTL (PsLTL_nil 0), rfl⟩ (by simp) (BwT_nil 0)
      simpa using this
  | append_singleton qs q ih =>
      intro h
      have h' : PsLTL 0 qs := fun r hr => h r (List.mem_append_left _ hr)
      have hq := h q (List.mem_append_right _ (List.mem_singleton_self _))
      have hG := HeN.GTC_wLTL hq.1 (HeN.GoodTTL_all q.1 hq.1) q.2 hq.2.1 hq.2.2
      have hC : PsLd 0 ((p1.1 ++ Uss0, us0) :: qs) := by
        have := PsLd_append (PsLd_word (WOK_deep_append 0 Uss0 hU0) hNT hR) (PsLd_of_PsLTL h')
        simpa using this
      have := hG _ ⟨(p1.1 ++ Uss0, us0) :: qs, hC, rfl⟩ (Fr_CLT 0 ((p1.1 ++ Uss0, us0) :: qs)) (ih h')
      simpa [List.map_append] using this

theorem starOK_deepW (Uss0 : List (List UT)) (hU0 : ∀ us ∈ Uss0, TreeTs 0 0 true us)
    (us0 : List (Option TrioSeq)) (hNT : GzJ.NoTie us0) (hR : RawU 0 us0)
    (qs : List (List (List UT) × List (Option TrioSeq))) (h : PsLTL 0 qs)
    {Ls : List TrioSeq} (hW : WordsG 0 Ls) :
    StarOK 0 (rword 0 0 (((p1.1 ++ Uss0, us0) :: qs).map (wLT 0) ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 0 _ p hp⟩
  have hB := BwT_append_words (Fr_CLT 0 ((p1.1 ++ Uss0, us0) :: qs)) (BwT_deepW Uss0 hU0 us0 hNT hR qs h)
    Ls hW 0 le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

/-- ★ 族: 先頭の語（深い葉 ＋ 子の並び Uss0、荷 us0）＋ 段つきの木の語 qs ＋ 遠い語 Ls ＋ 吊るした荷 Z。 -/
theorem deepW_hang (Uss0 : List (List UT)) (hU0 : ∀ us ∈ Uss0, TreeTs 0 0 true us)
    (us0 : List (Option TrioSeq)) (hNT : GzJ.NoTie us0) (hR : RawU 0 us0)
    (qs : List (List (List UT) × List (Option TrioSeq))) (h : PsLTL 0 qs)
    {Ls : List TrioSeq} (hW : WordsG 0 Ls) {u : ℕ} {Z : TrioSeq} (hZ : Z ∈ Wg u) (hb : based Z) :
    (((0, 0, 0) : ℕ×ℕ×ℕ) :: (rword 0 0 (((p1.1 ++ Uss0, us0) :: qs).map (wLT 0) ++ Ls) ++ shiftr01 1 0 Z))
      ∈ W 0 :=
  GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_deepW Uss0 hU0 us0 hNT hR qs h hW) hZ hb))

/-- ★ R_pm ＋ シート行 1667 の尾（深い葉の語に子の並びを足す）。 -/
theorem Rpm_1667 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_deepW ([([] : List HdA.UT)] : List (List HdA.UT)) (HeO.TreeTss_cons (HeK.TreeTs_nil 0 0 true) (HeO.TreeTss_nil 0)) ([] : List (Option TrioSeq)) (by simp [NoTie]) (RawU_nil 0) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HeK.PsLTL_nil 0) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT, p1, HdQ.wLT] using h

/-- ★ R_pm ＋ シート行 1668 の尾（深い葉の語に子の並びを足す）。 -/
theorem Rpm_1668 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_deepW ([([] : List HdA.UT)] : List (List HdA.UT)) (HeO.TreeTss_cons (HeK.TreeTs_nil 0 0 true) (HeO.TreeTss_nil 0)) ([] : List (Option TrioSeq)) (by simp [NoTie]) (RawU_nil 0) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HeK.PsLTL_nil 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT, p1, HdQ.wLT] using h

/-- ★ R_pm ＋ シート行 1669 の尾（深い葉の語に子の並びを足す）。 -/
theorem Rpm_1669 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (2, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_deepW ([([] : List HdA.UT)] : List (List HdA.UT)) (HeO.TreeTss_cons (HeK.TreeTs_nil 0 0 true) (HeO.TreeTss_nil 0)) ([] : List (Option TrioSeq)) (by simp [NoTie]) (RawU_nil 0) ([(([] : List (List HdA.UT)), ([] : List (Option TrioSeq)))] : List (List (List HdA.UT) × List (Option TrioSeq))) (HeK.PsLTL_cons (HeO.TreeTss_nil 0) (by simp [NoTie]) (RawU_nil 0) (HeK.PsLTL_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT, p1, HdQ.wLT] using h

/-- ★ R_pm ＋ シート行 1670 の尾（深い葉の語に子の並びを足す）。 -/
theorem Rpm_1670 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_deepW ([([HdA.UT.tie 0 ([] : List HdA.UT)] : List HdA.UT)] : List (List HdA.UT)) (HeO.TreeTss_cons (HeK.TreeTs_cons_tie0 (HeK.TreeTs_nil 0 0 true) (HeK.TreeTs_nil 0 0 true)) (HeO.TreeTss_nil 0)) ([] : List (Option TrioSeq)) (by simp [NoTie]) (RawU_nil 0) ([(([] : List (List HdA.UT)), ([] : List (Option TrioSeq)))] : List (List (List HdA.UT) × List (Option TrioSeq))) (HeK.PsLTL_cons (HeO.TreeTss_nil 0) (by simp [NoTie]) (RawU_nil 0) (HeK.PsLTL_nil 0)) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT, p1, HdQ.wLT] using h

/-- ★ R_pm ＋ シート行 1671 の尾（深い葉の語に子の並びを足す）。 -/
theorem Rpm_1671 : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_deepW ([([HdA.UT.tie 1 ([] : List HdA.UT)] : List HdA.UT)] : List (List HdA.UT)) (HeO.TreeTss_cons (HeK.TreeTs_cons_up (l := 0) rfl (by decide) (HeK.TreeTs_nil 0 1 false) (HeK.TreeTs_nil 0 0 true)) (HeO.TreeTss_nil 0)) ([] : List (Option TrioSeq)) (by simp [NoTie]) (RawU_nil 0) ([] : List (List (List HdA.UT) × List (Option TrioSeq))) (HeK.PsLTL_nil 0) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil, HbB.wT, HbK.wN, HbD.farWn, HbD.fwWn, HbD.FT, HbV.wL, HbP.FTL0, HbM.fwH, HcA.farWc, HcA.FTLc, HcI.farWu, HcI.FTLu, HcI.chF, HcI.unitF, HcS.wLU, HdQ.wLT, HdQ.topTs, HdQ.topT, HdA.farWt, HdA.FTLt, HdA.chT, HdA.unitT, p1, HdQ.wLT] using h

end PmA
end TRIO
