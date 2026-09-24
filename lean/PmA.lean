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


end PmA
end TRIO
