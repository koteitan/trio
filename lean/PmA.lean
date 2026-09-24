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

/-! ## 深い葉の子の並びを任意の良い接頭辞の後ろに足す -/

/-- ★★ GoodChtX_deep の接頭辞つき版: 良い子の並び Lds の後ろに深い葉の子の並びを足しても良い。 -/
theorem GoodChtX_snoc_deep {A0 : List ℕ} {o u : ℕ} (hAo : ∀ a ∈ A0, a < o) (hA01 : ∀ a ∈ A0, 1 ≤ a)
    (ho : 1 ≤ o) {Lds : List (List UT)} (hL : GoodChtX A0 o (fun _ => 0) u Lds) :
    GoodChtX A0 o (fun _ => 0) u (Lds ++ [[HdA.UT.tie 1 [HdA.UT.tie 1 []]]]) := by
  refine ⟨fun us hus => ?_, fun g S o' f b hE hub ws hC hR => ?_⟩
  · rcases List.mem_append.mp hus with hus | hus
    · exact hL.1 us hus
    · simp only [List.mem_singleton] at hus; subst hus; simp [RawTs, RawT]
  · have hrel : (Lds ++ [[HdA.UT.tie 1 [HdA.UT.tie 1 []]]]).map (relTs A0 (fun _ => 0) g u)
        = Lds.map (relTs A0 (fun _ => 0) g u) ++ [[HdA.UT.tie 1 [HdA.UT.tie 1 []]]] := by
      simp [relTs, relT]
    rw [hrel, farWt_snoc]
    obtain ⟨q0, hq0⟩ : ∃ q0, b + liftOff f (S ++ A0) o' + 1 = q0 + 1 :=
      ⟨b + liftOff f (S ++ A0) o', rfl⟩
    rw [hq0]
    have key : fwH b (q0+1) (FTLt b (q0+1) u
          (Lds.map (relTs A0 (fun _ => 0) g u) ++ [[HdA.UT.tie 1 [HdA.UT.tie 1 []]]])) u []
        = fwH b (q0+1) (FTLt b (q0+1) u (Lds.map (relTs A0 (fun _ => 0) g u))) u []
          ++ shiftr01 1 0 (shiftr01 1 0 (((0,q0+1,0):ℕ×ℕ×ℕ) :: ([((1,q0+2,0):ℕ×ℕ×ℕ)] ++ [((2,q0+2,0):ℕ×ℕ×ℕ)]))) := by
      simp [fwH, FTLt_snoc, chT, unitT, shiftr01, mlift_nil]
    rw [key]
    refine HeQ.upleaf_deep_coreD hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 f
      (Fr_farWt _ _ _) (Fr_fwH _ _ _ _ _) (Hd_fwH _ _ _ _ _) (by simp [fwH])
      (D := [((1,q0+2,0):ℕ×ℕ×ℕ)]) (d0 := 2) (m := q0+2) (q := q0+1) (d := 1)
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; omega)
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact le_refl _)
      (by omega) (by omega) (by omega) ?_
    intro m' hm'
    obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    rw [show ([((1,q0+2,0):ℕ×ℕ×ℕ)] ++ [((2,q0+2,0):ℕ×ℕ×ℕ)])
        = [((1,q0+2,0):ℕ×ℕ×ℕ),((2,q0+2,0):ℕ×ℕ×ℕ)] from rfl, HeU.tow_eq_chT_dtree b u q0]
    have hgd := (HeI.GoodChtX_snocT hAo hA01 ho hL (HeU.TreeOKs_dtree u j)).2 g S o' f b hE hub ws hC hR
    have hreldt : (Lds ++ [[HeT.dtree j]]).map (relTs A0 (fun _ => 0) g u)
        = Lds.map (relTs A0 (fun _ => 0) g u) ++ [[HeT.dtree j]] := by
      simp only [List.map_append, List.map_cons, List.map_nil, relTs, HeU.relT_dtree A0 (fun _ => 0) g u j]
    rw [hreldt, hq0, farWt_snoc] at hgd
    have key2 : fwH b (q0+1) (FTLt b (q0+1) u
          (Lds.map (relTs A0 (fun _ => 0) g u) ++ [[HeT.dtree j]])) u []
        = fwH b (q0+1) (FTLt b (q0+1) u (Lds.map (relTs A0 (fun _ => 0) g u))) u []
          ++ shiftr01 1 0 (shiftr01 1 0 (((0,q0+1,0):ℕ×ℕ×ℕ) :: chT b (q0+1) u [HeT.dtree j])) := by
      simp [fwH, FTLt_snoc, shiftr01, mlift_nil]
    rw [key2] at hgd
    exact hgd

theorem WOK_snoc_deep {v : ℕ} {Uss : List (List UT)} (h : WOK v Uss) :
    WOK v (Uss ++ [[HdA.UT.tie 1 [HdA.UT.tie 1 []]]]) := by
  refine ⟨fun us hus => ?_, fun u hu => ?_⟩
  · rcases List.mem_append.mp hus with hus | hus
    · exact h.1 us hus
    · simp only [List.mem_singleton] at hus; subst hus; exact TRawLs_deep v _ (by simp [p1])
  · have e : (Uss ++ [[HdA.UT.tie 1 [HdA.UT.tie 1 []]]]).map farTs
        = Uss.map farTs ++ [[HdA.UT.tie 1 [HdA.UT.tie 1 []]]] := by simp [farTs, farT]
    rw [e]
    exact GoodChtX_snoc_deep (by simp) (by simp) (by decide) (h.2 u hu)

/-- ★★ 良い接頭辞 Uss（WOK, GoodTTL）の後ろに深い葉の子の並びを足した語は、文脈 CLTL で良い。 -/
theorem deep_after (u : ℕ) (Uss : List (List UT)) (hU : WOK u Uss) (hG : HeL.GoodTTL u Uss) :
    GTC CLTL u (wLT u (Uss ++ [[HdA.UT.tie 1 [HdA.UT.tie 1 []]]], ([] : List (Option TrioSeq)))) := by
  have e : wLT u (Uss ++ [[HdA.UT.tie 1 [HdA.UT.tie 1 []]]], ([] : List (Option TrioSeq)))
      = wLT u (Uss, []) ++ shiftr01 0 0 (shiftr01 1 0
        (((0, u+1, 0) : ℕ×ℕ×ℕ) :: ([((1,u+2,0):ℕ×ℕ×ℕ)] ++ [((2, u+2, 0) : ℕ×ℕ×ℕ)]))) := by
    simp [wLT, FTL0_snoc, topTs, topT, unitsC, shiftr01]
  rw [e]
  refine HeN.upleaf_deep_coreDT (C := CLTL) (u := u) (d := 0) (q := u+1) (d0 := 2) (m := u+2)
    (D := [(1,u+2,0)]) (by intro p hp; simp at hp; subst hp; simp)
    (by intro p hp; simp at hp; subst hp; simp) (by decide) (by omega) (by omega) (fun m' hm' => ?_)
  obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
  have ee : wLT u (Uss, []) ++ shiftr01 0 0 (shiftr01 1 0
      (tow (u+1) 0 ([((1,u+2,0):ℕ×ℕ×ℕ)] ++ [((2,u+2,0):ℕ×ℕ×ℕ)]) (j+1)))
      = wLT u (Uss ++ [[HeT.dtree j]], ([] : List (Option TrioSeq))) := by
    rw [show ([((1,u+2,0):ℕ×ℕ×ℕ)] ++ [((2,u+2,0):ℕ×ℕ×ℕ)]) = [((1,u+2,0):ℕ×ℕ×ℕ),((2,u+2,0):ℕ×ℕ×ℕ)] from rfl,
      HeU.tow_dtreeQ u j, topTs_dtreeQ u j]
    simp [wLT, FTL0_snoc, topTs, unitsC, shiftr01]
  rw [ee]
  have hG2 := HeL.GdT_good HeL.TPSOK_TP0 (HeN.GdT_treeTP0 (TreeTs_dtree_u u j)) le_rfl hU hG
    (HeL.TPNil_TP0 u)
  have e2 : Uss ++ [HeB.plugQ [] [HeT.dtree j]] = Uss ++ [[HeT.dtree j]] := by simp [HeB.plugQ]
  rw [e2] at hG2
  exact hG2 u le_rfl

theorem GoodTTL_deep_after {u : ℕ} {Uss : List (List UT)} (hU : WOK u Uss) (hG : HeL.GoodTTL u Uss) :
    HeL.GoodTTL u (Uss ++ [[HdA.UT.tie 1 [HdA.UT.tie 1 []]]]) :=
  fun u' hu' => deep_after u' Uss (WOK_mono hu' hU) (fun u'' hu'' => hG u'' (le_trans hu' hu''))

/-- ★ 深い葉の子の並びを n 個並べた語は良い。 -/
theorem rep_deep (n : ℕ) :
    WOK 0 (List.replicate n [HdA.UT.tie 1 [HdA.UT.tie 1 []]]) ∧
      HeL.GoodTTL 0 (List.replicate n [HdA.UT.tie 1 [HdA.UT.tie 1 []]]) := by
  induction n with
  | zero => exact ⟨WOK_of_TreeTs (fun _ h => by simp at h), HeN.GoodTTL_nil 0⟩
  | succ n ih =>
      rw [List.replicate_succ']
      exact ⟨WOK_snoc_deep ih.1, GoodTTL_deep_after ih.1 ih.2⟩

/-- ★ R_pm ＋ シート行 1672 の尾: (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(3,0,0) ∈ W 0。
    展開は深い葉の子の並びを n+1 個並べた語（gtc_flat + rep_deep）。 -/
theorem Rpm_1672 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(3,0,0)] : TrioSeq) ∈ W 0 := by
  have hG : GTC CLTL 0 (([(1,1,1)] : TrioSeq) ++ [((1,1,0):ℕ×ℕ×ℕ), (2,2,0), (3,2,0)] ++ [((1 + 1, 0, 0) : ℕ×ℕ×ℕ)]) := by
    refine HdR.gtc_flat (C := CLTL) (d := 1) (by simp) rfl ?_ (fun n => ?_)
    · intro r hr1 hr2
      simp only [List.length_cons, List.length_nil] at hr2
      rcases (show r = 1 ∨ r = 2 by omega) with rfl | rfl <;> simp [entry]
    · have := (rep_deep n).2 0 le_rfl
      have e : wLT 0 (List.replicate n [HdA.UT.tie 1 [HdA.UT.tie 1 []]], ([] : List (Option TrioSeq)))
          = ([(1,1,1)] : TrioSeq) ++ (List.range n).flatMap (fun _ => [((1,1,0):ℕ×ℕ×ℕ), (2,2,0), (3,2,0)]) := by
        have := FTL0_rep 1 [] (topTs 0 [HdA.UT.tie 1 [HdA.UT.tie 1 []]]) n
        simp only [List.nil_append] at this
        simp only [wLT, List.map_replicate, unitsC, List.append_nil]
        rw [this]
        simp [FTL0, topTs, topT, shiftr01]
      rwa [e] at this
  have hS : StarOK 0 (rword 0 0 [([(1,1,1)] : TrioSeq) ++ [((1,1,0):ℕ×ℕ×ℕ), (2,2,0), (3,2,0)] ++ [((1 + 1, 0, 0) : ℕ×ℕ×ℕ)]]) := by
    refine ⟨?_, fun p hp => rword_ge 0 0 _ p hp⟩
    have hB := hG [] ⟨[], PsLd_of_PsLTL (PsLTL_nil 0), rfl⟩ (by simp) (BwT_nil 0)
    have h2 := hB 0 le_rfl
    rw [Nat.sub_self] at h2
    simpa only [mlift_zero, List.map_cons, List.map_nil, List.nil_append] using h2
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK hS)
  simpa [rword, rcol, shiftr01] using h

/-! ## 遠い像側: [深い葉] は最上段の道の集合 PNil で Gd -/

/-- ★★ 一般の級 (C, o, f) で、良い子の並び Lds の後ろに [深い葉] を置いた最後の語は GpT。 -/
theorem BotT_deep {C : List ℕ} {o : ℕ} {f : ℕ → ℕ} {u : ℕ} (hCo : ∀ a ∈ C, a < o)
    (hC1 : ∀ a ∈ C, 1 ≤ a) (ho : 1 ≤ o) {Lds : List (List UT)} (hL : GoodChtX C o f u Lds) :
    HeB.BotT C o f u Lds [] [HdA.UT.tie 1 [HdA.UT.tie 1 []]] := by
  intro b hub ws hC hR
  rw [show HeB.plugQ [] [HdA.UT.tie 1 [HdA.UT.tie 1 []]] = [HdA.UT.tie 1 [HdA.UT.tie 1 []]] from rfl,
    farWt_snoc]
  obtain ⟨q0, hq0⟩ : ∃ q0, b + liftOff f C o + 1 = q0 + 1 := ⟨b + liftOff f C o, rfl⟩
  rw [hq0]
  have key : fwH b (q0+1) (FTLt b (q0+1) u (Lds ++ [[HdA.UT.tie 1 [HdA.UT.tie 1 []]]])) u []
      = fwH b (q0+1) (FTLt b (q0+1) u Lds) u []
        ++ shiftr01 1 0 (shiftr01 1 0 (((0,q0+1,0):ℕ×ℕ×ℕ) :: ([((1,q0+2,0):ℕ×ℕ×ℕ)] ++ [((2,q0+2,0):ℕ×ℕ×ℕ)]))) := by
    simp [fwH, FTLt_snoc, chT, unitT, shiftr01, mlift_nil]
  rw [key]
  refine HeQ.upleaf_deep_coreD hCo hC1 ho f
    (Fr_farWt _ _ _) (Fr_fwH _ _ _ _ _) (Hd_fwH _ _ _ _ _) (by simp [fwH])
    (D := [((1,q0+2,0):ℕ×ℕ×ℕ)]) (d0 := 2) (m := q0+2) (q := q0+1) (d := 1)
    (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; omega)
    (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact le_refl _)
    (by omega) (by omega) (by omega) ?_
  intro m' hm'
  obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
  rw [show ([((1,q0+2,0):ℕ×ℕ×ℕ)] ++ [((2,q0+2,0):ℕ×ℕ×ℕ)])
      = [((1,q0+2,0):ℕ×ℕ×ℕ),((2,q0+2,0):ℕ×ℕ×ℕ)] from rfl, HeU.tow_eq_chT_dtree b u q0]
  have hL0 : GoodChtX ([] ++ C) o f u Lds := by simpa using hL
  have hL2 := HeC.Gd_P0_good (HeI.Gd_treeP0 hC1 ho hCo f (HeU.TreeOKs_dtree u j))
    (HcM.EmbU_triv hCo hC1 ho f) le_rfl hL0
  rw [HeB.imgT_zero] at hL2
  have hgd := hL2.2 (fun _ => 0) [] o f b (HcM.EmbU_triv hCo hC1 ho f) hub ws
    (by simpa using hC) (by simpa using hR)
  have hmap : ∀ L : List (List UT), L.map (relTs C f (fun _ => 0) u) = L := by
    intro L
    induction L with
    | nil => rfl
    | cons x L ih => simp only [List.map_cons, HdA.relTs_zero C f u x, ih]
  simp only [List.nil_append] at hgd
  rw [hmap (Lds ++ [[HeT.dtree j]]), hq0, farWt_snoc] at hgd
  have key2 : fwH b (q0+1) (FTLt b (q0+1) u (Lds ++ [[HeT.dtree j]])) u []
      = fwH b (q0+1) (FTLt b (q0+1) u Lds) u []
        ++ shiftr01 1 0 (shiftr01 1 0 (((0,q0+1,0):ℕ×ℕ×ℕ) :: chT b (q0+1) u [HeT.dtree j])) := by
    simp [fwH, FTLt_snoc, shiftr01, mlift_nil]
  rw [key2] at hgd
  exact hgd

theorem imgT_deep (A : List ℕ) (H G : ℕ → ℕ) (c u : ℕ) :
    HeB.imgT A H G c u [HdA.UT.tie 1 [HdA.UT.tie 1 []]] = [HdA.UT.tie 1 [HdA.UT.tie 1 []]] := by
  simp [HeB.imgT, mlTs, mlT, relTs, relT]

/-- ★★ [深い葉] は最上段の道の集合 PNil で Gd。 -/
theorem Gd_deep {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} :
    HeB.Gd HeC.PNil A k H c [HdA.UT.tie 1 [HdA.UT.tie 1 []]] := by
  refine ⟨by simp [RawTs, RawT], fun G S o f hE u _ Lds hL Q hQ => ?_⟩
  simp only [HeC.PNil] at hQ; subst hQ
  rw [imgT_deep]
  exact BotT_deep hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 hL

/-! ## GTC 側: 深い葉の後ろに荷を足す（HeM.GdT_load の最上段の場合の写し） -/

/-- 子の並び x は、全ての段 u ≥ v・全ての良い接頭辞 Uss の後ろで良い（最上段の道 [] での BotCL）。 -/
def DL (v : ℕ) (x : List UT) : Prop :=
  ∀ u, v ≤ u → ∀ Uss, WOK u Uss → HeL.GoodTTL u Uss → HeL.BotCL u Uss [] x

/-- 子の並び x は TRawLs で、遠い像が最上段の道の集合 PNil で Gd（WOK を延ばせる）。 -/
def WC (v : ℕ) (x : List UT) : Prop :=
  TRawLs v x ∧ ∀ u, v ≤ u → HeB.Gd HeC.PNil [] 1 (fun _ => 0) u (farTs x)

theorem WOK_snoc_WC {v u : ℕ} (hvu : v ≤ u) {Uss : List (List UT)} {x : List UT} (hU : WOK u Uss)
    (hx : WC v x) : WOK u (Uss ++ [x]) := by
  refine ⟨fun us hus => ?_, fun u' hu' => ?_⟩
  · rcases List.mem_append.mp hus with hus | hus
    · exact hU.1 us hus
    · simp only [List.mem_singleton] at hus; subst hus; exact TRawLs_mono hvu _ hx.1
  · have hL : GoodChtX ([] ++ []) 1 (fun _ => 0) u' (Uss.map farTs) := by simpa using hU.2 u' hu'
    have := HeB.Gd_good HeC.PSOK_PNil (hx.2 u' (le_trans hvu hu'))
      (HcM.EmbU_triv (A := []) (by simp) (by simp) (by decide) (fun _ => 0)) le_rfl hL
      (show HeC.PNil ([] ++ []) 1 (fun _ => 0) u' [] from rfl)
    rw [List.map_append, List.map_singleton]
    simpa [HeB.plugQ, HeB.imgT_zero] using this

theorem GoodTTL_of_DL {v u : ℕ} (hvu : v ≤ u) {Uss : List (List UT)} {x : List UT} (hx : DL v x)
    (hU : WOK u Uss) (hG : HeL.GoodTTL u Uss) : HeL.GoodTTL u (Uss ++ [x]) := by
  intro u' hu'
  have := hx u' (le_trans hvu hu') Uss (WOK_mono hu' hU) (fun u'' hu'' => hG u'' (le_trans hu' hu''))
  exact this

theorem DL_deep (v : ℕ) : DL v [HdA.UT.tie 1 [HdA.UT.tie 1 []]] :=
  fun u _ Uss hU hG => deep_after u Uss hU hG

theorem WC_deep (v : ℕ) : WC v [HdA.UT.tie 1 [HdA.UT.tie 1 []]] :=
  ⟨by simp [TRawLs, TRawL], fun u _ => by simpa [farTs, farT] using Gd_deep⟩

theorem WC_snoc_ch {v : ℕ} {pre : List UT} (hp : WC v pre) {Z : TrioSeq} (hZ : Z ∈ Wg (2 * v))
    (hb : based Z) : WC v (pre ++ [UT.ch Z]) := by
  refine ⟨TRawLs_append.mpr ⟨hp.1, by simp [TRawLs, TRawL]; exact ⟨hZ, hb⟩⟩, fun u hu => ?_⟩
  rw [HdR.farTs_append]
  have hZu : Z ∈ Wg (2 * u) := Wg_mono (by omega) hZ
  have hX : HeG.okLowP u (shiftr01 1 0 Z) := by simpa using HeG.okLowP_load (HeG.okLowP_nil u) hZu hb
  simpa [farTs, farT] using
    HeI.Gd_snoc_ch HeC.PSOK_PNil HeC.PSDec_PNil (by simp) (le_refl 1) (hp.2 u hu) hX

/-- ★★ 最上段で、良い子の並び pre（DL, WC）の後ろに荷 ch Z を足しても良い。 -/
theorem DL_snoc_ch {v : ℕ} :
    ∀ Z ∈ Wg (2 * v), based Z → ∀ pre : List UT, DL v pre → WC v pre → DL v (pre ++ [UT.ch Z]) := by
  have key := based_Wg_ind (u := v)
    (Q := fun Z => Z ∈ Wg (2 * v) → ∀ pre : List UT, DL v pre → WC v pre → DL v (pre ++ [UT.ch Z]))
    ?_ ?_ ?_ ?_
  · exact fun Z hZ hb => key Z hZ hb hZ
  · -- nil
    intro _ pre hD _ u hu Uss hU hG
    have := hD u hu Uss hU hG
    rw [HeL.BotCL_word] at this ⊢
    rwa [HdS.topTs_snoc_ch, show shiftr01 1 0 ([] : TrioSeq) = [] from rfl, List.append_nil]
  · -- flat
    intro Z hZW hbZ hIH hZW' pre hD hW u hu Uss hU hG
    have hDZ := hIH hZW pre hD hW
    have hWZ := WC_snoc_ch hW hZW hbZ
    have hVF : Fr (topTs u pre ++ shiftr01 1 0 Z) := Fr_append (Fr_topTs _ _) (Fr_shift1 Z)
    rw [HeL.BotCL_word, HdS.topTs_snoc_ch]
    obtain ⟨M, hM⟩ : ∃ M : TrioSeq,
        M = ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u pre ++ shiftr01 1 0 Z) := ⟨_, rfl⟩
    have eW : wLT u (Uss ++ [HeB.plugQ [] []], []) ++
          shiftr01 (([] : HeB.Path).length + 1) 0
            (topTs u pre ++ shiftr01 1 0 (Z ++ [((0, 0, 0) : ℕ × ℕ × ℕ)]))
        = FTL0 (u + 1) (Uss.map (topTs u)) ++ M ++ [((1 + 1, 0, 0) : ℕ × ℕ × ℕ)] := by
      rw [hM]; simp [wLT, FTL0_snoc, HeB.plugQ, topTs, unitsC, shiftr01]
    rw [eW]
    refine HdR.gtc_flat (by rw [hM]; simp) (by rw [hM]; rfl) ?_ (fun n => ?_)
    · intro r' hr1 hr2
      obtain ⟨w, rfl⟩ : ∃ w, r' = w + 1 := ⟨r' - 1, by omega⟩
      have hw : w < (topTs u pre ++ shiftr01 1 0 Z).length := by
        rw [hM] at hr2; simp only [List.length_cons, shiftr01_length] at hr2; omega
      rw [hM, entry_cons, entry0_shiftr01 hw]
      have := getD_row0_ge hVF hw
      omega
    · have hGn : ∀ n, WOK u (Uss ++ List.replicate n (pre ++ [UT.ch Z])) ∧
          HeL.GoodTTL u (Uss ++ List.replicate n (pre ++ [UT.ch Z])) := by
        intro n
        induction n with
        | zero => simpa using And.intro hU hG
        | succ n ih =>
            rw [List.replicate_succ', ← List.append_assoc]
            exact ⟨WOK_snoc_WC hu ih.1 hWZ, GoodTTL_of_DL hu hDZ ih.1 ih.2⟩
      have := (hGn n).2 u le_rfl
      have eR : wLT u (Uss ++ List.replicate n (pre ++ [UT.ch Z]), [])
          = FTL0 (u + 1) (Uss.map (topTs u)) ++ (List.range n).flatMap (fun _ => M) := by
        show FTL0 (u + 1) ((Uss ++ List.replicate n (pre ++ [UT.ch Z])).map (topTs u)) ++
          unitsC u ([] : List (Option TrioSeq)) = _
        rw [show unitsC u ([] : List (Option TrioSeq)) = [] from rfl, List.append_nil, List.map_append,
          List.map_replicate, FTL0_rep, HdS.topTs_snoc_ch, hM]
      rwa [eR] at this
  · -- oper
    intro Z hZW hbZ hlen hp hIH hZW' pre hD hW u hu Uss hU hG
    rw [HeL.BotCL_word, HdS.topTs_snoc_ch, shiftr01_append0, shiftr01_add0, ← List.append_assoc]
    refine HdR.gtc_oper hlen hp (fun n hn => ?_)
    have := (hIH n hn).2 (hIH n hn).1 pre hD hW u hu Uss hU hG
    rwa [HeL.BotCL_word, HdS.topTs_snoc_ch, shiftr01_append0, shiftr01_add0, ← List.append_assoc] at this
  · -- orph
    intro Z h j hZW hbZ hj1 hjv hnp hz hZW' pre hD hW u hu Uss hU hG
    rw [HeL.BotCL_word, HdS.topTs_snoc_ch]
    have eU : topTs u pre ++ shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])
        = (topTs u pre ++ shiftr01 1 0 Z) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by simp [shiftr01]
    rw [eU]
    have hHP : Hd (shiftr01 1 0 (Z ++ [((h, j, 0) : ℕ × ℕ × ℕ)])) := HcS.Hd_shift1_based hbZ
    refine HdR.gtc_orph (HeL.PathCone_YtopL u Uss [] (fun q hq => by simp at hq))
      (by rw [← eU]; exact Hd_app (Hd_topTLs u pre (TRawLs_mono hu pre hW.1)) hHP) hj1 (by omega) ?_
      (fun z hz' hbz => ?_)
    · have hlen : (topTs u pre ++ shiftr01 1 0 Z).length = (topTs u pre).length + Z.length := by
        simp only [List.length_append, shiftr01_length]
      rw [← eU, hlen, hasParent_append_gen (by simp [shiftr01])
        (rsum_of_Hd (Fr_topTs _ _) (Fr_shift1 _) hHP), hasParent_shiftr01]
      exact hnp
    · have hzz := (hz z hz' hbz).2 (hz z hz' hbz).1 pre hD hW u hu Uss hU hG
      rw [HeL.BotCL_word, HdS.topTs_snoc_ch] at hzz
      have ez : topTs u pre ++ shiftr01 1 0 (Z ++ shiftr01 h 0 z)
          = (topTs u pre ++ shiftr01 1 0 Z) ++ shiftr01 (h + 1) 0 z := by
        rw [shiftr01_append0, shiftr01_add0, List.append_assoc]
      rwa [ez] at hzz

theorem DL_mono {v v' : ℕ} (h : v ≤ v') {x : List UT} (hx : DL v x) : DL v' x :=
  fun u hu => hx u (le_trans h hu)

theorem WC_mono {v v' : ℕ} (h : v ≤ v') {x : List UT} (hx : WC v x) : WC v' x :=
  ⟨TRawLs_mono h x hx.1, fun u hu => hx.2 u (le_trans h hu)⟩

theorem WC_tieE {v : ℕ} {pre : List UT} (hp : WC v pre) : WC v (pre ++ [UT.tie 0 []]) := by
  refine ⟨TRawLs_append.mpr ⟨hp.1, by simp [TRawLs, TRawL]⟩, fun u hu => ?_⟩
  rw [HdR.farTs_append]
  simpa [farTs, farT] using HeG.Gd_tieE HeC.PSOK_PNil HeC.PSDec_PNil (hp.2 u hu)

/-- ★★ 最上段で、良い子の並び pre の後ろに空の tie 0 を足しても良い（HeM.GdT_tieE の写し）。 -/
theorem DL_tieE {v : ℕ} {pre : List UT} (hD : DL v pre) (hW : WC v pre) :
    DL v (pre ++ [UT.tie 0 []]) := by
  intro u' hu' Uss hU hG
  rw [HeL.BotCL_word]
  have eT : topTs u' (pre ++ [UT.tie 0 []]) = topTs u' pre ++ [((1, u' + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [topTs_append, topTs, topT, shiftr01]
  rw [eT]
  have hQr : ∀ q ∈ ([] : HeB.Path), TRawLs u' q.1 := fun q hq => by simp at hq
  have hraw : TRawLs u' pre := TRawLs_mono hu' pre hW.1
  refine HdR.gtc_tie (HeL.PathCone_YtopL u' Uss [] hQr) (Fr_append (Fr_topTs _ _) (GzF.Fr_single le_rfl _ _))
    (Hd_app (Hd_topTLs u' pre hraw) (fun _ => rfl)) (coneV_top (Fr_topTs _ _) u')
    (fun u'' hu'' Z hZ hbZ => ?_) (fun L hC u3 hu3 => CLTL_lift L u' hC u3 hu3)
  rw [HeL.mlift_YtopL hu'' hU.1 hQr,
    mlift_topTLs pre hraw u' le_rfl (u'' - u'), show u' + (u'' - u') = u'' by omega]
  have hD2 := DL_snoc_ch (v := u'') Z hZ hbZ pre (DL_mono (le_trans hu' hu'') hD)
    (WC_mono (le_trans hu' hu'') hW)
  have := hD2 u'' le_rfl Uss (WOK_mono hu'' hU) (fun u3 hu3 => hG u3 (le_trans hu'' hu3))
  rwa [HeL.BotCL_word, HdS.topTs_snoc_ch] at this

/-! ## 族: 先頭の語の最初の子の並びが x（DL, WC） -/

theorem GoodTTL_first {x : List UT} (hD : DL 0 x) (hW : WC 0 x) :
    ∀ Uss : List (List UT), (∀ us ∈ Uss, TreeTs 0 0 true us) →
      WOK 0 ([x] ++ Uss) ∧ HeL.GoodTTL 0 ([x] ++ Uss) := by
  intro Uss
  induction Uss using List.reverseRecOn with
  | nil =>
      intro _
      have h0 : WOK 0 ([] : List (List UT)) := WOK_of_TreeTs (fun _ h => by simp at h)
      have := GoodTTL_of_DL le_rfl hD h0 (HeN.GoodTTL_nil 0)
      exact ⟨by simpa using WOK_snoc_WC le_rfl h0 hW, by simpa using this⟩
  | append_singleton Uss us ih =>
      intro h
      have h' : ∀ us' ∈ Uss, TreeTs 0 0 true us' := fun us' hus' => h us' (List.mem_append_left _ hus')
      have hus := h us (List.mem_append_right _ (List.mem_singleton_self _))
      obtain ⟨hWk, hGt⟩ := ih h'
      refine ⟨by rw [← List.append_assoc]; exact WOK_snoc hWk hus, ?_⟩
      have := HeL.GdT_good HeL.TPSOK_TP0 (HeN.GdT_treeTP0 hus) le_rfl hWk hGt (HeL.TPNil_TP0 0)
      have e : ([x] ++ Uss) ++ [HeB.plugQ [] us] = [x] ++ (Uss ++ [us]) := by simp [HeB.plugQ]
      rwa [e] at this

/-- ★★ 先頭の語（子の並び x ＋ 段つきの木の子の並び Uss0、荷 us0）のあとに段つきの木の語の並び qs。 -/
theorem BwT_first {x : List UT} (hD : DL 0 x) (hW : WC 0 x)
    (Uss0 : List (List UT)) (hU0 : ∀ us ∈ Uss0, TreeTs 0 0 true us)
    (us0 : List (Option TrioSeq)) (hNT : GzJ.NoTie us0) (hR : RawU 0 us0) :
    ∀ qs : List (List (List UT) × List (Option TrioSeq)),
    PsLTL 0 qs → BwT 0 ((([x] ++ Uss0, us0) :: qs).map (wLT 0)) := by
  obtain ⟨hWk, hGt⟩ := GoodTTL_first hD hW Uss0 hU0
  intro qs
  induction qs using List.reverseRecOn with
  | nil =>
      intro _
      have := GTC_wLTLw hWk hGt us0 hNT hR [] ⟨[], PsLd_of_PsLTL (PsLTL_nil 0), rfl⟩ (by simp) (BwT_nil 0)
      simpa using this
  | append_singleton qs q ih =>
      intro h
      have h' : PsLTL 0 qs := fun r hr => h r (List.mem_append_left _ hr)
      have hq := h q (List.mem_append_right _ (List.mem_singleton_self _))
      have hG := HeN.GTC_wLTL hq.1 (HeN.GoodTTL_all q.1 hq.1) q.2 hq.2.1 hq.2.2
      have hC : PsLd 0 (([x] ++ Uss0, us0) :: qs) := by
        have := PsLd_append (PsLd_word hWk hNT hR) (PsLd_of_PsLTL h')
        simpa using this
      have := hG _ ⟨([x] ++ Uss0, us0) :: qs, hC, rfl⟩ (Fr_CLT 0 (([x] ++ Uss0, us0) :: qs)) (ih h')
      simpa [List.map_append] using this

theorem starOK_first {x : List UT} (hD : DL 0 x) (hW : WC 0 x)
    (Uss0 : List (List UT)) (hU0 : ∀ us ∈ Uss0, TreeTs 0 0 true us)
    (us0 : List (Option TrioSeq)) (hNT : GzJ.NoTie us0) (hR : RawU 0 us0)
    (qs : List (List (List UT) × List (Option TrioSeq))) (h : PsLTL 0 qs)
    {Ls : List TrioSeq} (hW' : WordsG 0 Ls) :
    StarOK 0 (rword 0 0 ((([x] ++ Uss0, us0) :: qs).map (wLT 0) ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 0 _ p hp⟩
  have hB := BwT_append_words (Fr_CLT 0 (([x] ++ Uss0, us0) :: qs)) (BwT_first hD hW Uss0 hU0 us0 hNT hR qs h)
    Ls hW' 0 le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

/-- ★ 族: 先頭の語（子の並び x ＋ Uss0、荷 us0）＋ 語の並び qs ＋ 遠い語 Ls ＋ 吊るした荷 Z。 -/
theorem first_hang {x : List UT} (hD : DL 0 x) (hW : WC 0 x)
    (Uss0 : List (List UT)) (hU0 : ∀ us ∈ Uss0, TreeTs 0 0 true us)
    (us0 : List (Option TrioSeq)) (hNT : GzJ.NoTie us0) (hR : RawU 0 us0)
    (qs : List (List (List UT) × List (Option TrioSeq))) (h : PsLTL 0 qs)
    {Ls : List TrioSeq} (hW' : WordsG 0 Ls) {u : ℕ} {Z : TrioSeq} (hZ : Z ∈ Wg u) (hb : based Z) :
    (((0, 0, 0) : ℕ×ℕ×ℕ) :: (rword 0 0 ((([x] ++ Uss0, us0) :: qs).map (wLT 0) ++ Ls) ++ shiftr01 1 0 Z))
      ∈ W 0 :=
  GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_first hD hW Uss0 hU0 us0 hNT hR qs h hW') hZ hb))

/-- ★ R_pm ＋ シート行 1673 の尾: (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(3,1,0) ∈ W 0。 -/
theorem Rpm_1673 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(3,1,0)] : TrioSeq) ∈ W 0 := by
  have hS := starOK_first (x := [HdA.UT.tie 1 [HdA.UT.tie 1 []], UT.tie 0 []])
    (by simpa using DL_tieE (DL_deep 0) (WC_deep 0)) (by simpa using WC_tieE (WC_deep 0))
    [] (fun _ h => by simp at h) [] (by simp [GzJ.NoTie]) (RawU_nil 0) [] (PsLTL_nil 0) (WordsG_nil 0)
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK hS)
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01] using h

/-- ★ R_pm ＋ シート行 1674 の尾: (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(3,1,0)(1,1,1)(2,1,1) ∈ W 0。 -/
theorem Rpm_1674 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(3,1,0),(1,1,1),(2,1,1)] : TrioSeq) ∈ W 0 := by
  have hS := starOK_first (x := [HdA.UT.tie 1 [HdA.UT.tie 1 []], UT.tie 0 []])
    (by simpa using DL_tieE (DL_deep 0) (WC_deep 0)) (by simpa using WC_tieE (WC_deep 0))
    [] (fun _ h => by simp at h) [] (by simp [GzJ.NoTie]) (RawU_nil 0) [p0]
    (PsLTL_cons (fun _ h => by simp [p0] at h) (by simp [p0, GzJ.NoTie]) (RawU_nil 0) (PsLTL_nil 0))
    (WordsG_nil 0)
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK hS)
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01, p0] using h

/-! ## 壁 A の基盤 (G): 閉じた道の集合の全ての道で、並びの先頭に深い葉 -/

/-- ★★★ 道の集合 P（TPSOK, TExt で閉じる, TLast）で空の並びが GdT なら、P の全ての道 Q で
    [深い葉] を置いた語は良い。GdT_upleaf と同じ描画で upleaf_deep_coreDT、dtree 側は GdT_treeL。 -/
theorem BotCL_deep {P : HeL.TPS} (hP : HeL.TPSOK P 0 true) (hD : HeL.TPSDec P 0 true)
    (hcl : HeL.TExt P 0 true 0 P) (hlast : HeL.TLast P 0) {v : ℕ} (hnil : HeL.GdT P 0 true v []) :
    ∀ u, v ≤ u → ∀ Uss, WOK u Uss → HeL.GoodTTL u Uss → ∀ Q, P u Q →
      HeL.BotCL u Uss Q [HdA.UT.tie 1 [HdA.UT.tie 1 []]] := by
  intro u hu Uss hU hG Q hQ
  have hdt : ∀ j, HeL.BotCL u Uss Q [HeT.dtree j] := by
    intro j
    have := HeN.GdT_treeL [HeT.dtree j] P 0 true hP hD hlast (fun _ => ⟨rfl, hcl⟩) v [] (TreeTs_dtree_u v j) hnil
    exact this.2 u hu Uss hU hG Q hQ
  have eD : ∀ u' : ℕ, shiftr01 1 0 (topTs u' [HdA.UT.tie 1 [HdA.UT.tie 1 []]])
      = shiftr01 1 0 ([((1,u'+2,0):ℕ×ℕ×ℕ)] ++ [((2,u'+2,0):ℕ×ℕ×ℕ)]) := by
    intro u'; simp [topTs, topT, shiftr01]
  rcases List.eq_nil_or_concat Q with rfl | ⟨Q', ⟨v', p'⟩, rfl⟩
  · have eW : ∀ T : List UT, HeL.BotCL u Uss [] T
        = GTC CLTL u (FTL0 (u + 1) (Uss.map (topTs u)) ++ shiftr01 0 0
            (((1, u + 1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u T))) := by
      intro T
      show GTC CLTL u (wLT u (Uss ++ [T], [])) = _
      rw [shiftr01_zero', Nat.add_zero]
      simp only [wLT, List.map_append, List.map_singleton, FTL0_snoc]
      rw [show unitsC u ([] : List (Option TrioSeq)) = [] from rfl, List.append_nil]
    rw [eW, eD u]
    refine HeN.upleaf_deep_coreDT (C := CLTL) (u := u) (d := 0) (q := u+1) (d0 := 2) (m := u+2)
      (D := [(1,u+2,0)]) (by intro p hp; simp at hp; subst hp; simp)
      (by intro p hp; simp at hp; subst hp; simp) (by decide) (by omega) (by omega) (fun m' hm' => ?_)
    obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    have := hdt j
    rw [eW] at this
    rw [show ([((1,u+2,0):ℕ×ℕ×ℕ)] ++ [((2,u+2,0):ℕ×ℕ×ℕ)]) = [((1,u+2,0):ℕ×ℕ×ℕ),((2,u+2,0):ℕ×ℕ×ℕ)] from rfl,
      HeU.tow_dtreeQ u j, topTs_dtreeQ u j]
    simpa [shiftr01] using this
  · simp only [List.concat_eq_append] at hQ hdt ⊢
    have hp' : p' = 0 := by have := hlast u _ hQ; rwa [HeC.lastL_snoc] at this
    subst hp'
    have eW : ∀ T : List UT, HeL.BotCL u Uss (Q' ++ [(v', 0)]) T
        = GTC CLTL u ((wLT u (Uss ++ [HeB.plugQ Q' []], []) ++ shiftr01 (Q'.length + 1) 0 (topTs u v')) ++
            shiftr01 (Q'.length + 1) 0
              (((1, u + 1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (topTs u T))) := by
      intro T
      rw [HeL.BotCL_snoc_eq, HeL.BotCL_word, HeM.topTs_snoc_tieL, shiftr01_append0, List.append_assoc]
    rw [eW, eD u]
    refine HeN.upleaf_deep_coreDT (C := CLTL) (u := u) (d := Q'.length + 1) (q := u+1) (d0 := 2) (m := u+2)
      (D := [(1,u+2,0)]) (by intro p hp; simp at hp; subst hp; simp)
      (by intro p hp; simp at hp; subst hp; simp) (by decide) (by omega) (by omega) (fun m' hm' => ?_)
    obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    have := hdt j
    rw [eW] at this
    rw [show ([((1,u+2,0):ℕ×ℕ×ℕ)] ++ [((2,u+2,0):ℕ×ℕ×ℕ)]) = [((1,u+2,0):ℕ×ℕ×ℕ),((2,u+2,0):ℕ×ℕ×ℕ)] from rfl,
      HeU.tow_dtreeQ u j, topTs_dtreeQ u j]
    simpa [shiftr01] using this

/-! ## 壁 A の基盤 (F): 遠い像側で、閉じた道の集合の全ての道で並びの先頭に深い葉 -/

theorem imgT_dtree (A : List ℕ) (H G : ℕ → ℕ) (c u : ℕ) (j : ℕ) :
    HeB.imgT A H G c u [HeT.dtree j] = [HeT.dtree j] := by
  induction j with
  | zero => simp [HeB.imgT, mlTs, mlT, relTs, relT, HeT.dtree]
  | succ j ih =>
      simp only [HeB.imgT, mlTs, relTs, List.cons.injEq, and_true] at ih ⊢
      simp [mlT, relT, HeT.dtree, mlTs, relTs]
      simpa [HeB.imgT, mlTs, relTs] using ih

theorem chT_deep (b r u : ℕ) :
    chT b r u [HdA.UT.tie 1 [HdA.UT.tie 1 []]] = [((1, r + 1, 0) : ℕ×ℕ×ℕ), ((2, r + 1, 0) : ℕ×ℕ×ℕ)] := by
  simp [chT, unitT, shiftr01]

/-- ★★★ 遠い像側: 道の集合 P（PSOK, PSDec, 段 0 の延長で閉じる, 最後の段 0）で空の並びが Gd なら、[深い葉] も Gd。 -/
theorem Gd_deep_gen {P : HeB.PS} (hP : HeB.PSOK P) (hD : HeC.PSDec P) (hcl : HeB.Ext P 0 P)
    (hlast : HeC.LastL P 0) {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k)
    (hAk : ∀ a ∈ A, a < k) {c : ℕ} (hnil : HeB.Gd P A k H c []) :
    HeB.Gd P A k H c [HdA.UT.tie 1 [HdA.UT.tie 1 []]] := by
  refine ⟨by simp [RawTs, RawT], fun G S o f hE u hcu Lds hL Q hQ => ?_⟩
  intro b hub ws hC hR
  have hA := hE.2.2.1
  have hA1 := hE.2.2.2.1
  have ho := hE.2.2.2.2.1
  rw [imgT_deep]
  have hT : ∀ j, HeB.Gd P A k H c [HeT.dtree j] := fun j => by
    have := HeI.Gd_treeL hA01 hk hAk H [HeT.dtree j] P 0 true hP hD hlast (fun _ => hcl) []
      (HeU.TreeOKs_dtree c j) hnil
    simpa using this
  have hrep : ∀ j, GpT (S ++ A) o f b (farWt b (b + liftOff f (S ++ A) o + 1)
      (ws ++ [(Lds ++ [HeB.plugQ Q [HeT.dtree j]], u, [])])) := by
    intro j
    have := (hT j).2 G S o f hE u hcu Lds hL Q hQ b hub ws hC hR
    rwa [imgT_dtree] at this
  obtain ⟨q0, hq0⟩ : ∃ q0, q0 = b + liftOff f (S ++ A) o := ⟨_, rfl⟩
  rw [← hq0] at hrep ⊢
  have htow : ∀ j, (tow (q0+1) 0 [((1,q0+1+1,0):ℕ×ℕ×ℕ),((2,q0+1+1,0):ℕ×ℕ×ℕ)] (j+1) : TrioSeq)
      = ((0,q0+1,0):ℕ×ℕ×ℕ) :: chT b (q0+1) u [HeT.dtree j] := fun j => HeU.tow_eq_chT_dtree b u q0 j
  rcases List.eq_nil_or_concat Q with rfl | ⟨Q', ⟨v, p'⟩, rfl⟩
  · obtain ⟨Yp, hYpd⟩ : ∃ Yp, Yp = ((1, q0+1, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FTLt b (q0+1) u Lds) := ⟨_, rfl⟩
    have eW : ∀ T : List UT, farWt b (q0+1) (ws ++ [(Lds ++ [HeB.plugQ [] T], u, [])])
        = farWt b (q0+1) ws ++ (Yp ++ shiftr01 1 0
            (((1, q0+1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b (q0+1) u T))) := by
      intro T
      rw [show HeB.plugQ [] T = T from rfl, farWt_snoc, hYpd]
      simp [fwH, FTLt_snoc, mlift_nil, shiftr01_append0]
    have hYpF : Fr Yp := by rw [hYpd]; exact Fr_letter _ _
    have hYpne : Yp ≠ [] := by rw [hYpd]; simp
    have hYpH : Hd Yp := by rw [hYpd]; exact fun _ => rfl
    rw [eW, chT_deep]
    have e1 : (((1, q0+1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 [((1, q0+1+1, 0) : ℕ×ℕ×ℕ), ((2, q0+1+1, 0) : ℕ×ℕ×ℕ)])
        = shiftr01 1 0 (((0, q0+1, 0) : ℕ×ℕ×ℕ) :: ([((1,q0+1+1,0):ℕ×ℕ×ℕ)] ++ [((2,q0+1+1,0):ℕ×ℕ×ℕ)])) := by
      simp [shiftr01]
    rw [e1]
    refine HeQ.upleaf_deep_coreD hA hA1 ho f (Fr_farWt _ _ _) hYpF hYpH hYpne
      (D := [((1,q0+1+1,0):ℕ×ℕ×ℕ)]) (d0 := 2) (m := q0+1+1) (q := q0+1) (d := 1)
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; omega)
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact le_refl _)
      (by omega) (by omega) (by omega) ?_
    intro m' hm'
    obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    rw [show ([((1,q0+1+1,0):ℕ×ℕ×ℕ)] ++ [((2,q0+1+1,0):ℕ×ℕ×ℕ)])
        = [((1,q0+1+1,0):ℕ×ℕ×ℕ),((2,q0+1+1,0):ℕ×ℕ×ℕ)] from rfl, htow j]
    have := hrep j
    rw [eW] at this
    simpa [shiftr01] using this
  · simp only [List.concat_eq_append] at hQ hrep ⊢
    have hp' : p' = 0 := by have := hlast _ _ _ _ _ hQ; rwa [HeC.lastL_snoc] at this
    subst hp'
    have hv := hP.raw _ _ _ _ _ hQ (v, 0) (by simp)
    obtain ⟨Yp, hYpd⟩ : ∃ Yp, Yp = fwH b (q0+1) (FTLt b (q0+1) u (Lds ++ [HeB.plugQ Q' []])) u [] ++
        shiftr01 (Q'.length + 2) 0 (chT b (q0+1) u v) := ⟨_, rfl⟩
    have eW : ∀ T : List UT, farWt b (q0+1) (ws ++ [(Lds ++ [HeB.plugQ (Q' ++ [(v, 0)]) T], u, [])])
        = farWt b (q0+1) ws ++ (Yp ++ shiftr01 (Q'.length + 2) 0
            (((1, q0+1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b (q0+1) u T))) := by
      intro T
      rw [HeB.plugQ_snoc, HeD.farWt_botT, hYpd, chT_append, shiftr01_append0]
      simp [chT, unitT, List.append_assoc]
    have hYpF : Fr Yp := by rw [hYpd]; exact Fr_append (Fr_fwH _ _ _ _ _) (Fr_shiftr (Fr_chT _ hv) _)
    have hYpne : Yp ≠ [] := by rw [hYpd]; simp [fwH]
    have hYpH : Hd Yp := by rw [hYpd]; exact Hd_app_ne (Hd_fwH _ _ _ _ _) (by simp [fwH])
    rw [eW, chT_deep]
    have e1 : (((1, q0+1 + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 [((1, q0+1+1, 0) : ℕ×ℕ×ℕ), ((2, q0+1+1, 0) : ℕ×ℕ×ℕ)])
        = shiftr01 1 0 (((0, q0+1, 0) : ℕ×ℕ×ℕ) :: ([((1,q0+1+1,0):ℕ×ℕ×ℕ)] ++ [((2,q0+1+1,0):ℕ×ℕ×ℕ)])) := by
      simp [shiftr01]
    rw [e1]
    refine HeQ.upleaf_deep_coreD hA hA1 ho f (Fr_farWt _ _ _) hYpF hYpH hYpne
      (D := [((1,q0+1+1,0):ℕ×ℕ×ℕ)]) (d0 := 2) (m := q0+1+1) (q := q0+1) (d := Q'.length + 2)
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; omega)
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact le_refl _)
      (by omega) (by omega) (by omega) ?_
    intro m' hm'
    obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
    rw [show ([((1,q0+1+1,0):ℕ×ℕ×ℕ)] ++ [((2,q0+1+1,0):ℕ×ℕ×ℕ)])
        = [((1,q0+1+1,0):ℕ×ℕ×ℕ),((2,q0+1+1,0):ℕ×ℕ×ℕ)] from rfl, htow j]
    have := hrep j
    rw [eW] at this
    simpa [shiftr01] using this

end PmA
end TRIO
