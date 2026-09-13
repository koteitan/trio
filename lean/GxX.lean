/-
GxX.lean: tools/gen_gxw.py が生成。タイの下の語を持つシート行。
-/
import GxW

namespace TRIO
namespace GxX

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW

/-- ★ シート行 988。 -/
theorem R988_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 990。 -/
theorem R990_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 991。 -/
theorem R991_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_nil 1)) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 992。 -/
theorem R992_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 993。 -/
theorem R993_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_nil1 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 994。 -/
theorem R994_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_node (ρ := 1) (σ := 1) (u := 1) (by omega) (by omega) (GF_nil1 1) (GF_nil1 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 995。 -/
theorem R995_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_node (ρ := 1) (σ := 2) (u := 1) (by omega) (by omega) (GF_nil1 1) (GF_nil (σ := 2) (by omega) 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 996。 -/
theorem R996_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (5, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_node (ρ := 1) (σ := 2) (u := 1) (by omega) (by omega) (GF_nil1 1) (GF_node (ρ := 2) (σ := 3) (u := 1) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 1) (GF_nil (σ := 3) (by omega) 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 997。 -/
theorem R997_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_nil 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 998。 -/
theorem R998_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (1, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_nil 1)))) (WordsG_nil 1)))) rfl) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 999。 -/
theorem R999_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_nil 1)))) (WordsG_nil 1)))) rfl) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_node (ρ := 1) (σ := 2) (u := 1) (by omega) (by omega) (GF_nil1 1) (GF_nil (σ := 2) (by omega) 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1000。 -/
theorem R1000_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_nil 1)))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1001。 -/
theorem R1001_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_nil 1)))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1002。 -/
theorem R1002_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_nil 1)))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1003。 -/
theorem R1003_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_nil 1)))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_consT (v := 2) (TF_tieG (u := 2) (TF_nil 2) (GF_node (ρ := 1) (σ := 2) (u := 2) (by omega) (by omega) (GF_nil1 2) (GF_nil (σ := 2) (by omega) 2))) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1004。 -/
theorem R1004_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 4, 0), (3, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_nil 1)))) (WordsG_nil 1))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 2) (WordsG_consT (v := 2) (TF_tieG (u := 2) (TF_nil 2) (GF_node (ρ := 1) (σ := 2) (u := 2) (by omega) (by omega) (GF_nil1 2) (GF_nil (σ := 2) (by omega) 2))) (WordsG_nil 2))) (Wg_of_starOK (starOK_wordsG (v := 3) (WordsG_nil 3))) rfl)) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1005。 -/
theorem R1005_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1006。 -/
theorem R1006_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_nil 1)))) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1007。 -/
theorem R1007_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1008。 -/
theorem R1008_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_load (u := 0) (TF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1009。 -/
theorem R1009_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_nil1 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1010。 -/
theorem R1010_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_nil1 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1011。 -/
theorem R1011_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 1) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil1 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1012。 -/
theorem R1012_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1013。 -/
theorem R1013_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_node (ρ := 2) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 2) (by omega) 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1014。 -/
theorem R1014_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 3) (by omega) 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1015。 -/
theorem R1015_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1016。 -/
theorem R1016_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1017。 -/
theorem R1017_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1018。 -/
theorem R1018_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1019。 -/
theorem R1019_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_load (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1020。 -/
theorem R1020_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (GF_nil1 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1021。 -/
theorem R1021_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (GF_nil1 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1022。 -/
theorem R1022_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (GF_nil1 0)) (GF_nil1 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1023。 -/
theorem R1023_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (GF_node (ρ := 1) (σ := 1) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil1 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1024。 -/
theorem R1024_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1025。 -/
theorem R1025_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 3) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1026。 -/
theorem R1026_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1027。 -/
theorem R1027_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1028。 -/
theorem R1028_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 1) (u := 0) (by omega) (by omega) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0))) (GF_nil1 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1029。 -/
theorem R1029_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 1, 0), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 1) (u := 0) (by omega) (by omega) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0))) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1030。 -/
theorem R1030_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0))) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1031。 -/
theorem R1031_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0))) (GF_nil (σ := 2) (by omega) 0)) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1032。 -/
theorem R1032_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0))) (GF_node (ρ := 2) (σ := 1) (u := 0) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 0) (GF_nil1 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1033。 -/
theorem R1033_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0))) (GF_node (ρ := 2) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 2) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1034。 -/
theorem R1034_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 3) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1044。 -/
theorem R1044_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)) (GNF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1045。 -/
theorem R1045_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1046。 -/
theorem R1046_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_nil1 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1047。 -/
theorem R1047_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1048。 -/
theorem R1048_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1049。 -/
theorem R1049_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)) (GNF_nil 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)) (GNF_nil 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1050。 -/
theorem R1050_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)) (GNF_nil 0)))) (GF_nil1 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1051。 -/
theorem R1051_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 1) (u := 0) (by omega) (by omega) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)) (GNF_nil 0))) (GF_nil1 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1052。 -/
theorem R1052_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)) (GNF_nil 0))) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1057。 -/
theorem R1057_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)) (GNF_nil 0)) (GNF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1058。 -/
theorem R1058_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (3, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)) (GNF_nil 0)) (GNF_nil 0))) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1059。 -/
theorem R1059_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (3, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)) (GNF_nil 0)) (GNF_nil 0)) (GNF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1060。 -/
theorem R1060_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_load (u := 0) (GNF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1061。 -/
theorem R1061_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 0, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_load (u := 0) (GNF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1062。 -/
theorem R1062_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 0, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_load (u := 0) (GNF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl))) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1063。 -/
theorem R1063_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 0, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_load (u := 0) (GNF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)) (GNF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1064。 -/
theorem R1064_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 0, 0), (3, 2, 1), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_load (u := 0) (GNF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)) (GNF_load (u := 0) (GNF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1065。 -/
theorem R1065_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 0, 0), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_load (u := 0) (GNF_load (u := 0) (GNF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1066。 -/
theorem R1066_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 0, 0), (5, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_load (u := 0) (GNF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))) (by omega)) rfl)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1067。 -/
theorem R1067_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1068。 -/
theorem R1068_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1069。 -/
theorem R1069_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_nil 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1070。 -/
theorem R1070_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_load (u := 1) (GNF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1071。 -/
theorem R1071_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_load (u := 1) (GNF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1072。 -/
theorem R1072_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_load (u := 1) (GNF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1073。 -/
theorem R1073_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_load (u := 1) (GNF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_load (u := 1) (GNF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1074。 -/
theorem R1074_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_load (u := 1) (GNF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (GF_nil1 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1075。 -/
theorem R1075_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_node (ρ := 1) (σ := 2) (u := 1) (by omega) (by omega) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_load (u := 1) (GNF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl))) (GF_nil (σ := 2) (by omega) 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1078。 -/
theorem R1078_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_snoc (u := 1) (BWF_nil 1) (GNF_load (u := 1) (GNF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)) (GNF_nil 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1079。 -/
theorem R1079_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (4, 3, 1), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_snoc (u := 1) (BWF_nil 1) (GNF_load (u := 1) (GNF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)) (GNF_load (u := 1) (GNF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1080。 -/
theorem R1080_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_load (u := 1) (GNF_load (u := 1) (GNF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1081。 -/
theorem R1081_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (6, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_load (u := 1) (GNF_nil 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1)))) (by omega)) rfl)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1082。 -/
theorem R1082_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_tie (u := 1) (GNF_nil 1) (GF_nil1 1))))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1083。 -/
theorem R1083_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 4, 1), (6, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_BWF (BWF_snoc (u := 1) (BWF_nil 1) (GNF_tie (u := 1) (GNF_nil 1) (GF_nil1 1))))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_consT (v := 2) (TF_tieG (u := 2) (TF_nil 2) (GF_of_BWF (BWF_snoc (u := 2) (BWF_nil 2) (GNF_tie (u := 2) (GNF_nil 2) (GF_nil1 2))))) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1084。 -/
theorem R1084_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1085。 -/
theorem R1085_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1086。 -/
theorem R1086_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_nil1 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1087。 -/
theorem R1087_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1088。 -/
theorem R1088_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1089。 -/
theorem R1089_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1090。 -/
theorem R1090_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1091。 -/
theorem R1091_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_load (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1092。 -/
theorem R1092_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (GF_nil1 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1093。 -/
theorem R1093_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 1) (u := 0) (by omega) (by omega) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0)))) (GF_nil1 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1094。 -/
theorem R1094_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0)))) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1095。 -/
theorem R1095_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0)))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 3) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1101。 -/
theorem R1101_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))) (GNF_nil 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1102。 -/
theorem R1102_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 2, 1), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1103。 -/
theorem R1103_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1104。 -/
theorem R1104_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_nil1 0)) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1105。 -/
theorem R1105_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil (σ := 2) (by omega) 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1106。 -/
theorem R1106_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (5, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_tie (u := 0) (GNF_nil 0) (GF_of_BWF (BWF_snoc (u := 0) (BWF_nil 0) (GNF_nil 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

end GxX
end TRIO
