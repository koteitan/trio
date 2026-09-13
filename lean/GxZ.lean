/-
GxZ.lean: tools/gen_gxy.py が生成。節点の下の語（錨つきの型紙）を持つシート行。
-/
import GxY

namespace TRIO
namespace GxZ

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY

/-- ★ シート行 988。 -/
theorem R988_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 990。 -/
theorem R990_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 991。 -/
theorem R991_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_nil 1)) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 992。 -/
theorem R992_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 993。 -/
theorem R993_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_nil1 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 994。 -/
theorem R994_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_node (ρ := 1) (σ := 1) (u := 1) (by omega) (by omega) (GF_nil1 1) (GF_nil1 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 995。 -/
theorem R995_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_node (ρ := 1) (σ := 2) (u := 1) (by omega) (by omega) (GF_nil1 1) (GF_nil (σ := 2) (by omega) 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 996。 -/
theorem R996_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0), (5, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_node (ρ := 1) (σ := 2) (u := 1) (by omega) (by omega) (GF_nil1 1) (GF_node (ρ := 2) (σ := 3) (u := 1) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 1) (GF_nil (σ := 3) (by omega) 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 997。 -/
theorem R997_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_nil (σ := 1) (by omega) 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 998。 -/
theorem R998_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (1, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_nil (σ := 1) (by omega) 1)))) (WordsG_nil 1)))) rfl) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 999。 -/
theorem R999_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_nil (σ := 1) (by omega) 1)))) (WordsG_nil 1)))) rfl) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_node (ρ := 1) (σ := 2) (u := 1) (by omega) (by omega) (GF_nil1 1) (GF_nil (σ := 2) (by omega) 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1000。 -/
theorem R1000_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_nil (σ := 1) (by omega) 1)))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1001。 -/
theorem R1001_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_nil (σ := 1) (by omega) 1)))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1002。 -/
theorem R1002_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_nil (σ := 1) (by omega) 1)))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1003。 -/
theorem R1003_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_nil (σ := 1) (by omega) 1)))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_consT (v := 2) (TF_tieG (u := 2) (TF_nil 2) (GF_node (ρ := 1) (σ := 2) (u := 2) (by omega) (by omega) (GF_nil1 2) (GF_nil (σ := 2) (by omega) 2))) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1004。 -/
theorem R1004_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 4, 0), (3, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_nil (σ := 1) (by omega) 1)))) (WordsG_nil 1))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 2) (WordsG_consT (v := 2) (TF_tieG (u := 2) (TF_nil 2) (GF_node (ρ := 1) (σ := 2) (u := 2) (by omega) (by omega) (GF_nil1 2) (GF_nil (σ := 2) (by omega) 2))) (WordsG_nil 2))) (Wg_of_starOK (starOK_wordsG (v := 3) (WordsG_nil 3))) rfl)) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1005。 -/
theorem R1005_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1006。 -/
theorem R1006_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_nil (σ := 1) (by omega) 1)))) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1007。 -/
theorem R1007_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1008。 -/
theorem R1008_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_load (u := 0) (TF_nil 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1009。 -/
theorem R1009_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_nil1 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1010。 -/
theorem R1010_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_nil1 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1011。 -/
theorem R1011_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 1) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil1 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1012。 -/
theorem R1012_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1013。 -/
theorem R1013_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_node (ρ := 2) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 2) (by omega) 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1014。 -/
theorem R1014_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 3) (by omega) 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1015。 -/
theorem R1015_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1016。 -/
theorem R1016_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1017。 -/
theorem R1017_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1018。 -/
theorem R1018_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1019。 -/
theorem R1019_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_load (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1020。 -/
theorem R1020_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (GF_nil1 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1021。 -/
theorem R1021_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (GF_nil1 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1022。 -/
theorem R1022_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (GF_nil1 0)) (GF_nil1 0)) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1023。 -/
theorem R1023_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (GF_node (ρ := 1) (σ := 1) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil1 0))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1024。 -/
theorem R1024_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1025。 -/
theorem R1025_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 3) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1026。 -/
theorem R1026_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1027。 -/
theorem R1027_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (3, 2, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1028。 -/
theorem R1028_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 1) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_nil1 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1029。 -/
theorem R1029_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 1, 0), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 1) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1030。 -/
theorem R1030_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1031。 -/
theorem R1031_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_nil (σ := 2) (by omega) 0)) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1032。 -/
theorem R1032_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_node (ρ := 2) (σ := 1) (u := 0) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 0) (GF_nil1 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1033。 -/
theorem R1033_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_node (ρ := 2) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 2) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1034。 -/
theorem R1034_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 3) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1035。 -/
theorem R1035_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1036。 -/
theorem R1036_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (4, 3, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0)))) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1037。 -/
theorem R1037_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (4, 3, 1), (3, 2, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1038。 -/
theorem R1038_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (4, 3, 1), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_node (ρ := 2) (σ := 1) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0))) (GF_nil1 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1039。 -/
theorem R1039_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (4, 3, 1), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_node (ρ := 2) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0))) (GF_nil (σ := 2) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1040。 -/
theorem R1040_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (4, 3, 1), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0))) (GF_nil (σ := 3) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1041。 -/
theorem R1041_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (4, 3, 1), (4, 3, 0), (5, 4, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 3) (PVF_nil (σ := 3) (by omega) 0) (LCF_nil (σ := 3) (by omega) 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1042。 -/
theorem R1042_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (4, 3, 1), (4, 3, 0), (5, 4, 1), (5, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0))) (GF_node (ρ := 3) (σ := 4) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 3) (PVF_nil (σ := 3) (by omega) 0) (LCF_nil (σ := 3) (by omega) 0))) (GF_nil (σ := 4) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1043。 -/
theorem R1043_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 0), (4, 3, 1), (4, 3, 0), (5, 4, 1), (5, 4, 0), (6, 5, 1), (6, 5, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0))) (GF_node (ρ := 3) (σ := 4) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 3) (PVF_nil (σ := 3) (by omega) 0) (LCF_nil (σ := 3) (by omega) 0))) (GF_node (ρ := 4) (σ := 5) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 4) (PVF_nil (σ := 4) (by omega) 0) (LCF_nil (σ := 4) (by omega) 0))) (GF_nil (σ := 5) (by omega) 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1044。 -/
theorem R1044_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1045。 -/
theorem R1045_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1046。 -/
theorem R1046_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_nil1 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1047。 -/
theorem R1047_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1048。 -/
theorem R1048_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1049。 -/
theorem R1049_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1050。 -/
theorem R1050_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)))) (GF_nil1 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1051。 -/
theorem R1051_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 1) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0))) (GF_nil1 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1052。 -/
theorem R1052_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0))) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1053。 -/
theorem R1053_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (3, 2, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1054。 -/
theorem R1054_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (3, 2, 0), (4, 3, 1), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0)) (LCF_nil (σ := 2) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1055。 -/
theorem R1055_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (3, 2, 0), (4, 3, 1), (4, 3, 1), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0)) (LCF_nil (σ := 2) (by omega) 0))) (GF_nil (σ := 3) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1056。 -/
theorem R1056_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (3, 2, 0), (4, 3, 1), (4, 3, 1), (4, 3, 0), (5, 4, 1), (5, 4, 1), (5, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0)) (LCF_nil (σ := 2) (by omega) 0))) (GF_node (ρ := 3) (σ := 4) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 3) (PVF_snoc (b := 0) (σ := 3) (PVF_nil (σ := 3) (by omega) 0) (LCF_nil (σ := 3) (by omega) 0)) (LCF_nil (σ := 3) (by omega) 0))) (GF_nil (σ := 4) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1057。 -/
theorem R1057_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1058。 -/
theorem R1058_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (3, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0))) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1059。 -/
theorem R1059_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (3, 2, 1), (3, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1060。 -/
theorem R1060_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_load (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1061。 -/
theorem R1061_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 0, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_load (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1062。 -/
theorem R1062_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 0, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_load (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl))) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1063。 -/
theorem R1063_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 0, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_load (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1064。 -/
theorem R1064_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 0, 0), (3, 2, 1), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_load (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)) (LCF_load (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1065。 -/
theorem R1065_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 0, 0), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_load (σ := 1) (b := 0) (by omega) (LCF_load (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1066。 -/
theorem R1066_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 0, 0), (5, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_load (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))) (by omega)) rfl)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1067。 -/
theorem R1067_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1068。 -/
theorem R1068_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1069。 -/
theorem R1069_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_nil (σ := 1) (by omega) 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1070。 -/
theorem R1070_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_load (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1071。 -/
theorem R1071_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_load (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1072。 -/
theorem R1072_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_load (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1073。 -/
theorem R1073_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_load (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_load (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1074。 -/
theorem R1074_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_load (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (GF_nil1 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1075。 -/
theorem R1075_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_node (ρ := 1) (σ := 2) (u := 1) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_load (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl))) (GF_nil (σ := 2) (by omega) 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1076。 -/
theorem R1076_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (4, 3, 0), (5, 4, 1), (6, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_node (ρ := 1) (σ := 2) (u := 1) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_load (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl))) (GF_of_PVF (PVF_snoc (b := 1) (σ := 2) (PVF_nil (σ := 2) (by omega) 1) (LCF_load (σ := 2) (b := 1) (by omega) (LCF_nil (σ := 2) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl))))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1077。 -/
theorem R1077_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (4, 3, 0), (5, 4, 1), (6, 1, 0), (5, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_node (ρ := 1) (σ := 2) (u := 1) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_load (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl))) (GF_node (ρ := 2) (σ := 3) (u := 1) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 1) (σ := 2) (PVF_nil (σ := 2) (by omega) 1) (LCF_load (σ := 2) (b := 1) (by omega) (LCF_nil (σ := 2) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl))) (GF_nil (σ := 3) (by omega) 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1078。 -/
theorem R1078_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_load (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)) (LCF_nil (σ := 1) (by omega) 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1079。 -/
theorem R1079_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (4, 3, 1), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_load (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)) (LCF_load (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1080。 -/
theorem R1080_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_load (σ := 1) (b := 1) (by omega) (LCF_load (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1081。 -/
theorem R1081_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 1, 0), (6, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_load (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1)))) (by omega)) rfl)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1082。 -/
theorem R1082_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_node (σ := 1) (τ := 1) (b := 1) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 1) (GF_nil1 1))))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1083。 -/
theorem R1083_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 4, 1), (6, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_node (σ := 1) (τ := 1) (b := 1) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 1) (GF_nil1 1))))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_consT (v := 2) (TF_tieG (u := 2) (TF_nil 2) (GF_of_PVF (PVF_snoc (b := 2) (σ := 1) (PVF_nil (σ := 1) (by omega) 2) (LCF_node (σ := 1) (τ := 1) (b := 2) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 2) (GF_nil1 2))))) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1084。 -/
theorem R1084_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1085。 -/
theorem R1085_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1086。 -/
theorem R1086_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_nil1 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1087。 -/
theorem R1087_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1088。 -/
theorem R1088_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1089。 -/
theorem R1089_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1090。 -/
theorem R1090_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1091。 -/
theorem R1091_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_load (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1092。 -/
theorem R1092_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (GF_nil1 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1093。 -/
theorem R1093_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 1) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0)))) (GF_nil1 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1094。 -/
theorem R1094_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0)))) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1095。 -/
theorem R1095_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0)))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 3) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1096。 -/
theorem R1096_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 2, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1097。 -/
theorem R1097_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 2, 0), (4, 3, 1), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_node (σ := 2) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 2) (by omega) 0) (GF_nil1 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1098。 -/
theorem R1098_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 2, 0), (4, 3, 1), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_node (σ := 2) (τ := 2) (b := 0) (by omega) (by omega) (LCF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 2) (by omega) 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1099。 -/
theorem R1099_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 2, 0), (4, 3, 1), (5, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0)))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_node (σ := 2) (τ := 2) (b := 0) (by omega) (by omega) (LCF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 2) (by omega) 0)))) (GF_nil (σ := 3) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1100。 -/
theorem R1100_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 2, 0), (4, 3, 1), (5, 2, 0), (4, 3, 0), (5, 4, 1), (6, 3, 0), (5, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0)))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_node (σ := 2) (τ := 2) (b := 0) (by omega) (by omega) (LCF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 2) (by omega) 0)))) (GF_node (ρ := 3) (σ := 4) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 3) (PVF_nil (σ := 3) (by omega) 0) (LCF_node (σ := 3) (τ := 3) (b := 0) (by omega) (by omega) (LCF_nil (σ := 3) (by omega) 0) (GF_nil (σ := 3) (by omega) 0)))) (GF_nil (σ := 4) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1101。 -/
theorem R1101_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1102。 -/
theorem R1102_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 2, 1), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1103。 -/
theorem R1103_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1104。 -/
theorem R1104_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0)) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1105。 -/
theorem R1105_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil (σ := 2) (by omega) 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1106。 -/
theorem R1106_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 1, 0), (5, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1107。 -/
theorem R1107_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1108。 -/
theorem R1108_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_far (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1))))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1109。 -/
theorem R1109_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 0), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_far (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1))))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1110。 -/
theorem R1110_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1111。 -/
theorem R1111_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1112。 -/
theorem R1112_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))))) (GF_nil1 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1113。 -/
theorem R1113_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1114。 -/
theorem R1114_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1115。 -/
theorem R1115_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_node (σ := 2) (τ := 2) (b := 0) (by omega) (by omega) (LCF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 2) (by omega) 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1116。 -/
theorem R1116_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_node (σ := 2) (τ := 2) (b := 0) (by omega) (by omega) (LCF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 2) (by omega) 0)))) (GF_nil (σ := 3) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1117。 -/
theorem R1117_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 2, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_node (σ := 2) (τ := 2) (b := 0) (by omega) (by omega) (LCF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 2) (by omega) 0))) (LCF_nil (σ := 2) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1118。 -/
theorem R1118_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 2, 0), (4, 3, 1), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_node (σ := 2) (τ := 2) (b := 0) (by omega) (by omega) (LCF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 2) (by omega) 0))) (LCF_node (σ := 2) (τ := 2) (b := 0) (by omega) (by omega) (LCF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 2) (by omega) 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1119。 -/
theorem R1119_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 2, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_node (σ := 2) (τ := 2) (b := 0) (by omega) (by omega) (LCF_node (σ := 2) (τ := 2) (b := 0) (by omega) (by omega) (LCF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 2) (by omega) 0)) (GF_nil (σ := 2) (by omega) 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1120。 -/
theorem R1120_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 2, 0), (6, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_node (σ := 2) (τ := 2) (b := 0) (by omega) (by omega) (LCF_nil (σ := 2) (by omega) 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1121。 -/
theorem R1121_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_far (σ := 2) (b := 0) (by omega) (LCF_nil (σ := 2) (by omega) 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1122。 -/
theorem R1122_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 0), (4, 3, 0), (5, 4, 1), (6, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_far (σ := 2) (b := 0) (by omega) (LCF_nil (σ := 2) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 3) (PVF_nil (σ := 3) (by omega) 0) (LCF_node (σ := 3) (τ := 3) (b := 0) (by omega) (by omega) (LCF_nil (σ := 3) (by omega) 0) (GF_nil (σ := 3) (by omega) 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1123。 -/
theorem R1123_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 0), (4, 3, 0), (5, 4, 1), (6, 3, 0), (5, 4, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_far (σ := 2) (b := 0) (by omega) (LCF_nil (σ := 2) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 3) (PVF_snoc (b := 0) (σ := 3) (PVF_nil (σ := 3) (by omega) 0) (LCF_node (σ := 3) (τ := 3) (b := 0) (by omega) (by omega) (LCF_nil (σ := 3) (by omega) 0) (GF_nil (σ := 3) (by omega) 0))) (LCF_nil (σ := 3) (by omega) 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1124。 -/
theorem R1124_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 0), (4, 3, 0), (5, 4, 1), (6, 3, 0), (6, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_far (σ := 2) (b := 0) (by omega) (LCF_nil (σ := 2) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 3) (PVF_nil (σ := 3) (by omega) 0) (LCF_node (σ := 3) (τ := 3) (b := 0) (by omega) (by omega) (LCF_node (σ := 3) (τ := 3) (b := 0) (by omega) (by omega) (LCF_nil (σ := 3) (by omega) 0) (GF_nil (σ := 3) (by omega) 0)) (GF_nil (σ := 3) (by omega) 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1125。 -/
theorem R1125_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 0), (4, 3, 0), (5, 4, 1), (6, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_far (σ := 2) (b := 0) (by omega) (LCF_nil (σ := 2) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 3) (PVF_nil (σ := 3) (by omega) 0) (LCF_far (σ := 3) (b := 0) (by omega) (LCF_nil (σ := 3) (by omega) 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1126。 -/
theorem R1126_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 0), (4, 3, 0), (5, 4, 1), (6, 4, 0), (5, 4, 0), (6, 5, 1), (7, 5, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_far (σ := 2) (b := 0) (by omega) (LCF_nil (σ := 2) (by omega) 0)))) (GF_node (ρ := 3) (σ := 4) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 3) (PVF_nil (σ := 3) (by omega) 0) (LCF_far (σ := 3) (b := 0) (by omega) (LCF_nil (σ := 3) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 4) (PVF_nil (σ := 4) (by omega) 0) (LCF_far (σ := 4) (b := 0) (by omega) (LCF_nil (σ := 4) (by omega) 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1127。 -/
theorem R1127_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1128。 -/
theorem R1128_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (1, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1129。 -/
theorem R1129_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 0), (4, 3, 1), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_far (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1))) (LCF_nil (σ := 1) (by omega) 1)))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1130。 -/
theorem R1130_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1131。 -/
theorem R1131_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_nil1 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1132。 -/
theorem R1132_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_nil1 0) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1133。 -/
theorem R1133_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1134。 -/
theorem R1134_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1135。 -/
theorem R1135_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)))) (GF_nil1 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1136。 -/
theorem R1136_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0))) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1137。 -/
theorem R1137_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (3, 2, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_nil (σ := 2) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1138。 -/
theorem R1138_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_far (σ := 2) (b := 0) (by omega) (LCF_nil (σ := 2) (by omega) 0))) (LCF_nil (σ := 2) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1139。 -/
theorem R1139_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 0), (4, 3, 1), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_far (σ := 2) (b := 0) (by omega) (LCF_nil (σ := 2) (by omega) 0))) (LCF_nil (σ := 2) (by omega) 0))) (GF_nil (σ := 3) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1140。 -/
theorem R1140_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 0), (4, 3, 1), (4, 3, 0), (5, 4, 1), (6, 4, 0), (5, 4, 1), (5, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0))) (GF_node (ρ := 2) (σ := 3) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_far (σ := 2) (b := 0) (by omega) (LCF_nil (σ := 2) (by omega) 0))) (LCF_nil (σ := 2) (by omega) 0))) (GF_node (ρ := 3) (σ := 4) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 3) (PVF_snoc (b := 0) (σ := 3) (PVF_nil (σ := 3) (by omega) 0) (LCF_far (σ := 3) (b := 0) (by omega) (LCF_nil (σ := 3) (by omega) 0))) (LCF_nil (σ := 3) (by omega) 0))) (GF_nil (σ := 4) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1141。 -/
theorem R1141_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1142。 -/
theorem R1142_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (3, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0))) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1143。 -/
theorem R1143_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (3, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1144。 -/
theorem R1144_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_load (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1145。 -/
theorem R1145_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1146。 -/
theorem R1146_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 0), (4, 3, 1), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_far (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1))) (LCF_node (σ := 1) (τ := 1) (b := 1) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 1) (GF_nil1 1))))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1147。 -/
theorem R1147_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1148。 -/
theorem R1148_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (GF_nil1 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1149。 -/
theorem R1149_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1150。 -/
theorem R1150_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 1, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0)) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1151。 -/
theorem R1151_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1152。 -/
theorem R1152_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 0), (4, 3, 1), (5, 2, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_snoc (b := 0) (σ := 2) (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_far (σ := 2) (b := 0) (by omega) (LCF_nil (σ := 2) (by omega) 0))) (LCF_node (σ := 2) (τ := 2) (b := 0) (by omega) (by omega) (LCF_nil (σ := 2) (by omega) 0) (GF_nil (σ := 2) (by omega) 0))) (LCF_nil (σ := 2) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1153。 -/
theorem R1153_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 0), (4, 3, 1), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_far (σ := 2) (b := 0) (by omega) (LCF_nil (σ := 2) (by omega) 0))) (LCF_far (σ := 2) (b := 0) (by omega) (LCF_nil (σ := 2) (by omega) 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1154。 -/
theorem R1154_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1155。 -/
theorem R1155_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1156。 -/
theorem R1156_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1157。 -/
theorem R1157_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1159。 -/
theorem R1159_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_load (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1160。 -/
theorem R1160_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 0, 0), (5, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_load (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))) (by omega)) rfl)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1161。 -/
theorem R1161_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)) (GF_nil1 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1162。 -/
theorem R1162_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)) (GF_nil1 0))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_node (σ := 1) (τ := 1) (b := 1) (by omega) (by omega) (LCF_far (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1)) (GF_nil1 1))))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1163。 -/
theorem R1163_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)) (GF_nil1 0))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1164。 -/
theorem R1164_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)) (GF_nil1 0))))) (GF_nil1 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1165。 -/
theorem R1165_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)) (GF_nil1 0)))) (GF_nil (σ := 2) (by omega) 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1166。 -/
theorem R1166_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)) (GF_nil1 0))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1167。 -/
theorem R1167_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 1, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)) (GF_nil1 0))) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1168。 -/
theorem R1168_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1169。 -/
theorem R1169_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 0), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_node (ρ := 1) (σ := 2) (u := 0) (by omega) (by omega) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))))) (GF_of_PVF (PVF_snoc (b := 0) (σ := 2) (PVF_nil (σ := 2) (by omega) 0) (LCF_far (σ := 2) (b := 0) (by omega) (LCF_far (σ := 2) (b := 0) (by omega) (LCF_nil (σ := 2) (by omega) 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1170。 -/
theorem R1170_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1171。 -/
theorem R1171_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (LCF_nil (σ := 1) (by omega) 0)) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1172。 -/
theorem R1172_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 1), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1173。 -/
theorem R1173_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 1), (4, 2, 0), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1174。 -/
theorem R1174_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_node (σ := 1) (τ := 1) (b := 0) (by omega) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))) (GF_nil1 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1175。 -/
theorem R1175_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1176。 -/
theorem R1176_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 2, 0), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1177。 -/
theorem R1177_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (4, 2, 0), (4, 2, 0), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0)))))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1178。 -/
theorem R1178_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_farC (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (FSF_load (σ := 1) (b := 0) (by omega) (FSF_nil (σ := 1) (by omega) 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1179。 -/
theorem R1179_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 0, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_farC (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (FSF_load (σ := 1) (b := 0) (by omega) (FSF_nil (σ := 1) (by omega) 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1180。 -/
theorem R1180_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 0, 0), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_farC (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (FSF_load (σ := 1) (b := 0) (by omega) (FSF_nil (σ := 1) (by omega) 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1181。 -/
theorem R1181_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 0, 0), (5, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_farC (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (FSF_load (σ := 1) (b := 0) (by omega) (FSF_load (σ := 1) (b := 0) (by omega) (FSF_nil (σ := 1) (by omega) 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1182。 -/
theorem R1182_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 0, 0), (6, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_farC (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (FSF_load (σ := 1) (b := 0) (by omega) (FSF_nil (σ := 1) (by omega) 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))) (by omega)) rfl))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1183。 -/
theorem R1183_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_farC (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (FSF_tie (σ := 1) (b := 0) (by omega) (FSF_nil (σ := 1) (by omega) 0) (GF_nil1 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1184。 -/
theorem R1184_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 0), (6, 1, 0), (5, 3, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_farC (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (FSF_tie (σ := 1) (b := 0) (by omega) (FSF_nil (σ := 1) (by omega) 0) (GF_nil1 0)))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_far (σ := 1) (b := 1) (by omega) (LCF_farC (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (FSF_load (σ := 1) (b := 1) (by omega) (FSF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)))) (LCF_nil (σ := 1) (by omega) 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1185。 -/
theorem R1185_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 0), (6, 1, 0), (5, 3, 0), (6, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_farC (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (FSF_tie (σ := 1) (b := 0) (by omega) (FSF_nil (σ := 1) (by omega) 0) (GF_nil1 0)))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_farC (σ := 1) (b := 1) (by omega) (LCF_farC (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (FSF_load (σ := 1) (b := 1) (by omega) (FSF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl)) (FSF_load (σ := 1) (b := 1) (by omega) (FSF_nil (σ := 1) (by omega) 1) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl))))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1186。 -/
theorem R1186_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 0), (6, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_farC (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (FSF_tie (σ := 1) (b := 0) (by omega) (FSF_nil (σ := 1) (by omega) 0) (GF_nil1 0)))))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_PVF (PVF_snoc (b := 1) (σ := 1) (PVF_nil (σ := 1) (by omega) 1) (LCF_farC (σ := 1) (b := 1) (by omega) (LCF_nil (σ := 1) (by omega) 1) (FSF_tie (σ := 1) (b := 1) (by omega) (FSF_nil (σ := 1) (by omega) 1) (GF_nil1 1)))))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1187。 -/
theorem R1187_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_farC (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (FSF_tie (σ := 1) (b := 0) (by omega) (FSF_nil (σ := 1) (by omega) 0) (GF_nil1 0)))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1188。 -/
theorem R1188_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_farC (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (FSF_tie (σ := 1) (b := 0) (by omega) (FSF_nil (σ := 1) (by omega) 0) (GF_nil1 0)))))) (GF_nil1 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1189。 -/
theorem R1189_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_farC (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (FSF_tie (σ := 1) (b := 0) (by omega) (FSF_nil (σ := 1) (by omega) 0) (GF_nil1 0)))) (LCF_nil (σ := 1) (by omega) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1190。 -/
theorem R1190_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 1, 0), (4, 2, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_farC (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (FSF_tie (σ := 1) (b := 0) (by omega) (FSF_nil (σ := 1) (by omega) 0) (GF_nil1 0))))))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1191。 -/
theorem R1191_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 1, 0), (6, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_farC (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (FSF_tie (σ := 1) (b := 0) (by omega) (FSF_nil (σ := 1) (by omega) 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_nil (σ := 1) (by omega) 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1192。 -/
theorem R1192_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 1, 0), (6, 2, 1), (7, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_farC (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0) (FSF_tie (σ := 1) (b := 0) (by omega) (FSF_nil (σ := 1) (by omega) 0) (GF_of_PVF (PVF_snoc (b := 0) (σ := 1) (PVF_nil (σ := 1) (by omega) 0) (LCF_far (σ := 1) (b := 0) (by omega) (LCF_nil (σ := 1) (by omega) 0))))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

end GxZ
end TRIO
