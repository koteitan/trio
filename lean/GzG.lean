/-
GzG.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。
-/
import GzF

namespace TRIO
namespace GzG

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF

/-- ★ シート行 1338。 -/
theorem R1338_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1339。 -/
theorem R1339_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)))) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1340。 -/
theorem R1340_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)))) (GF_of_GPF (GPF_nil1 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1341。 -/
theorem R1341_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 1) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)) (GPF_nil1 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1342。 -/
theorem R1342_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1343。 -/
theorem R1343_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)))) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1346。 -/
theorem R1346_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1347。 -/
theorem R1347_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 0), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)) (GPF_load (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0) (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1348。 -/
theorem R1348_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 1) [] (by decide) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0) (GPF_nil1 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1349。 -/
theorem R1349_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1350。 -/
theorem R1350_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [] (by decide) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0) (GPF_nil (A := []) (o := 3) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1351。 -/
theorem R1351_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)) (GPF_of_PVF (PVF_snoc (A := []) (o := 2) (by decide) (PVF_nil (A := []) (o := 2) (by decide) (by decide) 0) (RLF_nil (A := []) (o := 2) (by decide) (by decide) (by decide) 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1352。 -/
theorem R1352_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)) (GPF_of_PVF (PVF_farR (A := []) (o := 2) (by decide) (by decide) (by decide) 0 1))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1353。 -/
theorem R1353_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 1), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 2) (by decide) (by decide) (by decide) 0 1)) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1354。 -/
theorem R1354_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 1), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 2) (by decide) (by decide) (by decide) 0 1)) (GPF_nil (A := []) (o := 3) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1355。 -/
theorem R1355_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 1), (4, 3, 0), (5, 4, 1), (6, 4, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 2) (by decide) (by decide) (by decide) 0 1)) (GPF_of_PVF (PVF_farR (A := []) (o := 3) (by decide) (by decide) (by decide) 0 1)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1356。 -/
theorem R1356_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 1), (4, 3, 0), (5, 4, 1), (6, 4, 1), (5, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 2) (by decide) (by decide) (by decide) 0 1)) (GPF_node (A := []) (o := 3) (by decide) (by decide) (by decide) (b := 0) (τ := 4) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 3) (by decide) (by decide) (by decide) 0 1)) (GPF_nil (A := []) (o := 4) (by decide) (by decide) 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1357。 -/
theorem R1357_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1358。 -/
theorem R1358_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0)) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1359。 -/
theorem R1359_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_nil (A := [1]) (o := 2) (by decide) (by decide) 0)))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1360。 -/
theorem R1360_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_nil (A := [1]) (o := 2) (by decide) (by decide) 0))) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1361。 -/
theorem R1361_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 0), (5, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_node (A := [1]) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (GPF_nil (A := [1]) (o := 2) (by decide) (by decide) 0) (GPF_nil (A := [1]) (o := 2) (by decide) (by decide) 0)))) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1362。 -/
theorem R1362_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 0), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_node (A := [1]) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [1] (by decide) (GPF_nil (A := [1]) (o := 2) (by decide) (by decide) 0) (GPF_nil (A := [1]) (o := 3) (by decide) (by decide) 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1363。 -/
theorem R1363_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 0), (5, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [1]) (o := 2) (by decide) (PVF_nil (A := [1]) (o := 2) (by decide) (by decide) 0) (RLF_nil (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1364。 -/
theorem R1364_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_farR (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0 1))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1365。 -/
theorem R1365_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_node (A := [1]) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [1] (by decide) (GPF_of_PVF (PVF_farR (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0 1)) (GPF_nil (A := [1]) (o := 3) (by decide) (by decide) 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1366。 -/
theorem R1366_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (5, 3, 0), (6, 4, 1), (7, 4, 1), (6, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_node (A := [1]) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [1] (by decide) (GPF_of_PVF (PVF_farR (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0 1)) (GPF_node (A := [1]) (o := 3) (by decide) (by decide) (by decide) (b := 0) (τ := 4) [1] (by decide) (GPF_of_PVF (PVF_farR (A := [1]) (o := 3) (by decide) (by decide) (by decide) 0 1)) (GPF_nil (A := [1]) (o := 4) (by decide) (by decide) 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1367。 -/
theorem R1367_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (5, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [1]) (o := 2) (by decide) (PVF_farR (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0 1) (RLF_nil (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1368。 -/
theorem R1368_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (5, 3, 1), (6, 3, 0), (7, 4, 1), (8, 4, 1), (7, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [1]) (o := 2) (by decide) (PVF_farR (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := [1]) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [2, 1] (by decide) (by decide) (RLF_nil (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0) (GPF_node (A := [2, 1]) (o := 3) (by decide) (by decide) (by decide) (b := 0) (τ := 4) [2, 1] (by decide) (GPF_of_PVF (PVF_farR (A := [2, 1]) (o := 3) (by decide) (by decide) (by decide) 0 1)) (GPF_nil (A := [2, 1]) (o := 4) (by decide) (by decide) 0)))))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1369。 -/
theorem R1369_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (5, 3, 1), (6, 3, 0), (7, 4, 1), (8, 4, 1), (7, 4, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [1]) (o := 2) (by decide) (PVF_farR (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := [1]) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [2, 1] (by decide) (by decide) (RLF_nil (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [2, 1]) (o := 3) (by decide) (PVF_farR (A := [2, 1]) (o := 3) (by decide) (by decide) (by decide) 0 1) (RLF_nil (A := [2, 1]) (o := 3) (by decide) (by decide) (by decide) 0))))))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1370。 -/
theorem R1370_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (5, 3, 1), (6, 3, 0), (7, 4, 1), (8, 4, 1), (7, 4, 1), (8, 4, 0), (9, 5, 1), (10, 5, 1), (9, 5, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 1 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [1]) (o := 2) (by decide) (PVF_farR (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := [1]) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [2, 1] (by decide) (by decide) (RLF_nil (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [2, 1]) (o := 3) (by decide) (PVF_farR (A := [2, 1]) (o := 3) (by decide) (by decide) (by decide) 0 1) (RLF_child (A := [2, 1]) (o := 3) (by decide) (by decide) (by decide) (b := 0) (τ := 4) [3, 2, 1] (by decide) (by decide) (RLF_nil (A := [2, 1]) (o := 3) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [3, 2, 1]) (o := 4) (by decide) (PVF_farR (A := [3, 2, 1]) (o := 4) (by decide) (by decide) (by decide) 0 1) (RLF_nil (A := [3, 2, 1]) (o := 4) (by decide) (by decide) (by decide) 0)))))))))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1371。 -/
theorem R1371_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 2 (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1372。 -/
theorem R1372_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_farN (v := 0) 2 (WordsG_nil 0)) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1373。 -/
theorem R1373_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_farN (v := 0) 2 (WordsG_nil 0)) (Wg_of_starOK (starOK_farN (v := 1) 1 (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1374。 -/
theorem R1374_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 1), (2, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_farN (v := 0) 2 (WordsG_nil 0)) (Wg_of_starOK (starOK_farN (v := 1) 2 (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1375。 -/
theorem R1375_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 1), (2, 2, 1), (3, 2, 1), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_farN (v := 0) 2 (WordsG_nil 0)) (Wg_of_starOK (starOK_hang (starOK_farN (v := 1) 2 (WordsG_nil 1)) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1376。 -/
theorem R1376_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 2 (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1377。 -/
theorem R1377_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 2 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 1)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1378。 -/
theorem R1378_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 2 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 2)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1379。 -/
theorem R1379_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 2 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 2)) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1380。 -/
theorem R1380_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 1), (4, 3, 1), (5, 3, 1), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 2 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 2)) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [] (by decide) (GPF_of_PVF (PVF_farR (A := []) (o := 2) (by decide) (by decide) (by decide) 0 2)) (GPF_nil (A := []) (o := 3) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1381。 -/
theorem R1381_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 2 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 2) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1382。 -/
theorem R1382_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (5, 3, 1), (6, 3, 1), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 2 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 2) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_node (A := [1]) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [1] (by decide) (GPF_of_PVF (PVF_farR (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0 2)) (GPF_nil (A := [1]) (o := 3) (by decide) (by decide) 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1383。 -/
theorem R1383_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 1), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (5, 3, 1), (6, 3, 1), (5, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 2 (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farR (A := []) (o := 1) (by decide) (by decide) (by decide) 0 2) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [1]) (o := 2) (by decide) (PVF_farR (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0 2) (RLF_nil (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1384。 -/
theorem R1384_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 3 (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR] using h

/-- ★ シート行 1385。 -/
theorem R1385_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farN (v := 0) 4 (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol, farR] using h

end GzG
end TRIO
