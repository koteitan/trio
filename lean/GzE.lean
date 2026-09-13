/-
GzE.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。
-/
import GzD

namespace TRIO
namespace GzE

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD

/-- ★ シート行 1317。 -/
theorem R1317_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farwords (v := 0) (WordsG_nil 0)))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1321。 -/
theorem R1321_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_farwords (v := 0) (WordsG_nil 0)) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1322。 -/
theorem R1322_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 0, 0), (2, 1, 1), (3, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_farwords (v := 0) (WordsG_nil 0)) (Wg_of_starOK (starOK_farwords (v := 0) (WordsG_nil 0))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1323。 -/
theorem R1323_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_farwords (v := 0) (WordsG_nil 0)) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1324。 -/
theorem R1324_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 0), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_farwords (v := 0) (WordsG_nil 0)) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_nil 1)) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1325。 -/
theorem R1325_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_farwords (v := 0) (WordsG_nil 0)) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_nil 1) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1326。 -/
theorem R1326_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_farwords (v := 0) (WordsG_nil 0)) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 1) (τ := 2) [] (by decide) (GPF_nil1 1) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1327。 -/
theorem R1327_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_farwords (v := 0) (WordsG_nil 0)) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_consT (v := 1) (TF_tieG (u := 1) (TF_nil 1) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_nil1 1) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 1))))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1328。 -/
theorem R1328_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_farwords (v := 0) (WordsG_nil 0)) (Wg_of_starOK (starOK_farwords (v := 1) (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1329。 -/
theorem R1329_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_farwords (v := 0) (WordsG_nil 0)) (Wg_of_starOK (starOK_hang (starOK_farwords (v := 1) (WordsG_nil 1)) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1330。 -/
theorem R1330_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 1), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_farwords (v := 0) (WordsG_nil 0)) (Wg_of_starOK (starOK_hang (starOK_farwords (v := 1) (WordsG_nil 1)) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1331。 -/
theorem R1331_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 1), (2, 2, 0), (3, 3, 1), (4, 3, 1), (3, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_farwords (v := 0) (WordsG_nil 0)) (Wg_of_starOK (starOK_hang (starOK_farwords (v := 1) (WordsG_nil 1)) (Wg_of_starOK (starOK_hang (starOK_farwords (v := 2) (WordsG_nil 2)) (Wg_of_starOK (starOK_wordsG (v := 3) (WordsG_nil 3))) rfl)) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1332。 -/
theorem R1332_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farwords (v := 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1333。 -/
theorem R1333_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farwords (v := 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_consT (v := 0) (TF_nil 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1334。 -/
theorem R1334_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farwords (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_nil1 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1335。 -/
theorem R1335_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farwords (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_nil1 0) (GPF_nil (A := []) (o := 2) (by decide) (by decide) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1336。 -/
theorem R1336_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farwords (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_nil1 0) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 1337。 -/
theorem R1337_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 0), (5, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_farwords (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_nil1 0) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [1]) (o := 2) (by decide) (PVF_nil (A := [1]) (o := 2) (by decide) (by decide) 0) (RLF_nil (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

end GzE
end TRIO
