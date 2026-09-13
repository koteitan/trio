/-
GxM.lean: tools/gen_gxm.py が生成。頭の直上の単位だけの中身を持つシート行。
-/
import GxL

namespace TRIO
namespace GxM

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL

/-- ★ シート行 519。 -/
theorem R519_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 0, 0), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_nil 0)))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 520。 -/
theorem R520_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 521。 -/
theorem R521_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 0, 0), (1, 1, 1), (2, 1, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_nil 0))) (WordsOK_nil 0)))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 522。 -/
theorem R522_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 0, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_nil 0)))) (WordsOK_nil 0))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 523。 -/
theorem R523_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 0, 0), (3, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))) (by omega)) rfl (RawU_nil 0))) (WordsOK_nil 0))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 524。 -/
theorem R524_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 0, 0), (3, 1, 1), (4, 1, 0), (3, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0))))) (by omega)) rfl (RawU_nil 0))) (WordsOK_nil 0))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 525。 -/
theorem R525_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 526。 -/
theorem R526_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 527。 -/
theorem R527_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1)) (WordsOK_cons (v := 1) (RawU_nil 1) (WordsOK_nil 1))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 528。 -/
theorem R528_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_nil 1))) (WordsOK_nil 1)))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 529。 -/
theorem R529_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1))) (WordsOK_nil 1)))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 530。 -/
theorem R530_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1))) (WordsOK_nil 1))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 531。 -/
theorem R531_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1))) (WordsOK_nil 1))) (Wg_of_starOK (starOK_words (v := 2) (WordsOK_nil 2))) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 532。 -/
theorem R532_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1))) (WordsOK_nil 1))) (Wg_of_starOK (starOK_words (v := 2) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_cons_some (v := 2) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 2))) (WordsOK_nil 2)))) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 533。 -/
theorem R533_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (4, 1, 0), (3, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1))) (WordsOK_nil 1))) (Wg_of_starOK (starOK_hang (starOK_words (v := 2) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_cons_some (v := 2) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 2))) (WordsOK_nil 2))) (Wg_of_starOK (starOK_words (v := 3) (WordsOK_nil 3))) rfl)) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 534。 -/
theorem R534_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_nil 1) (WordsOK_nil 1))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 535。 -/
theorem R535_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (2, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1)) (WordsOK_nil 1))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 536。 -/
theorem R536_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1)) (WordsOK_cons (v := 1) (RawU_nil 1) (WordsOK_nil 1)))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 537。 -/
theorem R537_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (2, 2, 1), (3, 2, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_nil 1))) (WordsOK_nil 1))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 538。 -/
theorem R538_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1))) (WordsOK_nil 1))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 539。 -/
theorem R539_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_nil 1)))) (WordsOK_nil 1)))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 540。 -/
theorem R540_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1)))) (WordsOK_nil 1)))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 541。 -/
theorem R541_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_nil 1)) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) rfl)) (by omega)) rfl (RawU_nil 1))) (WordsOK_nil 1)))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 542。 -/
theorem R542_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_nil 1) (WordsOK_nil 1)))) (by omega)) rfl (RawU_nil 1))) (WordsOK_nil 1)))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 543。 -/
theorem R543_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (4, 2, 1), (5, 2, 0), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1)) (WordsOK_cons (v := 1) (RawU_nil 1) (WordsOK_nil 1))))) (by omega)) rfl (RawU_nil 1))) (WordsOK_nil 1)))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 544。 -/
theorem R544_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_nil 1)))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 545。 -/
theorem R545_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (3, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_nil 1))) (Wg_of_starOK (starOK_words (v := 2) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_nil 2)) (WordsOK_cons (v := 2) (RawU_nil 2) (WordsOK_nil 2))))) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 546。 -/
theorem R546_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_nil 1))) (Wg_of_starOK (starOK_words (v := 2) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_cons_some (v := 2) (Wg_up (Wg_of_starOK (starOK_words (v := 2) (WordsOK_nil 2))) (by omega)) rfl (RawU_nil 2))) (WordsOK_nil 2)))) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 547。 -/
theorem R547_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (4, 2, 0), (3, 3, 1), (4, 3, 0), (3, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_nil 1))) (Wg_of_starOK (starOK_words (v := 2) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_cons_some (v := 2) (Wg_up (Wg_of_starOK (starOK_words (v := 2) (WordsOK_nil 2))) (by omega)) rfl (RawU_nil 2))) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_nil 2)) (WordsOK_cons (v := 2) (RawU_nil 2) (WordsOK_nil 2)))))) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 548。 -/
theorem R548_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (4, 2, 0), (3, 3, 1), (4, 3, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_nil 1))) (Wg_of_starOK (starOK_words (v := 2) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_cons_some (v := 2) (Wg_up (Wg_of_starOK (starOK_words (v := 2) (WordsOK_nil 2))) (by omega)) rfl (RawU_nil 2))) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_cons_some (v := 2) (Wg_up (Wg_of_starOK (starOK_words (v := 2) (WordsOK_nil 2))) (by omega)) rfl (RawU_nil 2))) (WordsOK_nil 2))))) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 549。 -/
theorem R549_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (4, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_nil 1))) (Wg_of_starOK (starOK_words (v := 2) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_cons_some (v := 2) (Wg_up (Wg_of_starOK (starOK_words (v := 2) (WordsOK_nil 2))) (by omega)) rfl (RawU_cons_some (v := 2) (Wg_up (Wg_of_starOK (starOK_words (v := 2) (WordsOK_nil 2))) (by omega)) rfl (RawU_nil 2)))) (WordsOK_nil 2)))) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 550。 -/
theorem R550_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_nil 1))) (Wg_of_starOK (starOK_words (v := 2) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_cons_none (v := 2) (RawU_nil 2))) (WordsOK_nil 2)))) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 551。 -/
theorem R551_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (4, 3, 0), (3, 3, 0), (4, 4, 1), (5, 4, 0), (5, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_nil 1))) (Wg_of_starOK (starOK_hang (starOK_words (v := 2) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_cons_none (v := 2) (RawU_nil 2))) (WordsOK_nil 2))) (Wg_of_starOK (starOK_words (v := 3) (WordsOK_cons (v := 3) (RawU_cons_none (v := 3) (RawU_cons_none (v := 3) (RawU_nil 3))) (WordsOK_nil 3)))) rfl)) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 552。 -/
theorem R552_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 553。 -/
theorem R553_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (1, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 554。 -/
theorem R554_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_nil 1) (WordsOK_nil 1)))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 555。 -/
theorem R555_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1)) (WordsOK_cons (v := 1) (RawU_nil 1) (WordsOK_nil 1))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 556。 -/
theorem R556_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_nil 1) (WordsOK_nil 1))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 557。 -/
theorem R557_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 1), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_nil 1) (WordsOK_nil 1)))) (Wg_of_starOK (starOK_words (v := 2) (WordsOK_nil 2))) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 558。 -/
theorem R558_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 1), (2, 2, 0), (3, 3, 1), (4, 3, 0), (4, 3, 0), (3, 3, 1), (3, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_nil 1) (WordsOK_nil 1)))) (Wg_of_starOK (starOK_hang (starOK_words (v := 2) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_cons_none (v := 2) (RawU_nil 2))) (WordsOK_cons (v := 2) (RawU_nil 2) (WordsOK_nil 2)))) (Wg_of_starOK (starOK_words (v := 3) (WordsOK_nil 3))) rfl)) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 559。 -/
theorem R559_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 560。 -/
theorem R560_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 561。 -/
theorem R561_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_nil 0)) (WordsOK_nil 0)))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 562。 -/
theorem R562_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_nil 0)))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 563。 -/
theorem R563_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 1), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1)) (WordsOK_nil 1))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 564。 -/
theorem R564_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 1), (3, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1)) (WordsOK_cons (v := 1) (RawU_nil 1) (WordsOK_nil 1)))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 565。 -/
theorem R565_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 1), (3, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1))) (WordsOK_nil 1))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 566。 -/
theorem R566_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1)) (WordsOK_nil 1))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 567。 -/
theorem R567_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 1), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (4, 3, 0), (3, 3, 1), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1)) (WordsOK_nil 1)))) (Wg_of_starOK (starOK_words (v := 2) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_cons_none (v := 2) (RawU_nil 2))) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_nil 2)) (WordsOK_nil 2))))) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 568。 -/
theorem R568_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 569。 -/
theorem R569_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 570。 -/
theorem R570_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_nil 0))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 571。 -/
theorem R571_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 572。 -/
theorem R572_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_nil 0))) (WordsOK_nil 0)))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 573。 -/
theorem R573_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0)))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 574。 -/
theorem R574_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1))) (WordsOK_nil 1))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 575。 -/
theorem R575_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1)) (WordsOK_cons (v := 1) (RawU_nil 1) (WordsOK_nil 1))))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 576。 -/
theorem R576_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 1), (3, 2, 0), (3, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1)))) (WordsOK_nil 1))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 577。 -/
theorem R577_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_nil 1))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 578。 -/
theorem R578_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (4, 3, 0), (3, 3, 1), (4, 3, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0)))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_nil 1)))) (Wg_of_starOK (starOK_words (v := 2) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_cons_none (v := 2) (RawU_nil 2))) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_cons_none (v := 2) (RawU_nil 2))) (WordsOK_nil 2))))) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 579。 -/
theorem R579_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 580。 -/
theorem R580_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 581。 -/
theorem R581_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_nil 0))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 582。 -/
theorem R582_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 583。 -/
theorem R583_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 584。 -/
theorem R584_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 585。 -/
theorem R585_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_nil 0)))) (WordsOK_nil 0))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 586。 -/
theorem R586_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_nil 0)))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 587。 -/
theorem R587_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 0, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_nil 0))))) (WordsOK_nil 0))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 588。 -/
theorem R588_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 0, 0), (3, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))) (by omega)) rfl (RawU_nil 0)))) (WordsOK_nil 0))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 589。 -/
theorem R589_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_nil 0))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 590。 -/
theorem R590_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_nil 1) (WordsOK_nil 1))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 591。 -/
theorem R591_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1)))) (WordsOK_nil 1)))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 592。 -/
theorem R592_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (3, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1)))) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))) (WordsOK_cons (v := 1) (RawU_nil 1) (WordsOK_nil 1)))))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 593。 -/
theorem R593_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (3, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_nil 1))) (by omega)) rfl (RawU_nil 1))))) (WordsOK_nil 1)))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 594。 -/
theorem R594_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (3, 1, 0), (4, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_cons_some (v := 1) (Wg_up (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_nil 1) (WordsOK_nil 1)))) (by omega)) rfl (RawU_nil 1)))) (WordsOK_nil 1)))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 595。 -/
theorem R595_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1)))) (WordsOK_nil 1)))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 596。 -/
theorem R596_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (4, 3, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_hang (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1)))) (WordsOK_nil 1))) (Wg_of_starOK (starOK_words (v := 2) (WordsOK_cons (v := 2) (RawU_cons_none (v := 2) (RawU_cons_none (v := 2) (RawU_cons_none (v := 2) (RawU_nil 2)))) (WordsOK_nil 2)))) rfl)) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 597。 -/
theorem R597_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 598。 -/
theorem R598_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 599。 -/
theorem R599_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_nil 0)))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 600。 -/
theorem R600_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 601。 -/
theorem R601_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_nil 0)))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 602。 -/
theorem R602_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 603。 -/
theorem R603_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_nil 0)))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 604。 -/
theorem R604_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0))))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 605。 -/
theorem R605_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_some (v := 0) (Wg_up (Wg_of_starOK (starOK_words (v := 0) (WordsOK_nil 0))) (by omega)) rfl (RawU_nil 0))))) (WordsOK_nil 0))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 606。 -/
theorem R606_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))))) (WordsOK_nil 0))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 607。 -/
theorem R607_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (3, 2, 0), (3, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))))) (WordsOK_nil 0))) (Wg_of_starOK (starOK_words (v := 1) (WordsOK_cons (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_cons_none (v := 1) (RawU_nil 1))))) (WordsOK_nil 1)))) rfl))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 608。 -/
theorem R608_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 609。 -/
theorem R609_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))))) (WordsOK_nil 0))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 610。 -/
theorem R610_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0)))))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

/-- ★ シート行 611。 -/
theorem R611_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_words (v := 0) (WordsOK_cons (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_cons_none (v := 0) (RawU_nil 0))))))) (WordsOK_cons (v := 0) (RawU_nil 0) (WordsOK_nil 0)))))
  simpa [unitsC, unitC, rword, rcol, shiftr01] using h

#print axioms R519_mem
#print axioms R586_mem
#print axioms R611_mem

end GxM
end TRIO
