/-
GxO.lean: tools/gen_gxo.py が生成。錐のタイの森と荷の中身を持つシート行。
-/
import GxN

namespace TRIO
namespace GxO

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN

/-- ★ シート行 612。 -/
theorem R612_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 613。 -/
theorem R613_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 614。 -/
theorem R614_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 615。 -/
theorem R615_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 616。 -/
theorem R616_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_seq (SCF_load (u := 0) 0 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 0 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 617。 -/
theorem R617_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 618。 -/
theorem R618_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 619。 -/
theorem R619_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0)))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 620。 -/
theorem R620_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (2, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 621。 -/
theorem R621_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 622。 -/
theorem R622_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_nil 0)) (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) rfl)) (by omega)) rfl) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 623。 -/
theorem R623_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_nil 0)) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl)) (by omega)) rfl) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 624。 -/
theorem R624_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (4, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 625。 -/
theorem R625_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 627。 -/
theorem R627_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 628。 -/
theorem R628_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 629。 -/
theorem R629_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1)) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 630。 -/
theorem R630_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 631。 -/
theorem R631_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 632。 -/
theorem R632_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 633。 -/
theorem R633_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (2, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 634。 -/
theorem R634_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 1, 0), (3, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 2) (WordsG_cons (v := 2) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_load (u := 2) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 2))) (SCF_nil 0 2)) (WordsG_nil 2))) (Wg_of_starOK (starOK_wordsG (v := 3) (WordsG_nil 3))) rfl)) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 635。 -/
theorem R635_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 636。 -/
theorem R636_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (2, 2, 1), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1)))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 637。 -/
theorem R637_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (2, 2, 1), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_cons (v := 1) (SCF_seq (SCF_load (u := 1) 0 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 0 1)) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 638。 -/
theorem R638_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (2, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1)) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 639。 -/
theorem R639_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (2, 2, 1), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1)) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1)))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 640。 -/
theorem R640_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (2, 2, 1), (3, 2, 0), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 641。 -/
theorem R641_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 642。 -/
theorem R642_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_load (u := 1) 0 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 0 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 643。 -/
theorem R643_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_load (u := 1) 0 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 0 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 644。 -/
theorem R644_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 645。 -/
theorem R645_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 1, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_cons (v := 2) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_load (u := 2) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 2))) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_nil 1 2)) (SCF_nil 0 2))) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 646。 -/
theorem R646_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1))) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 647。 -/
theorem R647_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (3, 2, 0), (2, 2, 1), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1))) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1)))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 648。 -/
theorem R648_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (3, 2, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1))) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1))) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1)))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 649。 -/
theorem R649_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (3, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 650。 -/
theorem R650_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (3, 2, 0), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1)))) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 651。 -/
theorem R651_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (3, 2, 0), (3, 2, 0), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1))))) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 654。 -/
theorem R654_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (3, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 655。 -/
theorem R655_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (3, 2, 0), (4, 1, 0), (3, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 656。 -/
theorem R656_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 1)))) (SCF_nil 0 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 657。 -/
theorem R657_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1)))) (SCF_nil 0 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 658。 -/
theorem R658_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_nil 1)) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl)) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 659。 -/
theorem R659_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (5, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1)))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 660。 -/
theorem R660_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 1, 0), (5, 2, 1), (6, 2, 0), (7, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1)))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 661。 -/
theorem R661_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 662。 -/
theorem R662_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_cons (v := 2) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_load (u := 2) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) (by omega)) rfl) (SCF_nil 1 2))) (SCF_nil 0 2)) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 663。 -/
theorem R663_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 2, 0), (3, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_cons (v := 2) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_load (u := 2) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) (by omega)) rfl) (SCF_nil 1 2))) (SCF_nil 0 2)) (WordsG_cons (v := 2) (SCF_nil 0 2) (WordsG_nil 2))))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 664。 -/
theorem R664_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_cons (v := 2) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_load (u := 2) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) (by omega)) rfl) (SCF_nil 1 2))) (SCF_seq (SCF_load (u := 2) 0 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) (by omega)) rfl) (SCF_nil 0 2))) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 665。 -/
theorem R665_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 2, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_cons (v := 2) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_load (u := 2) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) (by omega)) rfl) (SCF_nil 1 2))) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_nil 1 2)) (SCF_nil 0 2))) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 666。 -/
theorem R666_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 2, 0), (4, 3, 0), (3, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_cons (v := 2) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_load (u := 2) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) (by omega)) rfl) (SCF_nil 1 2))) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_nil 1 2)) (SCF_nil 0 2))) (WordsG_cons (v := 2) (SCF_nil 0 2) (WordsG_nil 2))))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 667。 -/
theorem R667_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 2, 0), (4, 3, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_cons (v := 2) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_load (u := 2) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) (by omega)) rfl) (SCF_nil 1 2))) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_load (u := 2) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) (by omega)) rfl) (SCF_nil 1 2))) (SCF_nil 0 2))) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 668。 -/
theorem R668_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 2, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_cons (v := 2) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_load (u := 2) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) (by omega)) rfl) (SCF_seq (SCF_load (u := 2) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_nil 2))) (by omega)) rfl) (SCF_nil 1 2)))) (SCF_nil 0 2)) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 669。 -/
theorem R669_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_cons (v := 2) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_child (d := 1) (u := 2) (SCF_nil 2 2)) (SCF_nil 1 2))) (SCF_nil 0 2)) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 670。 -/
theorem R670_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 3, 0), (3, 3, 0), (4, 4, 1), (5, 4, 0), (6, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 2) (WordsG_cons (v := 2) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_child (d := 1) (u := 2) (SCF_nil 2 2)) (SCF_nil 1 2))) (SCF_nil 0 2)) (WordsG_nil 2))) (Wg_of_starOK (starOK_wordsG (v := 3) (WordsG_cons (v := 3) (SCF_seq (SCF_child (d := 0) (u := 3) (SCF_seq (SCF_child (d := 1) (u := 3) (SCF_nil 2 3)) (SCF_nil 1 3))) (SCF_nil 0 3)) (WordsG_nil 3)))) rfl)) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 671。 -/
theorem R671_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 672。 -/
theorem R672_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (1, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 675。 -/
theorem R675_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 676。 -/
theorem R676_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 677。 -/
theorem R677_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_load (u := 0) 0 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 0 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 678。 -/
theorem R678_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 679。 -/
theorem R679_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (2, 2, 1), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0)) (WordsG_nil 0)))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1)) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 680。 -/
theorem R680_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 681。 -/
theorem R681_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 682。 -/
theorem R682_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 683。 -/
theorem R683_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0), (4, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 684。 -/
theorem R684_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 686。 -/
theorem R686_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 687。 -/
theorem R687_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 688。 -/
theorem R688_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 689。 -/
theorem R689_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 690。 -/
theorem R690_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 691。 -/
theorem R691_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_load (u := 0) 0 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 0 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 692。 -/
theorem R692_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 0, 0), (3, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_load (u := 0) 0 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))) (by omega)) rfl) (SCF_nil 0 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 693。 -/
theorem R693_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 694。 -/
theorem R694_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (3, 1, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_seq (SCF_load (u := 1) 0 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 0 1))) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 696。 -/
theorem R696_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (3, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_seq (SCF_load (u := 1) 0 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_seq (SCF_load (u := 1) 0 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 0 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 697。 -/
theorem R697_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 698。 -/
theorem R698_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (3, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 3, 0), (4, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_cons (v := 2) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_child (d := 1) (u := 2) (SCF_nil 2 2)) (SCF_nil 1 2))) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_nil 1 2)) (SCF_nil 0 2))) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 699。 -/
theorem R699_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 700。 -/
theorem R700_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 701。 -/
theorem R701_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 702。 -/
theorem R702_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 703。 -/
theorem R703_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 704。 -/
theorem R704_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 705。 -/
theorem R705_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 706。 -/
theorem R706_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_seq (SCF_load (u := 0) 0 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 0 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 707。 -/
theorem R707_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 708。 -/
theorem R708_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0)))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 709。 -/
theorem R709_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 710。 -/
theorem R710_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 711。 -/
theorem R711_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 0, 0), (4, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 712。 -/
theorem R712_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 713。 -/
theorem R713_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (3, 2, 0), (4, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 714。 -/
theorem R714_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (3, 2, 0), (4, 1, 0), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1)))) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 715。 -/
theorem R715_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (3, 2, 0), (4, 1, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1)))) (SCF_nil 0 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 716。 -/
theorem R716_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_nil 0 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 717。 -/
theorem R717_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (3, 2, 0), (4, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 3, 0), (4, 3, 0), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_nil 0 1))) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_cons (v := 2) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_child (d := 1) (u := 2) (SCF_nil 2 2)) (SCF_nil 1 2))) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_child (d := 1) (u := 2) (SCF_nil 2 2)) (SCF_nil 1 2))) (SCF_nil 0 2))) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 718。 -/
theorem R718_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 719。 -/
theorem R719_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 1), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 720。 -/
theorem R720_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 721。 -/
theorem R721_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 722。 -/
theorem R722_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_load (u := 0) 0 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 0 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 723。 -/
theorem R723_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 724。 -/
theorem R724_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0)))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 725。 -/
theorem R725_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 726。 -/
theorem R726_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_nil 0 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 727。 -/
theorem R727_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 728。 -/
theorem R728_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (3, 2, 0), (4, 2, 0), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)))) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_nil 0 1)))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 729。 -/
theorem R729_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 730。 -/
theorem R730_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 731。 -/
theorem R731_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0))))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 732。 -/
theorem R732_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 733。 -/
theorem R733_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 0, 0), (4, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))) (by omega)) rfl) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 734。 -/
theorem R734_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 735。 -/
theorem R735_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (4, 1, 0), (3, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1)))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 736。 -/
theorem R736_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (4, 1, 0), (3, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1)))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_nil 1 1)) (SCF_nil 0 1))) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 737。 -/
theorem R737_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (4, 1, 0), (3, 2, 0), (4, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1)))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1))) (SCF_nil 0 1))) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 738。 -/
theorem R738_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (4, 1, 0), (3, 2, 0), (4, 2, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1)))) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1)))) (SCF_nil 0 1))) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 739。 -/
theorem R739_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (4, 1, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_seq (SCF_load (u := 1) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 1 1))))) (SCF_nil 0 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 740。 -/
theorem R740_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1)))) (SCF_nil 0 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 741。 -/
theorem R741_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (4, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 3, 0), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1)))) (SCF_nil 0 1)) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_cons (v := 2) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_child (d := 1) (u := 2) (SCF_nil 2 2)) (SCF_seq (SCF_child (d := 1) (u := 2) (SCF_nil 2 2)) (SCF_nil 1 2)))) (SCF_nil 0 2)) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 742。 -/
theorem R742_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 743。 -/
theorem R743_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0))))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 744。 -/
theorem R744_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (2, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_seq (SCF_load (u := 0) 0 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 0 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 745。 -/
theorem R745_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (2, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 746。 -/
theorem R746_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 747。 -/
theorem R747_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (2, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0)))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 748。 -/
theorem R748_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (2, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 749。 -/
theorem R749_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 750。 -/
theorem R750_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 751。 -/
theorem R751_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))) (SCF_nil 0 0)))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 752。 -/
theorem R752_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_load (u := 0) 1 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 1 0)))) (SCF_nil 0 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 753。 -/
theorem R753_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_nil 0 0))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 754。 -/
theorem R754_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 755。 -/
theorem R755_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (3, 1, 0), (2, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_nil 0 0)))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 756。 -/
theorem R756_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 757。 -/
theorem R757_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 758。 -/
theorem R758_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (3, 1, 0), (3, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 759。 -/
theorem R759_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 760。 -/
theorem R760_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (3, 1, 0), (3, 1, 0), (3, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0))))))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 761。 -/
theorem R761_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_load (u := 0) 2 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 762。 -/
theorem R762_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 0, 0), (5, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_load (u := 0) 2 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))) (by omega)) rfl) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 763。 -/
theorem R763_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_nil 3 0)) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 764。 -/
theorem R764_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (5, 1, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_nil 3 0)) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_seq (SCF_load (u := 1) 2 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 2 1))) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1)))) (SCF_nil 0 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 765。 -/
theorem R765_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (5, 1, 0), (4, 2, 0), (2, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_nil 3 0)) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_seq (SCF_load (u := 1) 2 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 2 1))) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_nil 2 1)) (SCF_nil 1 1)))) (SCF_nil 0 1)) (WordsG_cons (v := 1) (SCF_nil 0 1) (WordsG_nil 1))))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 766。 -/
theorem R766_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (5, 1, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_nil 3 0)) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_seq (SCF_load (u := 1) 2 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_seq (SCF_load (u := 1) 2 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_nil 1))) (by omega)) rfl) (SCF_nil 2 1)))) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 767。 -/
theorem R767_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (5, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_nil 3 0)) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_seq (SCF_child (d := 2) (u := 1) (SCF_nil 3 1)) (SCF_nil 2 1))) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1)))) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 768。 -/
theorem R768_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (1, 1, 0), (2, 2, 1), (3, 2, 0), (4, 2, 0), (5, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 0), (5, 3, 0), (6, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_nil 3 0)) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))) (Wg_of_starOK (starOK_hang (starOK_wordsG (v := 1) (WordsG_cons (v := 1) (SCF_seq (SCF_child (d := 0) (u := 1) (SCF_seq (SCF_child (d := 1) (u := 1) (SCF_seq (SCF_child (d := 2) (u := 1) (SCF_nil 3 1)) (SCF_nil 2 1))) (SCF_nil 1 1))) (SCF_nil 0 1)) (WordsG_nil 1))) (Wg_of_starOK (starOK_wordsG (v := 2) (WordsG_cons (v := 2) (SCF_seq (SCF_child (d := 0) (u := 2) (SCF_seq (SCF_child (d := 1) (u := 2) (SCF_seq (SCF_child (d := 2) (u := 2) (SCF_nil 3 2)) (SCF_nil 2 2))) (SCF_nil 1 2))) (SCF_nil 0 2)) (WordsG_nil 2)))) rfl)) rfl))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 769。 -/
theorem R769_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_nil 3 0)) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 770。 -/
theorem R770_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (2, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_nil 3 0)) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_nil 1 0)) (SCF_nil 0 0))) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 771。 -/
theorem R771_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (3, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_nil 3 0)) (SCF_nil 2 0))) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_nil 2 0)) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 772。 -/
theorem R772_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (3, 1, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_nil 3 0)) (SCF_nil 2 0))) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_nil 3 0)) (SCF_nil 2 0))) (SCF_nil 1 0)))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 773。 -/
theorem R773_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (4, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_nil 3 0)) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_nil 3 0)) (SCF_nil 2 0)))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 774。 -/
theorem R774_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (5, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_seq (SCF_load (u := 0) 3 (Wg_up (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_nil 0))) (by omega)) rfl) (SCF_nil 3 0))) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 775。 -/
theorem R775_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (5, 1, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_seq (SCF_child (d := 3) (u := 0) (SCF_nil 4 0)) (SCF_nil 3 0))) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 776。 -/
theorem R776_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (5, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_seq (SCF_child (d := 3) (u := 0) (SCF_nil 4 0)) (SCF_nil 3 0))) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 777。 -/
theorem R777_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (5, 1, 0), (5, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_seq (SCF_child (d := 3) (u := 0) (SCF_nil 4 0)) (SCF_seq (SCF_child (d := 3) (u := 0) (SCF_nil 4 0)) (SCF_nil 3 0)))) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 778。 -/
theorem R778_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (5, 1, 0), (6, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_seq (SCF_child (d := 3) (u := 0) (SCF_seq (SCF_child (d := 4) (u := 0) (SCF_nil 5 0)) (SCF_nil 4 0))) (SCF_nil 3 0))) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

/-- ★ シート行 779。 -/
theorem R779_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 1, 0), (4, 1, 0), (5, 1, 0), (6, 1, 0), (7, 1, 0), (1, 1, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0) (WordsG_cons (v := 0) (SCF_seq (SCF_child (d := 0) (u := 0) (SCF_seq (SCF_child (d := 1) (u := 0) (SCF_seq (SCF_child (d := 2) (u := 0) (SCF_seq (SCF_child (d := 3) (u := 0) (SCF_seq (SCF_child (d := 4) (u := 0) (SCF_seq (SCF_child (d := 5) (u := 0) (SCF_nil 6 0)) (SCF_nil 5 0))) (SCF_nil 4 0))) (SCF_nil 3 0))) (SCF_nil 2 0))) (SCF_nil 1 0))) (SCF_nil 0 0)) (WordsG_cons (v := 0) (SCF_nil 0 0) (WordsG_nil 0)))))
  simpa [shiftr01, rword, rcol] using h

#print axioms R612_mem
#print axioms R779_mem

end GxO
end TRIO
