/-
GxA.lean: 前の目標 `Gm = (0,0,0)(1,1,1)(2,1,0)(1,1,1)`（`GwZ.goal_mem`）を台座（`Aok`）にして、
シート行 423〜432 を出す。証明は `R338` を台座にした行 377〜395 と同じ形（台座一般の補題）。
-/
import GwZ
import GwX
import GwT

namespace TRIO
namespace GxA

open Wset
open Small
open GwS
open Gw
open GwU
open GwV
open GwW
open GwX
open GwZ

/-! ## 台座 `Gm` -/

theorem Aok_Gm : Aok Gm := by
  refine ⟨goal_mem, by simp [Gm], ?_, ?_, ?_⟩
  · refine ⟨by simp [Gm, entry], ?_⟩
    intro j hj1 hj2
    simp [Gm] at hj2
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl <;> simp [Gm, entry]
  · intro c hc h0
    simp only [Gm, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> simp_all
  · intro c hc
    simp only [Gm, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> (dsimp only; omega)

theorem Bok_000 : Bok [((0, 0, 0) : ℕ × ℕ × ℕ)] := by
  refine ⟨A1_intro (Or.inl ⟨by simp, by simp [lev, entry]⟩), ?_, ?_, by simp [entry]⟩
  · intro c hc _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc; simp
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc; simp

/-- ★ シート行 423 `(0,0,0)(1,1,1)(2,1,0)(1,1,1)(1,0,0)`。 -/
theorem R423_mem : Gm ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := Bok.append Aok_Gm Bok_000
  simpa [bump, shiftr01] using h

/-- ★ シート行 424 `… (1,1,1)(1,1,0)`。 -/
theorem R424_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  row_mem_of_GoodFb Aok_Gm GoodFb_rword_nil

theorem RunA_Gm110 : RunA 0 1 (Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ)]) :=
  ⟨0, Gm, [((1, 1, 0) : ℕ × ℕ × ℕ)], rfl, rfl, LwA_of_Aok Aok_Gm, GoodFb_rword_nil.seg 0⟩

/-- ★ シート行 425 `… (1,1,1)(1,1,0)(2,2,0)`。 -/
theorem R425_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := RunG_snoc2 Iface_RunA0 0 1 _ RunA_Gm110
  simpa using h

/-- ★ シート行 426 `… (1,1,1)(1,1,0)(2,2,1)`。 -/
theorem R426_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  row_mem_of_GoodFb Aok_Gm (GoodFb_snoczR (l := []) (by intro U hU; simp at hU) GoodFb_rword_nil)

theorem Wg2_100 : [((1, 0, 0) : ℕ × ℕ × ℕ)] ∈ Wg 2 :=
  A1g_intro (Or.inl ⟨by simp, by simp [lev, entry]⟩)

/-- ★ シート行 427 `… (1,1,1)(1,1,0)(2,2,1)(3,0,0)`。 -/
theorem R427_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hG := GOKR_of_Wg2 [((1, 0, 0) : ℕ × ℕ × ℕ)] Wg2_100 (by decide) (by unfold Mono; decide)
    [] (by intro U hU; simp at hU) GoodFb_rword_nil
  exact row_mem_of_GoodFb Aok_Gm hG

/-- ★ シート行 428 `… (1,1,1)(1,1,0)(2,2,1)(3,1,0)`。 -/
theorem R428_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  row_mem_of_GoodFb Aok_Gm GoodFb_110

/-- ★ シート行 429 `… (1,1,1)(1,1,0)(2,2,1)(3,1,0)(4,2,1)`。 -/
theorem R429_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hG := GOKR_of_Wg2 GwT.T21 GwT.T21_Wg GwT.T21_ge GwT.T21_mono [] (by intro T hT; simp at hT)
    GoodFb_rword_nil
  exact row_mem_of_GoodFb Aok_Gm hG

/-! ## 台座 `G3 = Gm ++ M3 0`（シート行 430） -/

def G3 : TrioSeq := Gm ++ M3 0

/-- ★ シート行 430 `… (1,1,1)(1,1,0)(2,2,1)(3,2,0)`。 -/
theorem R430_mem : G3 ∈ W 0 := by
  have h := (SegA_M3 0).reapp P0 BaseOk_zero 0 Gm (LwB_of_base ⟨Aok_Gm, rfl⟩)
  simpa [G3] using h

theorem RunA_G3 : RunA 0 1 G3 := ⟨0, Gm, M3 0, rfl, rfl, LwA_of_Aok Aok_Gm, SegA_M3 0⟩

theorem Aok_G3 : Aok G3 := (BaseOk_RunA 0).aok 1 _ RunA_G3

/-- ★ シート行 431 `… (1,1,1)(1,1,0)(2,2,1)(3,2,0)(2,2,0)`。 -/
theorem R431_mem : G3 ++ [((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunG_snoc2 Iface_RunA0 0 1 G3 RunA_G3

theorem pk_G3 {J : ℕ → ℕ → TrioSeq} (hG : GoodFb J) :
    G3 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ J 2 2) ∈ W 0 := by
  have hP : PkGA 2 (G3 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ J 2 2)) :=
    ⟨RunA 0, Iface_RunA0, 0, 1, G3, J 2 2, rfl, RunA_G3, rfl, hG.pk 1⟩
  exact (PkGA_Aok hP).mem

theorem UG_row : ∀ n, Gm ++ U n ∈ W 0
  | 0 => by simpa [U] using Aok_Gm.mem
  | (n + 1) => by
      rw [show Gm ++ U (n + 1) = G3 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ rword 2 2 [U n]) from by
        simp [G3, GwW.M3, U]]
      exact pk_G3 (GoodFb_U n)

theorem Mtwd_UG (n : ℕ) : Mtwd 3 Gm M5 n = Gm ++ U n := by
  unfold Mtwd
  rw [U_flat]

/-- ★ シート行 432 `… (1,1,1)(1,1,0)(2,2,1)(3,2,0)(2,2,0)(3,3,1)(4,2,0)`。 -/
theorem R432_mem : G3 ++ [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((4, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := snocYd_mem0 (Y0 := Gm) (M := M5) (L := 1) (y := 2) (dl := 3)
    (by simp [Gm]) (by simp [M5]) (by simp [M5, entry])
    (by
      intro j hj1 hj2
      simp [M5] at hj2
      rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        simp [M5, entry])
    (by simp [M5, entry])
    (by
      intro t ht1 ht2 _ _
      simp [M5] at ht2
      rcases (by omega : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4) with rfl | rfl | rfl | rfl <;>
        simp [M5, entry])
    (by omega) (by omega) (fun n => by rw [Mtwd_UG]; exact UG_row n)
  simpa [G3, GwW.M3, M5, List.append_assoc] using h

#print axioms R432_mem

end GxA
end TRIO
