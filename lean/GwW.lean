/-
GwW.lean: 目標の `[2]` の塊 `M3 = (1,1,0)(2,2,1)(3,2,0)` を台座一般のセグメントにし、
シート行 386〜394 を出す。

- `SegA_M3 h : SegA h [(h+1,1,0),(h+2,2,1),(h+3,2,0)]`: 任意の梯子の頭の上で `M3` を継げる。
  `GwV.R385_mem` の証明の `row_mem_of_GoodFb` を `GoodFb` の `seg` 欄に替えたもの。
- `RunA 0 1 (R338 ++ M3)` から `Aok` / `ancd` / `hang` / `RunG_snoc2` / `PkGA` が使える。
-/
import GwV

namespace TRIO
namespace GwW

open Wset
open Small
open GwS
open Gw
open GwU
open GwV

/-! ## 中身の族 `Tc` の語は良い語 -/

theorem GoodFb_Tc (n : ℕ) : GoodFb (fun a b => rword a b [Tc n]) := by
  have h := GOKR_of_Wg2 (Tc n) (Tc_Wg n) (Tc_ge n) (Tc_mono n) [] (by intro U hU; simp at hU)
    GoodFb_rword_nil
  simpa using h

theorem shift_Tc (g n : ℕ) :
    shiftr01 g 0 (Tc (n + 1)) = ((g + 1, 1, 0) : ℕ × ℕ × ℕ) :: rword (g + 1) 1 [Tc n] := by
  show shiftr01 g 0 (((1, 1, 0) : ℕ × ℕ × ℕ) :: rword 1 1 [Tc n]) = _
  rw [show ((1, 1, 0) : ℕ × ℕ × ℕ) :: rword 1 1 [Tc n]
      = [((1, 1, 0) : ℕ × ℕ × ℕ)] ++ rword 1 1 [Tc n] from rfl,
    shiftr01_append0, shift_col, rword_shift, Nat.add_comm 1 g]
  rfl

theorem M2_shift (g : ℕ) :
    shiftr01 g 0 GwV.M2 = [((g + 1, 1, 0) : ℕ × ℕ × ℕ), ((g + 2, 2, 1) : ℕ × ℕ × ℕ)] := by
  simp only [GwV.M2, shiftr01, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
    and_true] <;> omega

theorem Mtwd_shift (A : TrioSeq) (g n : ℕ) :
    Mtwd 2 A [((g + 1, 1, 0) : ℕ × ℕ × ℕ), ((g + 2, 2, 1) : ℕ × ℕ × ℕ)] n
      = A ++ shiftr01 g 0 (Tc n) := by
  unfold Mtwd
  congr 1
  rw [← Tc_flat n, shiftr01_flatMap, ← M2_shift g]
  apply List.flatMap_congr
  intro k _
  rw [shiftr01_add0, shiftr01_add0, Nat.add_comm]

theorem Tcrow_LwB {P : ℕ → TrioSeq → Prop} (hP : BaseOk P) {g : ℕ} {A : TrioSeq}
    (hA : LwB P g A) : ∀ n, A ++ shiftr01 g 0 (Tc n) ∈ W 0
  | 0 => by
      have h := (LwB_Aok hP hA).mem
      simpa [Tc, shiftr01] using h
  | (n + 1) => by
      rw [shift_Tc]
      have h := ((GoodFb_Tc n).seg g).reapp P hP 0 A (by simpa using hA)
      simpa using h

/-! ## セグメント `M3` -/

def M3 (h : ℕ) : TrioSeq :=
  [((h + 1, 1, 0) : ℕ × ℕ × ℕ), ((h + 2, 2, 1) : ℕ × ℕ × ℕ), ((h + 3, 2, 0) : ℕ × ℕ × ℕ)]

theorem M3_shift (h s : ℕ) : shiftr01 s 0 (M3 h) = M3 (h + s) := by
  simp only [M3, shiftr01, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨Prod.ext (by dsimp only; omega) rfl, Prod.ext (by dsimp only; omega) rfl,
    Prod.ext (by dsimp only; omega) rfl⟩

theorem MidD_M3 (h : ℕ) : MidD (h + 2) (M3 h) := by
  refine ⟨by simp [M3], ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [M3, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> (dsimp only; omega)
  · simp [M3, entry]
  · simp [M3, entry]
  · intro j hj1 hj2
    simp [M3] at hj2
    rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl <;> simp [M3, entry] <;> omega
  · intro c hc
    simp only [M3, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> (dsimp only; omega)

theorem SegA_M3 (h : ℕ) : SegA h (M3 h) where
  mid := MidD_M3 h
  head1 := by simp [M3, entry]
  reapp := by
    intro P hP s A hA
    rw [M3_shift]
    set g := h + s with hg
    have hne : A ≠ [] := (LwB_Aok hP hA).ne
    have hmem := snocYd_mem0 (Y0 := A)
      (M := [((g + 1, 1, 0) : ℕ × ℕ × ℕ), ((g + 2, 2, 1) : ℕ × ℕ × ℕ)])
      (L := g + 1) (y := 2) (dl := 2) hne (by simp) (by simp [entry])
      (by
        intro j hj1 hj2
        simp at hj2
        have : j = 1 := by omega
        subst this
        simp [entry])
      (by simp [entry])
      (by
        intro t ht1 ht2 _ _
        simp at ht2
        have : t = 1 := by omega
        subst this
        simp [entry])
      (by omega) (by omega)
      (fun n => by rw [Mtwd_shift]; exact Tcrow_LwB hP (by simpa [hg] using hA) n)
    have e : M3 g = [((g + 1, 1, 0) : ℕ × ℕ × ℕ), ((g + 2, 2, 1) : ℕ × ℕ × ℕ)] ++
        [((g + 1 + 2, 2, 0) : ℕ × ℕ × ℕ)] := by
      simp only [M3, List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq, and_true,
        true_and]
    rw [e, ← List.append_assoc]
    exact hmem

#print axioms SegA_M3

/-! ## 台座 `G2 = R338 ++ M3 0`（シート行 385）の上 -/

def G2 : TrioSeq := R338 ++ M3 0

theorem RunA_G2 : RunA 0 1 G2 := ⟨0, R338, M3 0, rfl, rfl, LwA_of_Aok Aok_R338, SegA_M3 0⟩

theorem Aok_G2 : Aok G2 := (BaseOk_RunA 0).aok 1 _ RunA_G2

/-- ★ シート行 386 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,2,0)(1,1,0)`。 -/
theorem R386_mem : G2 ++ [((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  row_mem_of_GoodFb Aok_G2 GoodFb_rword_nil

/-- ★ シート行 387 `… (3,2,0)(1,1,0)(2,2,1)`。 -/
theorem R387_mem : G2 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  row_mem_of_GoodFb Aok_G2 (GoodFb_snoczR (l := []) (by intro U hU; simp at hU) GoodFb_rword_nil)

theorem GoodFb_110 : GoodFb (fun a b => rword a b [[((1, 1, 0) : ℕ × ℕ × ℕ)]]) := by
  have h := GOKR_of_Wg2 [((1, 1, 0) : ℕ × ℕ × ℕ)] Wg2_110 (by decide)
    (by unfold Mono; decide) [] (by intro U hU; simp at hU) GoodFb_rword_nil
  simpa using h

/-- ★ シート行 388 `… (3,2,0)(1,1,0)(2,2,1)(3,1,0)`。 -/
theorem R388_mem : G2 ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  row_mem_of_GoodFb Aok_G2 GoodFb_110

/-- ★ シート行 389 `… (3,2,0)(1,1,0)(2,2,1)(3,2,0)`。 -/
theorem R389_mem : G2 ++ M3 0 ∈ W 0 := by
  have h := (SegA_M3 0).reapp P0 BaseOk_zero 0 G2 (LwB_of_base ⟨Aok_G2, rfl⟩)
  simpa using h

theorem Aok_M3pow : ∀ n, Aok (R338 ++ (List.range n).flatMap (fun _ => M3 0))
  | 0 => by simpa using Aok_R338
  | (n + 1) => by
      have ih := Aok_M3pow n
      have hR : RunA 0 1 ((R338 ++ (List.range n).flatMap (fun _ => M3 0)) ++ M3 0) :=
        ⟨0, _, M3 0, rfl, rfl, LwA_of_Aok ih, SegA_M3 0⟩
      have h := (BaseOk_RunA 0).aok 1 _ hR
      rw [List.range_succ, List.flatMap_append]
      simpa [List.append_assoc] using h

/-- ★ シート行 390 `… (3,2,0)(2,0,0)`。 -/
theorem R390_mem : G2 ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := flat_mem'' (Y0 := R338) (M := M3 0) (d := 2) (by simp [M3]) (by simp [M3, entry])
    (by
      intro r hr1 hr2
      simp [M3] at hr2
      rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl <;> simp [M3, entry])
    (fun n => (Aok_M3pow n).mem)
  simpa [G2] using h

/-- ★ シート行 391 `… (3,2,0)(2,1,0)`。 -/
theorem R391_mem : G2 ++ [((2, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  snocd_gen (d := 2) (by omega) Aok_G2 ((BaseOk_RunA 0).ancd 1 _ RunA_G2)
    ((BaseOk_RunA 0).hang 1 _ RunA_G2)

/-- ★ シート行 392 `… (3,2,0)(2,2,0)`。 -/
theorem R392_mem : G2 ++ [((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  RunG_snoc2 Iface_RunA0 0 1 G2 RunA_G2

/-- pk の文脈（`(2,2,0)` の記録）の上の良い語。 -/
theorem pk_G2 {J : ℕ → ℕ → TrioSeq} (hG : GoodFb J) :
    G2 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ J 2 2) ∈ W 0 := by
  have hP : PkGA 2 (G2 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ J 2 2)) :=
    ⟨RunA 0, Iface_RunA0, 0, 1, G2, J 2 2, rfl, RunA_G2, rfl, hG.pk 1⟩
  exact (PkGA_Aok hP).mem

/-- ★ シート行 393 `… (3,2,0)(2,2,0)(3,3,1)`。 -/
theorem R393_mem : G2 ++ [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  pk_G2 (GoodFb_snoczR (l := []) (by intro U hU; simp at hU) GoodFb_rword_nil)

/-- ★ シート行 394 `… (3,2,0)(2,2,0)(3,3,1)(4,1,0)`。 -/
theorem R394_mem : G2 ++ [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((4, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 :=
  pk_G2 GoodFb_110

#print axioms R394_mem

end GwW
end TRIO
