/-
GwV.lean: シート行 379〜385。

行 379〜384 は `R338 ++ (1,1,0) :: rword 1 1 [(1,1,0) :: rword 1 1 l']`（字の中身の中に字）。
中身は `GwU.content_mem` で `Wg 2`、行は `GwS.GOKR_of_Wg2` で出る。
行 385 = `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,2,0)` は、中身の族
`Tc (n+1) = (1,1,0) :: rword 1 1 [Tc n]` の極限（`snocYd_mem0`、歩幅 2）。
-/
import GwU

namespace TRIO
namespace GwV

open Wset
open Small
open GwS
open Gw
open GwU

/-! ## 共通の部品 -/

theorem row_content {T : TrioSeq} (hT : T ∈ Wg 2) (hge : ∀ x ∈ T, 1 ≤ x.1) (hmo : Mono T) :
    R338 ++ (((1, 1, 0) : ℕ × ℕ × ℕ) :: rword 1 1 [T]) ∈ W 0 := by
  have hG := GOKR_of_Wg2 T hT hge hmo [] (by intro U hU; simp at hU) GoodFb_rword_nil
  have h := row_mem_of_GoodFb Aok_R338 hG
  rwa [List.nil_append] at h

theorem content_ge (l : List TrioSeq) :
    ∀ x ∈ (((1, 1, 0) : ℕ × ℕ × ℕ) :: rword 1 1 l), 1 ≤ x.1 := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · show 1 ≤ 1; omega
  · have := rword_ge 1 1 l x hx; omega

theorem Bw_one {T : TrioSeq} (hT : T ∈ Wg 2) (hge : ∀ x ∈ T, 1 ≤ x.1) : Bw [T] := by
  have h := Bw_snoc_mem (l := []) (by intro U hU; simp at hU) Bw_nil hT hge
  simpa using h

theorem RawW_of_Wg2 {T : TrioSeq} (hT : T ∈ Wg 2) (hge : ∀ x ∈ T, 1 ≤ x.1) : RawW T :=
  ⟨hge, Wg2_RiseOk hT⟩

theorem Wg2_110 : [((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ Wg 2 := by
  have h := tree_mem_Wg (p0 := ((1, 1, 0) : ℕ × ℕ × ℕ)) (R := [])
    (by unfold Z2s; decide) (by intro q hq; simp at hq)
  simpa using h

theorem Wg2_110_110 : [((1, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ Wg 2 :=
  mem_Wg_of_bound 2 _ (by simp) (by unfold Z2s; decide) 2 (by decide)

theorem Wg2_110_220 : [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ Wg 2 := by
  have h := tree_mem_Wg (p0 := ((1, 1, 0) : ℕ × ℕ × ℕ)) (R := [((2, 2, 0) : ℕ × ℕ × ℕ)])
    (by unfold Z2s; decide) (by decide)
  simpa using h

/-! ## 語 `l'` の `Bw` -/

theorem B379 : Bw [[((1, 1, 0) : ℕ × ℕ × ℕ)]] := Bw_one Wg2_110 (by decide)

theorem B380 : Bw [[((1, 1, 0) : ℕ × ℕ × ℕ)], []] := by
  have h := Bw_snocz (l := [[((1, 1, 0) : ℕ × ℕ × ℕ)]])
    (WOkW_singleton (RawW_of_Wg2 Wg2_110 (by decide))) B379
  simpa using h

theorem B381 : Bw [[((1, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ)]] :=
  Bw_one Wg2_110_110 (by decide)

theorem B382 : Bw [[((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ)]] :=
  Bw_one Wg2_110_220 (by decide)

theorem B383 : Bw [GwT.T21] := Bw_one GwT.T21_Wg GwT.T21_ge

theorem B384 : Bw [((1, 1, 0) : ℕ × ℕ × ℕ) :: rword 1 1 [[((1, 1, 0) : ℕ × ℕ × ℕ)]]] :=
  Bw_one (content_mem B379) (content_ge _)

/-! ## シート行 379〜384 -/

/-- ★ シート行 379 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,1)(5,1,0)`。 -/
theorem R379_mem : R341 ++ [((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 1) : ℕ × ℕ × ℕ),
    ((5, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := row_content (content_mem B379) (content_ge _)
    (by show Mono [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ)]
        unfold Mono; decide)
  exact h

/-- ★ シート行 380 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,1)(5,1,0)(4,2,1)`。 -/
theorem R380_mem : R341 ++ [((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 1) : ℕ × ℕ × ℕ),
    ((5, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := row_content (content_mem B380) (content_ge _)
    (by show Mono [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ),
          ((2, 2, 1) : ℕ × ℕ × ℕ)]
        unfold Mono; decide)
  exact h

/-- ★ シート行 381 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,1)(5,1,0)(5,1,0)`。 -/
theorem R381_mem : R341 ++ [((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 1) : ℕ × ℕ × ℕ),
    ((5, 1, 0) : ℕ × ℕ × ℕ), ((5, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := row_content (content_mem B381) (content_ge _)
    (by show Mono [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ),
          ((3, 1, 0) : ℕ × ℕ × ℕ)]
        unfold Mono; decide)
  exact h

/-- ★ シート行 382 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,1)(5,1,0)(6,2,0)`。 -/
theorem R382_mem : R341 ++ [((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 1) : ℕ × ℕ × ℕ),
    ((5, 1, 0) : ℕ × ℕ × ℕ), ((6, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := row_content (content_mem B382) (content_ge _)
    (by show Mono [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ),
          ((4, 2, 0) : ℕ × ℕ × ℕ)]
        unfold Mono; decide)
  exact h

/-- ★ シート行 383 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,1)(5,1,0)(6,2,1)`。 -/
theorem R383_mem : R341 ++ [((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 1) : ℕ × ℕ × ℕ),
    ((5, 1, 0) : ℕ × ℕ × ℕ), ((6, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := row_content (content_mem B383) (content_ge _)
    (by show Mono [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ),
          ((4, 2, 1) : ℕ × ℕ × ℕ)]
        unfold Mono; decide)
  exact h

/-- ★ シート行 384 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,2,1)(5,1,0)(6,2,1)(7,1,0)`。 -/
theorem R384_mem : R341 ++ [((3, 1, 0) : ℕ × ℕ × ℕ), ((4, 2, 1) : ℕ × ℕ × ℕ),
    ((5, 1, 0) : ℕ × ℕ × ℕ), ((6, 2, 1) : ℕ × ℕ × ℕ), ((7, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := row_content (content_mem B384) (content_ge _)
    (by show Mono [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 1, 0) : ℕ × ℕ × ℕ),
          ((4, 2, 1) : ℕ × ℕ × ℕ), ((5, 1, 0) : ℕ × ℕ × ℕ)]
        unfold Mono; decide)
  exact h

#print axioms R384_mem

/-! ## シート行 385 = 目標の `[2]` -/

/-- 中身の族 `Tc n = (1,1,0)(2,2,1)(3,1,0)(4,2,1)…`（`2n` 列）。 -/
def Tc : ℕ → TrioSeq
  | 0 => []
  | (n + 1) => ((1, 1, 0) : ℕ × ℕ × ℕ) :: rword 1 1 [Tc n]

theorem Tc_ge : ∀ n, ∀ x ∈ Tc n, 1 ≤ x.1
  | 0 => by intro x hx; simp [Tc] at hx
  | (n + 1) => content_ge [Tc n]

theorem Tc_Wg : ∀ n, Tc n ∈ Wg 2
  | 0 => Wg_nil 2
  | (n + 1) => content_mem (Bw_one (Tc_Wg n) (Tc_ge n))

theorem Tc_mono : ∀ n, Mono (Tc n)
  | 0 => by intro c hc; simp [Tc] at hc
  | (n + 1) => by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · show (0 : ℕ) ≤ 1; omega
      · rw [rword_singleton] at hc
        exact rcol_mono (Tc_mono n) c hc

theorem Tc_row : ∀ n, R338 ++ Tc n ∈ W 0
  | 0 => by simpa [Tc] using Aok_R338.mem
  | (n + 1) => row_content (Tc_Wg n) (Tc_ge n) (Tc_mono n)

def M2 : TrioSeq := [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)]

theorem shiftr01_flatMap (d : ℕ) (L : List ℕ) (g : ℕ → TrioSeq) :
    shiftr01 d 0 (L.flatMap g) = L.flatMap (fun k => shiftr01 d 0 (g k)) := by
  induction L with
  | nil => rfl
  | cons k L ih => rw [List.flatMap_cons, List.flatMap_cons, shiftr01_append0, ih]

theorem Tc_flat : ∀ n, (List.range n).flatMap (fun k => shiftr01 (2 * k) 0 M2) = Tc n
  | 0 => rfl
  | (n + 1) => by
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      have h : (List.range n).flatMap ((fun k => shiftr01 (2 * k) 0 M2) ∘ Nat.succ)
          = shiftr01 2 0 (Tc n) := by
        rw [← Tc_flat n, shiftr01_flatMap]
        apply List.flatMap_congr
        intro k _
        simp only [Function.comp_apply, shiftr01_add0]
        congr 1
      rw [show (List.range n).flatMap (fun a => shiftr01 (2 * a.succ) 0 M2)
          = shiftr01 2 0 (Tc n) from h]
      show shiftr01 (2 * 0) 0 M2 ++ shiftr01 2 0 (Tc n)
        = ((1, 1, 0) : ℕ × ℕ × ℕ) :: rword 1 1 [Tc n]
      rw [rword_singleton, rcol]
      simp [M2]

theorem Mtwd_Tc (n : ℕ) : Mtwd 2 R338 M2 n = R338 ++ Tc n := by
  unfold Mtwd
  rw [Tc_flat]

/-- ★★★ シート行 385 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,2,0) ∈ W 0`（目標の `[2]`、仮定なし）。 -/
theorem R385_mem : R341 ++ [((3, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := snocYd_mem0 (Y0 := R338) (M := M2) (L := 1) (y := 2) (dl := 2)
    (by simp [R338]) (by simp [M2]) (by simp [M2, entry])
    (by
      intro j hj1 hj2
      simp [M2] at hj2
      have : j = 1 := by omega
      subst this
      simp [M2, entry])
    (by simp [M2, entry])
    (by
      intro t ht1 ht2 _ _
      simp [M2] at ht2
      have : t = 1 := by omega
      subst this
      simp [M2, entry])
    (by omega) (by omega) (fun n => by rw [Mtwd_Tc]; exact Tc_row n)
  simpa [R341, M2, List.append_assoc] using h

#print axioms R385_mem

end GwV
end TRIO
