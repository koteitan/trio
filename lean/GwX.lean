/-
GwX.lean: シート行 395 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,2,0)(2,2,0)(3,3,1)(4,2,0)`。

行 395 の展開は `M5 = (1,1,0)(2,2,1)(3,2,0)(2,2,0)(3,3,1)` を歩幅 3 で並べた族
`R338 ++ U n`、`U (n+1) = (1,1,0)(2,2,1)(3,2,0)(2,2,0) ++ rword 2 2 [U n]`。
各項は `G2 ++ (2,2,0) :: rword 2 2 [U n]` なので `GoodFb` の pk 欄（`pk_G2`）で出る。
`U n ∈ Wg 2` は Wg の中で `hang_Wg`（語 `(1,2,1)(2,2,0)`、吊るす元 `(1,2,0) :: rword 1 2 [U n]`）。
語 `(0,1,0)(1,2,1)(2,2,0) ∈ Wg 2` は、根が生き返らせる塔 `oper_cons_tower1` と `Bw` で。
-/
import GwW

namespace TRIO
namespace GwX

open Wset
open Small
open GwS
open Gw
open GwU
open GwV
open GwW

/-! ## 相対の中身の字 `(0,1,0)(1,2,1)(2,2,0) ∈ Wg 2` -/

def R12 : TrioSeq := [((1, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ)]

theorem argOK_R12 : argOK R12 := by unfold argOK R12; decide

theorem srow_R12 : srow R12 (R12.length - 1) = 1 := by simp [srow, R12, entry]

theorem domT_R12 : domT R12 3 := by
  refine ⟨by simp [lev, R12, entry], ?_⟩
  rw [srow_R12]
  rintro ⟨k, hk, -⟩
  have hk' : nextrel1 R12 k (R12.length - 1) := by
    unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
  obtain ⟨-, -, hkl, hk1, -⟩ := hk'
  have hk0 : k = 0 := by simp [R12] at hkl; omega
  subst hk0
  simp [R12, entry] at hk1

theorem hasParent_G2c :
    hasParent (((0, 1, 0) : ℕ × ℕ × ℕ) :: R12) (srow R12 (R12.length - 1)) R12.length := by
  rw [srow_R12]
  show hasParent (((0, 1, 0) : ℕ × ℕ × ℕ) :: R12) 1 2
  have h01 : nextrel0 (((0, 1, 0) : ℕ × ℕ × ℕ) :: R12) 0 1 :=
    ⟨by simp [R12], by simp [R12], by omega, by simp [R12, entry], fun j hj => by omega⟩
  have h12 : nextrel0 (((0, 1, 0) : ℕ × ℕ × ℕ) :: R12) 1 2 :=
    ⟨by simp [R12], by simp [R12], by omega, by simp [R12, entry], fun j hj => by omega⟩
  have hle : le0 (((0, 1, 0) : ℕ × ℕ × ℕ) :: R12) 0 2 :=
    ⟨by simp [R12], by simp [R12],
      Relation.ReflTransGen.tail (Relation.ReflTransGen.single h01) h12⟩
  exact hasParent_one_of (by simp [R12]) (by omega) hle (by simp [R12, entry])

theorem natDom_G2c : natDom (((0, 1, 0) : ℕ × ℕ × ℕ) :: R12) := by
  refine natDom_iff.mpr (Or.inr ?_)
  have hl : ((((0, 1, 0) : ℕ × ℕ × ℕ) :: R12).length - 1) = R12.length := by simp [R12]
  have hs : srow (((0, 1, 0) : ℕ × ℕ × ℕ) :: R12)
      ((((0, 1, 0) : ℕ × ℕ × ℕ) :: R12).length - 1) = srow R12 (R12.length - 1) := by
    simp [srow, R12, entry]
  rw [hs, hl]
  exact hasParent_G2c

theorem tow_R12_succ (k : ℕ) :
    tow 1 0 R12 (k + 1)
      = ((0, 1, 0) : ℕ × ℕ × ℕ) :: rword 0 1 [shiftr01 1 0 (tow 1 0 R12 k)] := by
  rw [tow, graft_eq_shift, rword_singleton, rcol, shiftr01_add0]
  rfl

theorem tow_R12_Wg : ∀ k, tow 1 0 R12 k ∈ Wg 2
  | 0 => by simpa [tow] using Wg_nil 2
  | (k + 1) => by
      rw [tow_R12_succ]
      have hT : shiftr01 1 0 (tow 1 0 R12 k) ∈ Wg 2 := Wg_shift (tow_R12_Wg k) 1
      have hge : ∀ x ∈ shiftr01 1 0 (tow 1 0 R12 k), 1 ≤ x.1 := by
        intro x hx
        simp only [shiftr01, List.mem_map] at hx
        obtain ⟨p, -, rfl⟩ := hx
        dsimp only; omega
      exact Bw_one hT hge 1 le_rfl (argOK_rword 1 _) 2 le_rfl

theorem G2c_Wg : (((0, 1, 0) : ℕ × ℕ × ℕ) :: R12) ∈ Wg 2 := by
  refine A1g_intro (Or.inr (Or.inl ⟨natDom_G2c, fun n _ => ?_⟩))
  rw [oper_cons_tower1 argOK_R12 (by simp [R12]) domT_R12 srow_R12 hasParent_G2c]
  exact tow_R12_Wg n

/-! ## 中身の族 `U` -/

def U : ℕ → TrioSeq
  | 0 => []
  | (n + 1) => [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ),
      ((2, 2, 0) : ℕ × ℕ × ℕ)] ++ rword 2 2 [U n]

theorem U_ge : ∀ n, ∀ x ∈ U n, 1 ≤ x.1
  | 0 => by intro x hx; simp [U] at hx
  | (n + 1) => by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> (dsimp only; omega)
      · have := rword_ge 2 2 [U n] x hx; omega

theorem U_mono : ∀ n, Mono (U n)
  | 0 => by intro c hc; simp [U] at hc
  | (n + 1) => by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> (dsimp only; omega)
      · rw [rword_singleton] at hc
        exact rcol_mono (U_mono n) c hc

theorem U_eq (n : ℕ) : U (n + 1) = shiftr01 1 0 (((0, 1, 0) : ℕ × ℕ × ℕ) ::
    (R12 ++ (((1, 2, 0) : ℕ × ℕ × ℕ) :: rword 1 2 [U n]))) := by
  show _ = shiftr01 1 0 ([((0, 1, 0) : ℕ × ℕ × ℕ), ((1, 2, 1) : ℕ × ℕ × ℕ),
    ((2, 2, 0) : ℕ × ℕ × ℕ), ((1, 2, 0) : ℕ × ℕ × ℕ)] ++ rword 1 2 [U n])
  rw [shiftr01_append0, rword_shift]
  rfl

theorem U_Wg : ∀ n, U n ∈ Wg 2
  | 0 => Wg_nil 2
  | (n + 1) => by
      rw [U_eq]
      refine Wg_shift ?_ 1
      have hA : R12 ∈ Wstarv 1 := fun _ a ha => Wg_mono ha G2c_Wg
      have hR0 : (((0, 2, 0) : ℕ × ℕ × ℕ) :: rword 0 2 [U n]) ∈ Wg 4 :=
        Bw_one (U_Wg n) (U_ge n) 2 (by omega) (argOK_rword 2 _) 4 le_rfl
      have hR : (((1, 2, 0) : ℕ × ℕ × ℕ) :: rword 1 2 [U n]) ∈ Wg 4 := by
        have h := Wg_shift hR0 1
        rw [show (((0, 2, 0) : ℕ × ℕ × ℕ) :: rword 0 2 [U n])
            = [((0, 2, 0) : ℕ × ℕ × ℕ)] ++ rword 0 2 [U n] from rfl,
          shiftr01_append0, shift_col, rword_shift] at h
        simpa using h
      have hge : ∀ p ∈ R12 ++ (((1, 2, 0) : ℕ × ℕ × ℕ) :: rword 1 2 [U n]), 1 ≤ p.1 := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · simp only [R12, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl <;> (dsimp only; omega)
        · rcases List.mem_cons.mp hp with rfl | hp
          · dsimp only; omega
          · have := rword_ge 1 2 [U n] p hp; omega
      have hrs : rsum R12 (((1, 2, 0) : ℕ × ℕ × ℕ) :: rword 1 2 [U n]) := by
        intro p hp
        have he : entry (((1, 2, 0) : ℕ × ℕ × ℕ) :: rword 1 2 [U n]) 0 0 = 1 := rfl
        rw [he]
        exact hge p hp
      exact hang_Wg hA hR hrs (fun p hp => by have := hge p hp; omega) 2 le_rfl

theorem GoodFb_U (n : ℕ) : GoodFb (fun a b => rword a b [U n]) := by
  have h := GOKR_of_Wg2 (U n) (U_Wg n) (U_ge n) (U_mono n) [] (by intro V hV; simp at hV)
    GoodFb_rword_nil
  simpa using h

theorem U_row : ∀ n, R338 ++ U n ∈ W 0
  | 0 => by simpa [U] using Aok_R338.mem
  | (n + 1) => by
      rw [show R338 ++ U (n + 1) = G2 ++ ([((2, 2, 0) : ℕ × ℕ × ℕ)] ++ rword 2 2 [U n]) from by
        simp [G2, GwW.M3, U]]
      exact pk_G2 (GoodFb_U n)

/-! ## 極限 -/

def M5 : TrioSeq := [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ),
  ((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ)]

theorem U_flat : ∀ n, (List.range n).flatMap (fun k => shiftr01 (3 * k) 0 M5) = U n
  | 0 => rfl
  | (n + 1) => by
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      have h : (List.range n).flatMap ((fun k => shiftr01 (3 * k) 0 M5) ∘ Nat.succ)
          = shiftr01 3 0 (U n) := by
        rw [← U_flat n, shiftr01_flatMap]
        apply List.flatMap_congr
        intro k _
        simp only [Function.comp_apply, shiftr01_add0]
        congr 1
      rw [show (List.range n).flatMap (fun a => shiftr01 (3 * a.succ) 0 M5)
          = shiftr01 3 0 (U n) from h]
      show shiftr01 (3 * 0) 0 M5 ++ shiftr01 3 0 (U n)
        = [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((3, 2, 0) : ℕ × ℕ × ℕ),
          ((2, 2, 0) : ℕ × ℕ × ℕ)] ++ rword 2 2 [U n]
      rw [rword_singleton, rcol]
      simp [M5]

theorem Mtwd_U (n : ℕ) : Mtwd 3 R338 M5 n = R338 ++ U n := by
  unfold Mtwd
  rw [U_flat]

/-- ★ シート行 395 `(0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,2,0)(2,2,0)(3,3,1)(4,2,0)`（仮定なし）。 -/
theorem R395_mem : G2 ++ [((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((4, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := snocYd_mem0 (Y0 := R338) (M := M5) (L := 1) (y := 2) (dl := 3)
    (by simp [R338]) (by simp [M5]) (by simp [M5, entry])
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
    (by omega) (by omega) (fun n => by rw [Mtwd_U]; exact U_row n)
  simpa [G2, GwW.M3, M5, List.append_assoc] using h

#print axioms R395_mem

end GwX
end TRIO
