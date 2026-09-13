/-
GxD.lean: シート行 433〜439, 441, 442, 444〜450。

形はどれも `Gm ++ T`（`T ∈ Wg 2` を BH（`GwY.base_hang`、台座 `Aok_Gm`）で吊るす）。
`T` は段 1 の根 `(0,1,0)` の上の語を 1 段上げたもので、`hang_Wg` で段 1・段 2 の部品をつなぐ。

    433〜439: T = (0,1,0) :: (R12v 1 ++ (0,2,0) :: B)↑1       （B は段 2 の語・塔）
    441     : T = L4 ++ L4                                    （Wg_add）
    442     : T = L4 ++ (2,0,0)                               （最上位の複製）
    444〜450: T = (0,1,0) :: (X1 ++ R)↑1, X1 = (1,2,1)(2,2,0)(1,2,1)  （段 1 の Gm）
-/
import GxC

namespace TRIO
namespace GxD

open Wset
open Small
open GwS
open Gw
open GwU
open GwZ
open GxA

/-! ## 部品 -/

theorem hangv {v : ℕ} {A R : TrioSeq} (hA : A ∈ Wstarv v) (hAge : ∀ x ∈ A, 1 ≤ x.1)
    {u : ℕ} (hR : R ∈ Wg u) (hRge : ∀ x ∈ R, 1 ≤ x.1) (hhd : entry R 0 0 ≤ 1) :
    ∀ a, 2 * v ≤ a → (((0, v, 0) : ℕ × ℕ × ℕ) :: (A ++ R)) ∈ Wg a := by
  have hrs : rsum A R := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have := hAge p hp; omega
    · have := hRge p hp; omega
  refine hang_Wg hA hR hrs ?_
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hAge p hp
  · exact hRge p hp

theorem shift1_ge (Z : TrioSeq) : ∀ x ∈ shiftr01 1 0 Z, 1 ≤ x.1 := by
  intro x hx
  simp only [shiftr01, List.mem_map] at hx
  obtain ⟨p, -, rfl⟩ := hx
  dsimp only; omega

theorem Mono_shift {Z : TrioSeq} (h : Mono Z) (d : ℕ) : Mono (shiftr01 d 0 Z) := by
  intro x hx
  simp only [shiftr01, List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  have := h p hp
  dsimp only; omega

/-- BH の形: 根の高さ 0 の `Z ∈ Wg 2` を 1 段上げて `Gm` に吊るす。 -/
theorem BHs {Z : TrioSeq} (hZ : Z ∈ Wg 2) (hmo : Mono Z) (h0 : entry Z 0 0 = 0) :
    Gm ++ shiftr01 1 0 Z ∈ W 0 := by
  refine GwY.base_hang _ (Wg_shift hZ 1) (shift1_ge Z) (Mono_shift hmo 1) ?_ Gm Aok_Gm
  by_cases hZn : Z = []
  · subst hZn; simp [shiftr01, entry]
  · obtain ⟨p, Z', rfl⟩ := List.exists_cons_of_ne_nil hZn
    simp [shiftr01, entry] at h0 ⊢
    omega

/-! ## 段 v の Gm -/

def L4v (v : ℕ) : TrioSeq := [((0, v, 0) : ℕ × ℕ × ℕ), ((1, v + 1, 1) : ℕ × ℕ × ℕ),
  ((2, v + 1, 0) : ℕ × ℕ × ℕ), ((1, v + 1, 1) : ℕ × ℕ × ℕ)]

theorem L4v_n01 (v : ℕ) : nextrel0 (L4v v) 0 1 :=
  ⟨by simp [L4v], by simp [L4v], by omega, by simp [L4v, entry], fun j hj => by omega⟩

theorem L4v_n12 (v : ℕ) : nextrel0 (L4v v) 1 2 :=
  ⟨by simp [L4v], by simp [L4v], by omega, by simp [L4v, entry], fun j hj => by omega⟩

theorem L4v_le1_1 (v : ℕ) : le1 (L4v v) 0 1 := by
  refine ⟨by simp [L4v], by simp [L4v], Relation.ReflTransGen.single
    ⟨by simp [L4v], by simp [L4v], by omega, by simp [L4v, entry],
      ⟨by simp [L4v], by simp [L4v], Relation.ReflTransGen.single (L4v_n01 v)⟩, fun j hj => ?_⟩⟩
  have h1 := rtg0_le hj.2.2.2
  have : j = 1 := by omega
  subst this
  exact le_rfl

theorem L4v_le1_2 (v : ℕ) : le1 (L4v v) 0 2 := by
  refine ⟨by simp [L4v], by simp [L4v], Relation.ReflTransGen.single
    ⟨by simp [L4v], by simp [L4v], by omega, by simp [L4v, entry],
      ⟨by simp [L4v], by simp [L4v],
        Relation.ReflTransGen.tail (Relation.ReflTransGen.single (L4v_n01 v)) (L4v_n12 v)⟩,
      fun j hj => ?_⟩⟩
  have h1 := rtg0_le hj.2.2.2
  rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl <;> simp [L4v, entry]

open Classical in
theorem oper_L4v (v n : ℕ) : (L4v v)⟦n⟧ = (List.range n).flatMap (fun k => GwZ.Blk v k) := by
  have h := oper_z1_mask [] 0 v [((1, v + 1, 1) : ℕ × ℕ × ℕ), ((2, v + 1, 0) : ℕ × ℕ × ℕ)]
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> (dsimp only; omega)) n
  have eG : L4v v = [] ++ (((0, v, 0) : ℕ × ℕ × ℕ) :: [((1, v + 1, 1) : ℕ × ℕ × ℕ),
      ((2, v + 1, 0) : ℕ × ℕ × ℕ)] ++ [((0 + 1, v + 1, 1) : ℕ × ℕ × ℕ)]) := rfl
  rw [eG, h, List.nil_append]
  apply List.flatMap_congr
  intro k _
  have hle1 := L4v_le1_1 v
  have hle2 := L4v_le1_2 v
  simp only [L4v] at hle1 hle2
  simp [List.range_succ, hle1, hle2, entry, GwZ.Blk, Nat.add_comm] <;> omega

theorem L4v_Wg (v : ℕ) (hv : 1 ≤ v) : ∀ a, 2 * v ≤ a → L4v v ∈ Wg a := by
  intro a ha
  have hnat : natDom (L4v v) :=
    natDom_zroot v (X := [((1, v + 1, 1) : ℕ × ℕ × ℕ), ((2, v + 1, 0) : ℕ × ℕ × ℕ)]) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> (dsimp only; omega))
  refine A1g_intro (Or.inr (Or.inl ⟨hnat, fun n _ => ?_⟩))
  rw [oper_L4v, ← S_flat]
  exact Wg_mono ha (S_Wg n v hv)

def X1 : TrioSeq := [((1, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ), ((1, 2, 1) : ℕ × ℕ × ℕ)]

theorem X1_star : X1 ∈ Wstarv 1 := fun _ a ha => L4v_Wg 1 le_rfl a ha

theorem X1_ge : ∀ x ∈ X1, 1 ≤ x.1 := by
  intro x hx
  simp only [X1, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> (dsimp only; omega)

theorem R12_star : R12v 1 ∈ Wstarv 1 := fun _ a ha => Wg_mono ha (G2cv_Wg 1 le_rfl)

theorem R12_ge : ∀ x ∈ R12v 1, 1 ≤ x.1 := by
  intro x hx
  simp only [R12v, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> (dsimp only; omega)

theorem L4_Wg : GxC.L4 ∈ Wg 2 := by
  have h := Wg_shift (L4v_Wg 1 le_rfl 2 le_rfl) 1
  simpa [L4v, shiftr01, GxC.L4] using h

/-! ## 根が生き返らせる行 1 の孤児の塔 -/

theorem tower_snoc (v : ℕ) {A : TrioSeq} (hA : A ∈ Wstarv v) (hAge : ∀ x ∈ A, 1 ≤ x.1) :
    ∀ a, 2 * v ≤ a →
      (((0, v, 0) : ℕ × ℕ × ℕ) :: (A ++ [((1, v + 1, 0) : ℕ × ℕ × ℕ)])) ∈ Wg a := by
  set c : ℕ × ℕ × ℕ := (1, v + 1, 0) with hc
  set R : TrioSeq := A ++ [c] with hRdef
  have hRne : R ≠ [] := by simp [hRdef]
  have hRlen : R.length = A.length + 1 := by simp [hRdef]
  have hR : argOK R := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hAge p hp
    · simp only [List.mem_singleton] at hp
      subst hp; simp [hc]
  have hlast : ∀ i, entry R i (R.length - 1) = entry [c] i 0 := by
    intro i
    rw [show R.length - 1 = A.length + 0 by omega, hRdef, entry_append_right]
  have e0 : entry R 0 (R.length - 1) = 1 := by rw [hlast 0]; simp [entry, hc]
  have e1 : entry R 1 (R.length - 1) = v + 1 := by rw [hlast 1]; simp [entry, hc]
  have e2 : entry R 2 (R.length - 1) = 0 := by rw [hlast 2]; simp [entry, hc]
  have hAent : ∀ j, j < A.length → 1 ≤ entry R 0 j := by
    intro j hj
    rw [hRdef, Small.entry_append_left hj]
    have hmem : A.getD j (0, 0, 0) ∈ A := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      exact List.getElem_mem _
    exact hAge _ hmem
  have hsr : srow R (R.length - 1) = 1 := by
    unfold srow
    rw [e2, e1]
    simp
  have hd : domT R (2 * v + 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2]; omega
    · rw [hsr]
      rintro ⟨k, hk, -⟩
      have hk' : nextrel1 R k (R.length - 1) := by
        unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
      obtain ⟨-, -, hkl, -, ⟨-, -, hrt⟩, -⟩ := hk'
      rcases Relation.ReflTransGen.cases_tail hrt with heq | ⟨b, -, hb⟩
      · omega
      · obtain ⟨-, -, hbl, hb0, -⟩ := hb
        have h1 := hAent b (by omega)
        rw [e0] at hb0
        omega
  have hpM : hasParent (((0, v, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length := by
    rw [hsr]
    refine hasParent_one_of (b := R.length) (k := 0) (by simp) (by omega) ?_ ?_
    · refine ⟨by simp, by simp, Relation.ReflTransGen.single
        ⟨by simp, by simp, by omega, ?_, ?_⟩⟩
      · rw [entry_cons_last hRne 0, e0]; simp [entry]
      · intro j hj
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [entry_cons_last hRne 0, e0, entry_cons]
        exact hAent j' (by omega)
    · rw [entry_cons_last hRne 1, e1]; simp [entry]
  have hnat : natDom (((0, v, 0) : ℕ × ℕ × ℕ) :: R) := by
    refine natDom_iff.mpr (Or.inr ?_)
    have hl : ((((0, v, 0) : ℕ × ℕ × ℕ) :: R).length - 1) = R.length := by simp
    rw [hl, srow_cons_last hRne]
    exact hpM
  have hdl : R.dropLast = A := by simp [hRdef]
  have htow : ∀ k, tow v 0 R k ∈ Wg (2 * v) := by
    intro k
    induction k with
    | zero => simpa [tow] using Wg_nil (2 * v)
    | succ k ih =>
        have e : tow v 0 R (k + 1)
            = ((0, v, 0) : ℕ × ℕ × ℕ) :: (A ++ shiftr01 1 0 (tow v 0 R k)) := by
          rw [tow, graft_eq_shift, e0, hdl]
        rw [e]
        refine hangv hA hAge (Wg_shift ih 1) (shift1_ge _) ?_ (2 * v) le_rfl
        cases k with
        | zero => simp [tow, shiftr01, entry]
        | succ k' => simp [tow, shiftr01, entry]
  intro a ha
  refine A1g_intro (Or.inr (Or.inl ⟨hnat, fun n _ => ?_⟩))
  rw [oper_cons_tower1 hR hRne hd hsr hpM]
  exact Wg_mono ha (htow n)

/-! ## 段 2 の部品 -/

theorem Wg4_120 : [((1, 2, 0) : ℕ × ℕ × ℕ)] ∈ Wg 4 := by
  have h := Wg_shift (Om_mem_Wg 2) 1
  simpa [shiftr01] using h

theorem raw120 : RawWv 2 [((1, 2, 0) : ℕ × ℕ × ℕ)] :=
  ⟨by decide, Wg_RiseOkv (v0 := 2) Wg4_120⟩

theorem Bw_z : Bwv 2 [[]] := by
  have h := Bw_snoczv (v0 := 2) (by omega) (l := []) (by intro U hU; simp at hU) (Bwv_nil 2)
  simpa using h

theorem Bw_120 : Bwv 2 [[((1, 2, 0) : ℕ × ℕ × ℕ)]] := by
  have h := GOKWv_of_Wg (v0 := 2) (by omega) [((1, 2, 0) : ℕ × ℕ × ℕ)] Wg4_120 (by decide) []
    (by intro U hU; simp at hU) (Bwv_nil 2)
  simpa using h

theorem Bw_120_z : Bwv 2 [[((1, 2, 0) : ℕ × ℕ × ℕ)], []] := by
  have h := Bw_snoczv (v0 := 2) (by omega) (WOkWv_singleton raw120) Bw_120
  simpa using h

theorem Bw_120_120 : Bwv 2 [[((1, 2, 0) : ℕ × ℕ × ℕ)], [((1, 2, 0) : ℕ × ℕ × ℕ)]] := by
  have h := GOKWv_of_Wg (v0 := 2) (by omega) [((1, 2, 0) : ℕ × ℕ × ℕ)] Wg4_120 (by decide)
    [[((1, 2, 0) : ℕ × ℕ × ℕ)]] (WOkWv_singleton raw120) Bw_120
  simpa using h

theorem Wg4_1212 : [((1, 2, 0) : ℕ × ℕ × ℕ), ((1, 2, 0) : ℕ × ℕ × ℕ)] ∈ Wg 4 := by
  have h := Wg_add Wg4_120 Wg4_120 (by
    intro p hp
    simp only [List.mem_append, List.mem_singleton, or_self] at hp
    subst hp; simp [entry])
  simpa using h

theorem Bw_1212 : Bwv 2 [[((1, 2, 0) : ℕ × ℕ × ℕ), ((1, 2, 0) : ℕ × ℕ × ℕ)]] := by
  have h := GOKWv_of_Wg (v0 := 2) (by omega) _ Wg4_1212 (by decide) []
    (by intro U hU; simp at hU) (Bwv_nil 2)
  simpa using h

theorem B_z : (((0, 2, 0) : ℕ × ℕ × ℕ) :: [((1, 3, 1) : ℕ × ℕ × ℕ)]) ∈ Wg 4 := by
  have h := Bw_z 2 le_rfl (argOK_rword 2 _) 4 (by omega)
  simpa [rword, rcol, shiftr01] using h

theorem Wg4_1231 : [((1, 2, 0) : ℕ × ℕ × ℕ), ((2, 3, 1) : ℕ × ℕ × ℕ)] ∈ Wg 4 := by
  have h := Wg_shift B_z 1
  simpa [shiftr01] using h

theorem Bw_1231 : Bwv 2 [[((1, 2, 0) : ℕ × ℕ × ℕ), ((2, 3, 1) : ℕ × ℕ × ℕ)]] := by
  have h := GOKWv_of_Wg (v0 := 2) (by omega) _ Wg4_1231 (by decide) []
    (by intro U hU; simp at hU) (Bwv_nil 2)
  simpa using h

theorem A_120_star : [((1, 3, 1) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ Wstarv 2 := by
  have h := Bw_120 2 le_rfl
  simpa [rword, rcol, shiftr01] using h

/-! ## 行の組み立て -/

theorem rowAR {A R : TrioSeq} (hA : A ∈ Wstarv 1) (hAge : ∀ x ∈ A, 1 ≤ x.1) (hAmo : Mono A)
    {u : ℕ} (hR : R ∈ Wg u) (hRge : ∀ x ∈ R, 1 ≤ x.1) (hhd : entry R 0 0 ≤ 1)
    (hRmo : Mono R) :
    Gm ++ shiftr01 1 0 (((0, 1, 0) : ℕ × ℕ × ℕ) :: (A ++ R)) ∈ W 0 := by
  refine BHs (hangv hA hAge hR hRge hhd 2 le_rfl) ?_ (by simp [entry])
  intro x hx
  simp only [List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | hx | hx
  · show (0 : ℕ) ≤ 1; omega
  · exact hAmo x hx
  · exact hRmo x hx

/-- 段 2 の根の列 `(0,2,0) :: B` を 1 段上げた `R`。 -/
theorem rowAB {A B : TrioSeq} (hA : A ∈ Wstarv 1) (hAge : ∀ x ∈ A, 1 ≤ x.1) (hAmo : Mono A)
    (hB : (((0, 2, 0) : ℕ × ℕ × ℕ) :: B) ∈ Wg 4) (hBmo : Mono B) :
    Gm ++ shiftr01 1 0 (((0, 1, 0) : ℕ × ℕ × ℕ) ::
      (A ++ shiftr01 1 0 (((0, 2, 0) : ℕ × ℕ × ℕ) :: B))) ∈ W 0 := by
  refine rowAR hA hAge hAmo (Wg_shift hB 1) (shift1_ge _) (by simp [shiftr01, entry]) ?_
  refine Mono_shift ?_ 1
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · show (0 : ℕ) ≤ 2; omega
  · exact hBmo x hx

theorem R12_mono : Mono (R12v 1) := by unfold Mono R12v; decide

/-- ★ シート行 433 `… (1,1,0)(2,2,1)(3,2,0)(2,2,0)(3,3,1)(4,2,0)(3,3,0)`。 -/
theorem R433_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((4, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hB := tower_snoc 2 A_120_star (by decide) 4 le_rfl
  have h := rowAB R12_star R12_ge R12_mono hB (by unfold Mono; decide)
  simpa [shiftr01, R12v] using h

/-- ★ シート行 434 `… (2,2,0)(3,3,1)(4,2,0)(3,3,1)`。 -/
theorem R434_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((4, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hB := Bw_120_z 2 le_rfl (argOK_rword 2 _) 4 le_rfl
  have h := rowAB R12_star R12_ge R12_mono hB (by simp [Mono, rword, rcol, shiftr01])
  simpa [shiftr01, R12v, rword, rcol] using h

/-- ★ シート行 435 `… (2,2,0)(3,3,1)(4,2,0)(3,3,1)(4,2,0)`。 -/
theorem R435_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((4, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ), ((4, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hB := Bw_120_120 2 le_rfl (argOK_rword 2 _) 4 le_rfl
  have h := rowAB R12_star R12_ge R12_mono hB (by simp [Mono, rword, rcol, shiftr01])
  simpa [shiftr01, R12v, rword, rcol] using h

/-- ★ シート行 436 `… (2,2,0)(3,3,1)(4,2,0)(4,2,0)`。 -/
theorem R436_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((4, 2, 0) : ℕ × ℕ × ℕ), ((4, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hB := Bw_1212 2 le_rfl (argOK_rword 2 _) 4 le_rfl
  have h := rowAB R12_star R12_ge R12_mono hB (by simp [Mono, rword, rcol, shiftr01])
  simpa [shiftr01, R12v, rword, rcol] using h

/-- ★ シート行 437 `… (2,2,0)(3,3,1)(4,2,0)(5,3,1)`。 -/
theorem R437_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((4, 2, 0) : ℕ × ℕ × ℕ), ((5, 3, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hB := Bw_1231 2 le_rfl (argOK_rword 2 _) 4 le_rfl
  have h := rowAB R12_star R12_ge R12_mono hB (by simp [Mono, rword, rcol, shiftr01])
  simpa [shiftr01, R12v, rword, rcol] using h

/-- ★ シート行 438 `… (2,2,0)(3,3,1)(4,3,0)`。 -/
theorem R438_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((4, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := rowAB R12_star R12_ge R12_mono (G2cv_Wg 2 (by omega)) (by unfold Mono R12v; decide)
  simpa [shiftr01, R12v] using h

theorem S22_Wg : (((0, 2, 0) : ℕ × ℕ × ℕ) :: [((1, 3, 1) : ℕ × ℕ × ℕ), ((2, 3, 0) : ℕ × ℕ × ℕ),
    ((1, 3, 0) : ℕ × ℕ × ℕ), ((2, 4, 1) : ℕ × ℕ × ℕ), ((3, 4, 0) : ℕ × ℕ × ℕ)]) ∈ Wg 4 := by
  have h := S_Wg 2 2 (by omega)
  simpa [S, R12v, shiftr01] using h

/-- ★ シート行 439 `… (2,2,0)(3,3,1)(4,3,0)(3,3,0)(4,4,1)(5,4,0)`。 -/
theorem R439_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((4, 3, 0) : ℕ × ℕ × ℕ), ((3, 3, 0) : ℕ × ℕ × ℕ), ((4, 4, 1) : ℕ × ℕ × ℕ),
    ((5, 4, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := rowAB R12_star R12_ge R12_mono S22_Wg (by unfold Mono; decide)
  simpa [shiftr01, R12v] using h

/-! ## 台座 `Gm ++ L4` の行 -/

theorem L4_ge : ∀ x ∈ GxC.L4, 1 ≤ x.1 := by
  intro x hx
  simp only [GxC.L4, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> (dsimp only; omega)

theorem L4_mono : Mono GxC.L4 := by unfold Mono GxC.L4; decide

/-- ★ シート行 441 `… (1,1,0)(2,2,1)(3,2,0)(2,2,1)(1,1,0)(2,2,1)(3,2,0)(2,2,1)`。 -/
theorem R441_mem : Gm ++ (GxC.L4 ++ GxC.L4) ∈ W 0 := by
  have hT : GxC.L4 ++ GxC.L4 ∈ Wg 2 := Wg_add L4_Wg L4_Wg (by
    intro p hp
    have : 1 ≤ p.1 := by
      rcases List.mem_append.mp hp with hp | hp <;> exact L4_ge p hp
    simp [entry, GxC.L4]; omega)
  refine GwY.base_hang _ hT ?_ ?_ (by simp [entry, GxC.L4]) Gm Aok_Gm
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx <;> exact L4_ge x hx
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx <;> exact L4_mono x hx

/-- ★ シート行 442 `… (1,1,0)(2,2,1)(3,2,0)(2,2,1)(2,0,0)`。 -/
theorem R442_mem : Gm ++ (GxC.L4 ++ [((2, 0, 0) : ℕ × ℕ × ℕ)]) ∈ W 0 := by
  have hT : GxC.L4 ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] ∈ Wg 2 := by
    refine A1g_intro (Or.inr (Or.inl ⟨natDom_iff.mpr (Or.inl (by
      simp [lev, entry, GxC.L4])), fun n _ => ?_⟩))
    have h := oper_snoc00'' [] (M := GxC.L4) (d := 2) (by simp [GxC.L4])
      (by simp [GxC.L4, entry]) (by
        intro r hr1 hr2
        simp [GxC.L4] at hr2
        rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl <;>
          simp [GxC.L4, entry]) n
    simp only [List.nil_append] at h
    rw [h]
    exact Wg_flatMap_copies L4_Wg (by
      intro p hp
      have := L4_ge p hp
      simp [entry, GxC.L4]; omega) n
  refine GwY.base_hang _ hT ?_ ?_ (by simp [entry, GxC.L4]) Gm Aok_Gm
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact L4_ge x hx
    · simp only [List.mem_singleton] at hx; subst hx; simp
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact L4_mono x hx
    · simp only [List.mem_singleton] at hx; subst hx; simp

theorem X1_mono : Mono X1 := by unfold Mono X1; decide

/-- ★ シート行 444 `… (2,2,1)(2,1,0)(3,2,1)(4,2,0)(3,2,1)`。 -/
theorem R444_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ),
    ((3, 2, 1) : ℕ × ℕ × ℕ), ((4, 2, 0) : ℕ × ℕ × ℕ), ((3, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := rowAR X1_star X1_ge X1_mono L4_Wg L4_ge (by simp [entry, GxC.L4]) L4_mono
  simpa [shiftr01, X1, GxC.L4] using h

/-- ★ シート行 445 `… (2,2,1)(2,2,0)`。 -/
theorem R445_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hZ := tower_snoc 1 X1_star X1_ge 2 le_rfl
  have h := BHs hZ (by unfold Mono X1; decide) (by simp [entry])
  simpa [shiftr01, X1] using h

/-- 段 2 の根の列を 1 段上げて `X1` の後ろに置く。 -/
theorem rowX1 {B : TrioSeq} (hB : (((0, 2, 0) : ℕ × ℕ × ℕ) :: B) ∈ Wg 4) (hBmo : Mono B) :
    Gm ++ shiftr01 1 0 (((0, 1, 0) : ℕ × ℕ × ℕ) ::
      (X1 ++ shiftr01 1 0 (((0, 2, 0) : ℕ × ℕ × ℕ) :: B))) ∈ W 0 :=
  rowAB X1_star X1_ge X1_mono hB hBmo

/-- ★ シート行 446 `… (2,2,1)(2,2,0)(3,3,1)`。 -/
theorem R446_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ),
    ((3, 3, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := rowX1 B_z (by unfold Mono; decide)
  simpa [shiftr01, X1] using h

/-- ★ シート行 447 `… (2,2,1)(2,2,0)(3,3,1)(4,2,0)`。 -/
theorem R447_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ),
    ((3, 3, 1) : ℕ × ℕ × ℕ), ((4, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hB := Bw_120 2 le_rfl (argOK_rword 2 _) 4 le_rfl
  have h := rowX1 hB (by simp [Mono, rword, rcol, shiftr01])
  simpa [shiftr01, X1, rword, rcol] using h

/-- ★ シート行 448 `… (2,2,1)(2,2,0)(3,3,1)(4,3,0)`。 -/
theorem R448_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ),
    ((3, 3, 1) : ℕ × ℕ × ℕ), ((4, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := rowX1 (G2cv_Wg 2 (by omega)) (by unfold Mono R12v; decide)
  simpa [shiftr01, X1, R12v] using h

/-- ★ シート行 449 `… (2,2,1)(2,2,0)(3,3,1)(4,3,0)(3,3,0)(4,4,1)(5,4,0)`。 -/
theorem R449_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ),
    ((3, 3, 1) : ℕ × ℕ × ℕ), ((4, 3, 0) : ℕ × ℕ × ℕ), ((3, 3, 0) : ℕ × ℕ × ℕ),
    ((4, 4, 1) : ℕ × ℕ × ℕ), ((5, 4, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := rowX1 S22_Wg (by unfold Mono; decide)
  simpa [shiftr01, X1] using h

/-- ★ シート行 450 `… (2,2,1)(2,2,0)(3,3,1)(4,3,0)(3,3,1)`。 -/
theorem R450_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ),
    ((3, 3, 1) : ℕ × ℕ × ℕ), ((4, 3, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hB : L4v 2 ∈ Wg 4 := L4v_Wg 2 (by omega) 4 le_rfl
  have h := rowX1 (B := [((1, 3, 1) : ℕ × ℕ × ℕ), ((2, 3, 0) : ℕ × ℕ × ℕ),
    ((1, 3, 1) : ℕ × ℕ × ℕ)]) hB (by unfold Mono; decide)
  simpa [shiftr01, X1] using h

#print axioms R433_mem
#print axioms R450_mem

end GxD
end TRIO
