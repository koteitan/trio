/-
GxF.lean: シート行 456〜463。空の z の字が続く族 `(0,v,0) :: Aj v j`。

    Aj v j = (1,v+1,1)(2,v+1,0) (1,v+1,1)^j

末尾の空の字 `(1,v+1,1)` の潰れでは、中身の列は全部根の錐（行 1 ≥ v+1）なので、複製は一様に持ち上がる:

    ((0,v,0) :: X ++ (1,v+1,1))⟦n⟧ = Pz v X n = Σ_k ((0,v+k,0) :: X↑(行 1 + k))↑(行 0 + k)
    Pz v X (n+1) = (0,v,0) :: (X ++ (Pz (v+1) X↑(行 1 + 1) n)↑1)

`hang_Wg` で `Aj v j ∈ Wstarv v`（j の帰納）。段 0 は BH で `W 0`。
-/
import GxE
import Lcone

namespace TRIO
namespace GxF

open Wset
open Small
open GwS
open Gw
open GwU
open GwV
open GwZ
open GxA
open GxD

theorem getD_mem_P {X : TrioSeq} {j : ℕ} (hj : j < X.length) {P : ℕ × ℕ × ℕ → Prop}
    (hP : ∀ x ∈ X, P x) : P (X.getD j (0, 0, 0)) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact hP _ (List.getElem_mem _)

/-! ## 錐が全部の z の潰れ -/

def Pz (v : ℕ) (X : TrioSeq) (n : ℕ) : TrioSeq :=
  (List.range n).flatMap (fun k => shiftr01 k 0 (((0, v + k, 0) : ℕ × ℕ × ℕ) :: shiftr01 0 k X))

open Classical in
theorem oper_zall (v : ℕ) (X : TrioSeq) (hX0 : ∀ x ∈ X, 1 ≤ x.1)
    (hX1 : ∀ x ∈ X, v + 1 ≤ x.2.1) (n : ℕ) :
    ((((0, v, 0) : ℕ × ℕ × ℕ) :: X) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)])⟦n⟧ = Pz v X n := by
  have h := oper_z1_mask [] 0 v X (by intro x hx; have := hX0 x hx; omega) n
  have eM : (((0, v, 0) : ℕ × ℕ × ℕ) :: X) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]
      = [] ++ (((0, v, 0) : ℕ × ℕ × ℕ) :: X ++ [((0 + 1, v + 1, 1) : ℕ × ℕ × ℕ)]) := rfl
  rw [eM, h, List.nil_append]
  unfold Pz
  apply List.flatMap_congr
  intro k _
  set M : TrioSeq := [] ++ (((0, v, 0) : ℕ × ℕ × ℕ) :: X ++ [((0 + 1, v + 1, 1) : ℕ × ℕ × ℕ)])
    with hM
  have hMlen : M.length = X.length + 2 := by simp [hM]
  have hent : ∀ r j, j < X.length → entry M r (j + 1) = entry X r j := by
    intro r j hj
    rw [hM, List.nil_append, List.cons_append, entry_cons, Small.entry_append_left hj]
  have h00 : entry M 0 0 = 0 := by simp [hM, entry]
  have h10 : entry M 1 0 = v := by simp [hM, entry]
  have hr : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l := by
    intro l hl0 hl
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    rw [h00]
    rcases Nat.lt_or_ge l' X.length with hl' | hl'
    · rw [hent 0 l' hl']
      exact getD_mem_P hl' (P := fun x => 0 < x.1) (fun x hx => hX0 x hx)
    · have hlx : l' = X.length := by omega
      subst hlx
      rw [hM, List.nil_append, List.cons_append, entry_cons,
        show X.length = X.length + 0 from rfl, entry_append_right]
      simp [entry]
  have hle : ∀ i, i < X.length → le1 M 0 (1 + i) := by
    intro i hi
    rw [le1_zero_iff hr (by omega)]
    intro y hy hy0
    have hyle := rtg0_le hy
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    rw [hent 1 y' (by omega), h10]
    exact getD_mem_P (by omega) (P := fun x => v < x.2.1) (fun x hx => hX1 x hx)
  simp only [List.length_nil, Nat.zero_add, shiftr01, List.map_cons, List.map_map,
    Function.comp_def, Nat.add_zero, List.cons.injEq, true_and]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < X.length := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  rw [if_pos (hle i hi)]
  have e0 : entry X 0 i = X[i].1 := by
    show (X.getD i (0, 0, 0)).1 = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have e1 : entry X 1 i = X[i].2.1 := by
    show (X.getD i (0, 0, 0)).2.1 = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have e2 : entry X 2 i = X[i].2.2 := by
    show (X.getD i (0, 0, 0)).2.2 = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  rw [e0, e1, e2]

theorem Pz_succ (v : ℕ) (X : TrioSeq) (n : ℕ) :
    Pz v X (n + 1) = ((0, v, 0) : ℕ × ℕ × ℕ) ::
      (X ++ shiftr01 1 0 (Pz (v + 1) (shiftr01 0 1 X) n)) := by
  unfold Pz
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, GwV.shiftr01_flatMap]
  have e0 : shiftr01 0 0 (((0, v + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 0 0 X)
      = ((0, v, 0) : ℕ × ℕ × ℕ) :: X := by simp
  rw [e0, List.cons_append]
  congr 2
  apply List.flatMap_congr
  intro k _
  simp only [shiftr01, List.map_cons, List.map_map, Function.comp_def, Nat.succ_eq_add_one]
  congr 1
  · refine Prod.ext (by dsimp only; omega) (Prod.ext (by dsimp only; omega) rfl)
  · apply List.map_congr_left
    intro p _
    refine Prod.ext (by dsimp only; omega) (Prod.ext (by dsimp only; omega) rfl)

theorem Pz_head (v : ℕ) (X : TrioSeq) (n : ℕ) : entry (shiftr01 1 0 (Pz v X n)) 0 0 ≤ 1 := by
  cases n with
  | zero => simp [Pz, shiftr01, entry]
  | succ m => rw [Pz_succ]; simp [shiftr01, entry]

theorem Mono_Pz {X : TrioSeq} (hX : Mono X) (v n : ℕ) : Mono (Pz v X n) := by
  intro x hx
  simp only [Pz, List.mem_flatMap, List.mem_range, shiftr01, List.mem_map, List.mem_cons] at hx
  obtain ⟨k, -, p, hp, rfl⟩ := hx
  rcases hp with rfl | ⟨q, hq, rfl⟩
  · dsimp only; omega
  · have := hX q hq; dsimp only; omega

theorem Pz_Wg (F : ℕ → TrioSeq) (hsh : ∀ u, shiftr01 0 1 (F u) = F (u + 1))
    (hst : ∀ u, 1 ≤ u → F u ∈ Wstarv u) (hge : ∀ u, ∀ x ∈ F u, 1 ≤ x.1) :
    ∀ n v, 1 ≤ v → Pz v (F v) n ∈ Wg (2 * v)
  | 0, v, _ => by simpa [Pz] using Wg_nil (2 * v)
  | (n + 1), v, hv => by
      rw [Pz_succ, hsh]
      exact hangv (hst v hv) (hge v) (Wg_shift (Pz_Wg F hsh hst hge n (v + 1) (by omega)) 1)
        (shift1_ge _) (Pz_head _ _ _) (2 * v) le_rfl

/-! ## 族 `Aj` -/

def Aj (v j : ℕ) : TrioSeq :=
  [((1, v + 1, 1) : ℕ × ℕ × ℕ), ((2, v + 1, 0) : ℕ × ℕ × ℕ)] ++
    List.replicate j ((1, v + 1, 1) : ℕ × ℕ × ℕ)

theorem Aj_sh (j u : ℕ) : shiftr01 0 1 (Aj u j) = Aj (u + 1) j := by
  simp [Aj, shiftr01, List.map_replicate]

theorem Aj_ge (v j : ℕ) : ∀ x ∈ Aj v j, 1 ≤ x.1 := by
  intro x hx
  simp only [Aj, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_replicate] at hx
  rcases hx with (rfl | rfl) | ⟨-, rfl⟩ <;> (dsimp only; omega)

theorem Aj_ge1 (v j : ℕ) : ∀ x ∈ Aj v j, v + 1 ≤ x.2.1 := by
  intro x hx
  simp only [Aj, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_replicate] at hx
  rcases hx with (rfl | rfl) | ⟨-, rfl⟩ <;> (dsimp only; omega)

theorem Aj_mono (v j : ℕ) : Mono (Aj v j) := by
  intro x hx
  simp only [Aj, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_replicate] at hx
  rcases hx with (rfl | rfl) | ⟨-, rfl⟩ <;> (dsimp only; omega)

theorem Aj_succ (v j : ℕ) : Aj v (j + 1) = Aj v j ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)] := by
  simp [Aj, List.replicate_succ']

theorem Aj_star : ∀ j v, 1 ≤ v → Aj v j ∈ Wstarv v
  | 0, v, hv => by
      intro _ a ha
      have h := Wg_mono ha (G2cv_Wg v hv)
      simpa [Aj, R12v] using h
  | (j + 1), v, hv => by
      intro _ a ha
      rw [Aj_succ]
      have e : (((0, v, 0) : ℕ × ℕ × ℕ) :: (Aj v j ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]))
          = (((0, v, 0) : ℕ × ℕ × ℕ) :: Aj v j) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)] := rfl
      rw [e]
      refine A1g_intro (Or.inr (Or.inl ⟨natDom_zroot v (Aj_ge v j), fun n _ => ?_⟩))
      rw [oper_zall v (Aj v j) (Aj_ge v j) (Aj_ge1 v j) n]
      exact Wg_mono ha (Pz_Wg (fun u => Aj u j) (Aj_sh j) (fun u hu => Aj_star j u hu)
        (fun u => Aj_ge u j) n v hv)

/-! ## 段 0 -/

theorem Aok_root {X : TrioSeq} (hmem : (((0, 0, 0) : ℕ × ℕ × ℕ) :: X) ∈ W 0)
    (hge : ∀ x ∈ X, 1 ≤ x.1) (hmo : Mono X) : Aok (((0, 0, 0) : ℕ × ℕ × ℕ) :: X) := by
  refine ⟨hmem, by simp, ⟨by simp [entry], ?_⟩, ?_, ?_⟩
  · intro j hj1 hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [entry_cons]
    exact getD_mem_P (by simpa using hj) (P := fun x => 1 ≤ x.1) hge
  · intro c hc h0
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp
    · have := hge c hc; omega
  · intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp
    · exact hmo c hc

theorem Aj0 : ∀ j, Aok (((0, 0, 0) : ℕ × ℕ × ℕ) :: Aj 0 j)
  | 0 => by simpa [Aj, R338] using Aok_R338
  | (j + 1) => by
      refine Aok_root ?_ (Aj_ge 0 (j + 1)) (Aj_mono 0 (j + 1))
      rw [Aj_succ]
      have e : (((0, 0, 0) : ℕ × ℕ × ℕ) :: (Aj 0 j ++ [((1, 0 + 1, 1) : ℕ × ℕ × ℕ)]))
          = (((0, 0, 0) : ℕ × ℕ × ℕ) :: Aj 0 j) ++ [((1, 0 + 1, 1) : ℕ × ℕ × ℕ)] := rfl
      rw [e]
      refine A1_intro (Or.inr (Or.inl ?_))
      intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [oper_zall 0 (Aj 0 j) (Aj_ge 0 j) (Aj_ge1 0 j), Pz_succ, Aj_sh]
      have hT : shiftr01 1 0 (Pz 1 (Aj 1 j) m) ∈ Wg 2 :=
        Wg_shift (Pz_Wg (fun u => Aj u j) (Aj_sh j) (fun u hu => Aj_star j u hu)
          (fun u => Aj_ge u j) m 1 le_rfl) 1
      have h := GwY.base_hang _ hT (shift1_ge _) (Mono_shift (Mono_Pz (Aj_mono 1 j) 1 m) 1)
        (Pz_head _ _ _) _ (Aj0 j)
      simpa [List.cons_append] using h

/-- ★ シート行 456 `(0,0,0)(1,1,1)(2,1,0)(1,1,1)(1,1,1)`。 -/
theorem R456_mem : Gm ++ [((1, 1, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa [Aj, Gm] using (Aj0 2).mem

/-- ★ シート行 461 `… (1,1,1)(1,1,1)`。 -/
theorem R461_mem : Gm ++ [((1, 1, 1) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa [Aj, Gm, List.replicate] using (Aj0 3).mem

/-- ★ シート行 462 `… (1,1,1)(1,1,1)(1,1,1)`。 -/
theorem R462_mem : Gm ++ [((1, 1, 1) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ),
    ((1, 1, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  simpa [Aj, Gm, List.replicate] using (Aj0 4).mem

/-- ★ シート行 463 `(0,0,0)(1,1,1)(2,1,0)(1,1,1)(2,0,0)`。 -/
theorem R463_mem : Gm ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n _
  have e : Gm ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] = [((0, 0, 0) : ℕ × ℕ × ℕ), ((1, 1, 1) : ℕ × ℕ × ℕ),
      ((2, 1, 0) : ℕ × ℕ × ℕ)] ++ [((1, 1, 1) : ℕ × ℕ × ℕ)] ++ [((2, 0, 0) : ℕ × ℕ × ℕ)] := rfl
  rw [e, oper_snoc00'' _ (M := [((1, 1, 1) : ℕ × ℕ × ℕ)]) (d := 2) (by simp) (by simp [entry])
    (by intro r hr1 hr2; simp at hr2; omega) n, flatMap_const_singleton]
  simpa [Aj] using (Aj0 n).mem

/-- ★ シート行 457 `… (1,1,1)(1,1,1)(1,1,0)`。 -/
theorem R457_mem : Gm ++ [((1, 1, 1) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := GwY.base_hang _ Wg2_110 (by decide) (by unfold Mono; decide) (by simp [entry]) _ (Aj0 2)
  simpa [Aj, Gm] using h

/-- ★ シート行 458 `… (1,1,1)(1,1,1)(1,1,0)(2,2,1)(3,2,0)(2,2,1)`。 -/
theorem R458_mem : Gm ++ [((1, 1, 1) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := GwY.base_hang _ L4_Wg L4_ge L4_mono (by simp [entry, GxC.L4]) _ (Aj0 2)
  simpa [Aj, Gm, GxC.L4] using h

/-- ★ シート行 459 `… (1,1,0)(2,2,1)(3,2,0)(2,2,1)(2,2,1)`。 -/
theorem R459_mem : Gm ++ [((1, 1, 1) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hZ : (((0, 1, 0) : ℕ × ℕ × ℕ) :: Aj 1 2) ∈ Wg 2 := Aj_star 2 1 le_rfl (fun p hp => Aj_ge 1 2 p hp) 2 le_rfl
  have h := GwY.base_hang _ (Wg_shift hZ 1) (shift1_ge _) (Mono_shift (by
    intro x hx; simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · exact Aj_mono 1 2 x hx) 1) (by simp [shiftr01, entry]) _ (Aj0 2)
  simpa [Aj, Gm, shiftr01, List.replicate] using h

/-- ★ シート行 460 `… (1,1,0)(2,2,1)(3,2,0)(2,2,1)(2,2,1)(2,2,0)`。 -/
theorem R460_mem : Gm ++ [((1, 1, 1) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((2, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hZ := tower_snoc 1 (Aj_star 2 1 le_rfl) (Aj_ge 1 2) 2 le_rfl
  have h := GwY.base_hang _ (Wg_shift hZ 1) (shift1_ge _) (Mono_shift (by
    intro x hx; simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | hx | rfl
    · simp
    · exact Aj_mono 1 2 x hx
    · simp) 1) (by simp [shiftr01, entry]) _ (Aj0 2)
  simpa [Aj, Gm, shiftr01, List.replicate] using h

#print axioms R456_mem
#print axioms R463_mem
#print axioms R460_mem

end GxF
end TRIO
