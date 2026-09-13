/-
GxE.lean: シート行 443, 451〜455。

- `dead_snoc v`: `A ∈ Wstarv v` の後ろに根とタイの `(1,v,0)`（死んだ孤児）を置いた根の列は `Wg (2v)`。
  graft の荷 `y ∈ Wg (2v-1)` は `hang_Wg` で `A` の後ろに継ぐ。
- 行 443 = `Gm ++ ((0,1,0) :: (X1 ++ (1,1,0)))↑1`、行 451〜455 は `X1` の後ろに段 2 の部品。
-/
import GxD

namespace TRIO
namespace GxE

open Wset
open Small
open GwS
open Gw
open GwU
open GwZ
open GxA
open GxD

theorem dead_snoc (v : ℕ) (hv : 1 ≤ v) {A : TrioSeq} (hA : A ∈ Wstarv v)
    (hAge : ∀ x ∈ A, 1 ≤ x.1) :
    ∀ a, 2 * v ≤ a → (((0, v, 0) : ℕ × ℕ × ℕ) :: (A ++ [((1, v, 0) : ℕ × ℕ × ℕ)])) ∈ Wg a := by
  set c : ℕ × ℕ × ℕ := (1, v, 0) with hc
  set P : TrioSeq := ((0, v, 0) : ℕ × ℕ × ℕ) :: A with hPdef
  have eZ : (((0, v, 0) : ℕ × ℕ × ℕ) :: (A ++ [c])) = P ++ [c] := rfl
  rw [eZ]
  have hZlen : (P ++ [c]).length - 1 = P.length + 0 := by simp
  have hlast : ∀ i, entry (P ++ [c]) i ((P ++ [c]).length - 1) = entry [c] i 0 := by
    intro i
    rw [hZlen, entry_append_right]
  have e0 : entry (P ++ [c]) 0 ((P ++ [c]).length - 1) = 1 := by rw [hlast 0]; simp [entry, hc]
  have e1 : entry (P ++ [c]) 1 ((P ++ [c]).length - 1) = v := by rw [hlast 1]; simp [entry, hc]
  have e2 : entry (P ++ [c]) 2 ((P ++ [c]).length - 1) = 0 := by rw [hlast 2]; simp [entry, hc]
  have hPlen : P.length = A.length + 1 := by simp [hPdef]
  have hent : ∀ j, 1 ≤ j → j < P.length → 1 ≤ entry (P ++ [c]) 0 j := by
    intro j hj1 hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hj' : j' < A.length := by omega
    rw [Small.entry_append_left hj, hPdef, entry_cons]
    have hmem : A.getD j' (0, 0, 0) ∈ A := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
      exact List.getElem_mem _
    exact hAge _ hmem
  have h00 : entry (P ++ [c]) 1 0 = v := by
    rw [Small.entry_append_left (by simp [hPdef])]; simp [hPdef, entry]
  have hsr : srow (P ++ [c]) ((P ++ [c]).length - 1) = 1 := by
    unfold srow; rw [e2, e1]; simp; omega
  have hd : domT (P ++ [c]) (2 * v - 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2]; omega
    · rw [hsr]
      rintro ⟨k, hk, -⟩
      have hk' : nextrel1 (P ++ [c]) k ((P ++ [c]).length - 1) := by
        unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
      obtain ⟨-, -, hkl, hk1, ⟨-, -, hrt⟩, -⟩ := hk'
      rw [e1] at hk1
      rcases Relation.ReflTransGen.cases_tail hrt with heq | ⟨b, hkb, hb⟩
      · omega
      · obtain ⟨-, -, hbl, hb0, -⟩ := hb
        rw [e0] at hb0
        have hb00 : b = 0 := by
          by_contra hne
          have := hent b (by omega) (by rw [hZlen] at hbl; omega)
          omega
        subst hb00
        have hk0 : k = 0 := by have := rtg0_le hkb; omega
        subst hk0
        omega
  intro a ha
  refine A1g_intro (Or.inr (Or.inr ⟨2 * v - 1, by omega, hd, e2, fun y hy hby => ?_⟩))
  rw [graft_eq_shift, e0, List.dropLast_concat, hPdef]
  refine hangv hA hAge (Wg_shift hy 1) (shift1_ge y) ?_ a ha
  unfold based at hby
  cases y with
  | nil => simp [shiftr01, entry]
  | cons p y' =>
      simp [entry] at hby
      simp [shiftr01, entry, hby]

def Xv (v : ℕ) : TrioSeq :=
  [((1, v + 1, 1) : ℕ × ℕ × ℕ), ((2, v + 1, 0) : ℕ × ℕ × ℕ), ((1, v + 1, 1) : ℕ × ℕ × ℕ)]

theorem Xv_star (v : ℕ) (hv : 1 ≤ v) : Xv v ∈ Wstarv v := fun _ a ha => L4v_Wg v hv a ha

theorem Xv_ge (v : ℕ) : ∀ x ∈ Xv v, 1 ≤ x.1 := by
  intro x hx
  simp only [Xv, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> (dsimp only; omega)

/-- ★ シート行 443 `… (1,1,0)(2,2,1)(3,2,0)(2,2,1)(2,1,0)`。 -/
theorem R443_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 1, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hZ := dead_snoc 1 le_rfl X1_star X1_ge 2 le_rfl
  have h := BHs hZ (by unfold Mono X1; decide) (by simp [entry])
  simpa [shiftr01, X1] using h

theorem B451 : (((0, 2, 0) : ℕ × ℕ × ℕ) :: [((1, 3, 1) : ℕ × ℕ × ℕ), ((2, 3, 0) : ℕ × ℕ × ℕ),
    ((1, 3, 1) : ℕ × ℕ × ℕ), ((1, 0, 0) : ℕ × ℕ × ℕ)]) ∈ Wg 4 := by
  have e : (((0, 2, 0) : ℕ × ℕ × ℕ) :: [((1, 3, 1) : ℕ × ℕ × ℕ), ((2, 3, 0) : ℕ × ℕ × ℕ),
      ((1, 3, 1) : ℕ × ℕ × ℕ), ((1, 0, 0) : ℕ × ℕ × ℕ)])
      = [] ++ L4v 2 ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := rfl
  rw [e]
  refine A1g_intro (Or.inr (Or.inl ⟨natDom_iff.mpr (Or.inl (by simp [lev, entry, L4v])),
    fun n _ => ?_⟩))
  rw [oper_snoc00'' [] (M := L4v 2) (d := 1) (by simp [L4v]) (by simp [L4v, entry]) (by
    intro r hr1 hr2
    simp [L4v] at hr2
    rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl <;> simp [L4v, entry]) n]
  simp only [List.nil_append]
  exact Wg_flatMap_copies (L4v_Wg 2 (by omega) 4 le_rfl) (by
    intro p _
    simp [L4v, entry]) n

/-- ★ シート行 451 `… (2,2,0)(3,3,1)(4,3,0)(3,3,1)(3,0,0)`。 -/
theorem R451_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ),
    ((3, 3, 1) : ℕ × ℕ × ℕ), ((4, 3, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((3, 0, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have h := rowX1 B451 (by unfold Mono; decide)
  simpa [shiftr01, X1] using h

/-- ★ シート行 452 `… (2,2,0)(3,3,1)(4,3,0)(3,3,1)(3,2,0)`。 -/
theorem R452_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ),
    ((3, 3, 1) : ℕ × ℕ × ℕ), ((4, 3, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hB := dead_snoc 2 (by omega) (Xv_star 2 (by omega)) (Xv_ge 2) 4 le_rfl
  have h := rowX1 hB (by unfold Mono Xv; decide)
  simpa [shiftr01, X1, Xv] using h

/-- ★ シート行 453 `… (2,2,0)(3,3,1)(4,3,0)(3,3,1)(3,3,0)`。 -/
theorem R453_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ),
    ((3, 3, 1) : ℕ × ℕ × ℕ), ((4, 3, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((3, 3, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hB := tower_snoc 2 (Xv_star 2 (by omega)) (Xv_ge 2) 4 le_rfl
  have h := rowX1 hB (by unfold Mono Xv; decide)
  simpa [shiftr01, X1, Xv] using h

/-- ★ シート行 454 `… (4,3,0)(3,3,1)(3,3,0)(4,4,1)(5,4,0)(4,4,1)`。 -/
theorem R454_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ),
    ((3, 3, 1) : ℕ × ℕ × ℕ), ((4, 3, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((3, 3, 0) : ℕ × ℕ × ℕ), ((4, 4, 1) : ℕ × ℕ × ℕ), ((5, 4, 0) : ℕ × ℕ × ℕ),
    ((4, 4, 1) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hR : shiftr01 1 0 (L4v 3) ∈ Wg 6 := Wg_shift (L4v_Wg 3 (by omega) 6 le_rfl) 1
  have hB := hangv (Xv_star 2 (by omega)) (Xv_ge 2) hR (shift1_ge _)
    (by simp [shiftr01, entry, L4v]) 4 le_rfl
  have h := rowX1 hB (by simp [Mono, Xv, L4v, shiftr01])
  simpa [shiftr01, X1, Xv, L4v] using h

/-- ★ シート行 455 `… (3,3,0)(4,4,1)(5,4,0)(4,4,1)(4,4,0)`。 -/
theorem R455_mem : Gm ++ [((1, 1, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ),
    ((3, 2, 0) : ℕ × ℕ × ℕ), ((2, 2, 1) : ℕ × ℕ × ℕ), ((2, 2, 0) : ℕ × ℕ × ℕ),
    ((3, 3, 1) : ℕ × ℕ × ℕ), ((4, 3, 0) : ℕ × ℕ × ℕ), ((3, 3, 1) : ℕ × ℕ × ℕ),
    ((3, 3, 0) : ℕ × ℕ × ℕ), ((4, 4, 1) : ℕ × ℕ × ℕ), ((5, 4, 0) : ℕ × ℕ × ℕ),
    ((4, 4, 1) : ℕ × ℕ × ℕ), ((4, 4, 0) : ℕ × ℕ × ℕ)] ∈ W 0 := by
  have hT := tower_snoc 3 (Xv_star 3 (by omega)) (Xv_ge 3) 6 le_rfl
  have hR := Wg_shift hT 1
  have hB := hangv (Xv_star 2 (by omega)) (Xv_ge 2) hR (shift1_ge _)
    (by simp [shiftr01, entry]) 4 le_rfl
  have h := rowX1 hB (by simp [Mono, Xv, shiftr01])
  simpa [shiftr01, X1, Xv] using h

#print axioms R443_mem
#print axioms R455_mem

end GxE
end TRIO
