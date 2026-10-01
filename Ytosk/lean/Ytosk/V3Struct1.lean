/-
**3 行の構造の補題 (1)**: 経路の行 1（hpath）。

r = P_1(x) のとき、r と x の間の x の祖先 s は行 1 が r より大きい（P_1 は祖先の列で最初に行 1 が小さい列）。
-/
import Ytosk.V3MainT1

namespace Ytosk

open T

theorem mem_ancL_of_anc {M : Mat} {s b : Nat} (h : Anc0 M s b) (hne : s ≠ b) : s ∈ ancL M b := by
  induction h with
  | refl => exact absurd rfl hne
  | @step b' c hp ha ih =>
    rw [ancL_eq hp]
    by_cases hsb : s = b'
    · subst hsb; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hsb)

/-- **The row-1 path condition** from `r = P_1(x)`. -/
theorem hpath_of_par1 {M : Mat} {r x : Nat} (h1 : par M 1 x = some r) (hA : Anc0 M r x) (hrx : r ≠ x) :
    ∀ s, Anc0 M r s → Anc0 M s x → s ≠ r → s ≠ x → entry M 1 r < entry M 1 s := by
  intro s hrs hsx hsr hsx'
  obtain ⟨S, hS, hSp⟩ := ancL_through hA hrx
  rw [par1_find, hS] at h1
  have hpr : entry M 1 r < entry M 1 x := by
    have := List.find?_some h1; simpa using this
  have hsS : s ∈ S := by
    have hm := mem_ancL_of_anc hsx hsx'
    rw [hS] at hm
    rcases List.mem_append.mp hm with h | h
    · exact h
    · exfalso
      have hrs' : r < s := lt_of_le_of_ne hrs.le (Ne.symm hsr)
      rcases List.mem_cons.mp h with h | h
      · exact hsr h
      · have := mem_ancL_lt h; omega
  have hnone : S.find? (fun q => decide (entry M 1 q < entry M 1 x)) = none := by
    rw [List.find?_append] at h1
    cases hf : S.find? (fun q => decide (entry M 1 q < entry M 1 x)) with
    | none => rfl
    | some t =>
      rw [hf] at h1
      simp only [Option.some_or] at h1
      have ht := List.mem_of_find?_eq_some hf
      rw [Option.some.inj h1] at ht
      have := (hSp r ht).1; omega
  have := List.find?_eq_none.mp hnone s hsS
  simp at this
  omega

end Ytosk
