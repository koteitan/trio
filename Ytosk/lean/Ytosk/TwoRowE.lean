/-
**2 行: 行列全体の値（根の和 `ev2r`）の段。**

経路の一番上の祖先 ρ（根）は最後の根で、ev2r = （前の根の値の和）+ o(ρ)。展開で根の並びが変わらなければ、
ρ の値が小さく標準形になれば ev2r も小さく標準形になる。
-/
import Ytosk.TwoRowZ2

namespace Ytosk

open T

/-- The root columns. -/
def roots (M : Mat) : List Nat := (List.range M.length).filter (fun i => decide (col M i = (0, 0, 0)))

theorem ev2r_roots (M : Mat) : ev2r M = sumN ((roots M).map (o2r M)) := rfl

theorem roots_sorted (M : Mat) : (roots M).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

theorem mem_roots {M : Mat} {c : Nat} : c ∈ roots M ↔ c < M.length ∧ col M c = (0, 0, 0) := by
  unfold roots; rw [List.mem_filter, List.mem_range]; simp

/-- Root values, left to right, do not increase. -/
def RootsDec (M : Mat) : Prop := ((roots M).map (o2r M)).Pairwise (fun a b => b ≤ a)

/-- **The top of the path is the last root.** -/
theorem roots_split {M : Mat} {x ρ : Nat} (hx : x + 1 = M.length) (hρ : Anc0 M ρ x)
    (hρ0 : col M ρ = (0, 0, 0)) :
    roots M = (roots M).filter (fun c => decide (c < ρ)) ++ [ρ] := by
  apply split_last_max _ ρ (roots_sorted M) (mem_roots.mpr ⟨by have := hρ.le; omega, hρ0⟩)
  intro c hc
  obtain ⟨hcl, hc0⟩ := mem_roots.mp hc
  by_contra hcon
  have h1 := anc0_interval hρ c (by omega) (by omega)
  have e1 : entry M 0 c = 0 := by unfold entry; unfold col at hc0; rw [hc0]; rfl
  omega

/-- **Roots unchanged** when the columns before `x` agree and no later column is a root. -/
theorem roots_eq {M N : Mat} {x : Nat} (hx : x + 1 = M.length) (hNl : x ≤ N.length)
    (hpre : ∀ c, c < x → col N c = col M c) (hxr : col M x ≠ (0, 0, 0))
    (hcopy : ∀ c, x ≤ c → c < N.length → col N c ≠ (0, 0, 0)) : roots N = roots M := by
  apply eq_of_sorted_mem _ _ (roots_sorted N) (roots_sorted M)
  intro c
  rw [mem_roots, mem_roots]
  constructor
  · rintro ⟨hcl, hc0⟩
    rcases Nat.lt_or_ge c x with h | h
    · rw [hpre c h] at hc0; exact ⟨by omega, hc0⟩
    · exact absurd hc0 (hcopy c h hcl)
  · rintro ⟨hcl, hc0⟩
    rcases Nat.lt_or_ge c x with h | h
    · rw [← hpre c h] at hc0; exact ⟨by omega, hc0⟩
    · have : c = x := by omega
      subst this; exact absurd hc0 hxr

end Ytosk
