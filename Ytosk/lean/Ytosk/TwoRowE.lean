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

/-- **The matrix value drops with the top of the path.** -/
theorem ev2r_lt_of_top {M N : Mat} {x ρ : Nat} (hx : x + 1 = M.length) (hG : Good2 M)
    (hRD : RootsDec M) (hρ : Anc0 M ρ x) (hρ0 : col M ρ = (0, 0, 0)) (hroots : roots N = roots M)
    (hoff : ∀ c ∈ roots M, c < ρ → o2r N c = o2r M c)
    (hot : isOT (o2r N ρ) = true) (hlt : o2r N ρ < o2r M ρ) :
    isOT (ev2r N) = true ∧ ev2r N < ev2r M := by
  have hsplit := roots_split hx hρ hρ0
  set R := (roots M).filter (fun c => decide (c < ρ)) with hRdef
  have hRv : R.map (o2r N) = R.map (o2r M) := by
    apply List.map_congr_left
    intro c hc
    rw [hRdef, List.mem_filter] at hc
    exact hoff c hc.1 (by simpa using hc.2)
  have hdM : (R.map (o2r M) ++ [o2r M ρ]).Pairwise (fun a b => b ≤ a) := by
    have := hRD; unfold RootsDec at this
    rw [hsplit, List.map_append] at this; exact this
  have hdM' := List.pairwise_append.mp hdM
  have hsing : ∀ t ∈ R.map (o2r M), Single t := by
    intro t ht; obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht; exact single_o2r hG i
  have hdN : (R.map (o2r M) ++ [o2r N ρ]).Pairwise (fun a b => b ≤ a) := by
    rw [List.pairwise_append]
    refine ⟨hdM'.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb
    exact le_trans (le_of_lt hlt) (hdM'.2.2 a ha _ (List.mem_singleton_self _))
  have hsN : ∀ t ∈ R.map (o2r M) ++ [o2r N ρ], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsing t ht
    · rw [List.mem_singleton] at ht; subst ht; exact ⟨hot, o2r_psi_form _ _⟩
  have hsM : ∀ t ∈ R.map (o2r M) ++ [o2r M ρ], Single t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hsing t ht
    · rw [List.mem_singleton] at ht; subst ht; exact single_o2r hG ρ
  have eN : ev2r N = app (sumN (R.map (o2r M))) (o2r N ρ) := by
    rw [ev2r_roots, hroots, hsplit, List.map_append, hRv]
    exact sumN_snoc_dec hsN hdN
  have eM : ev2r M = app (sumN (R.map (o2r M))) (o2r M ρ) := by
    rw [ev2r_roots, hsplit, List.map_append]
    exact sumN_snoc_dec hsM hdM
  refine ⟨?_, ?_⟩
  · have := (sumN_dec _ hsN hdN).1
    rw [eN, ← sumN_snoc_dec hsN hdN]; exact this
  · rw [eN, eM]; exact (app_lt_app_left_iff _).mpr hlt

end Ytosk
