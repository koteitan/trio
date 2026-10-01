/-
**3 行・t = 1: x より前の列の構造は M と N で同じ。**

N = gexp M r L d0 0 n（n ≥ 2）、x = r + L。x より前の列 i で
- 子・P_1・行 1・行 2 は同じ（`children_N_lt` ほか）、
- 上げは同じ（x − 1 では、N の x が上げの形にならないことを使う、`upg_N_lt`）、
- topped は同じ（q の最後の子 x は、N でも M でものりしろの子でない）、
- 子 x の寄与は M でも N でも o(x)（x は上げられない）。
上げられること（isUpg）の一致は仮定 `hiu`・`hiux` に置く（`sameAt_lt`）。
-/
import Ytosk.V3Copy5

namespace Ytosk

open T

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- The parent of `x` in `N` is that in `M`. -/
theorem par0_N_x : par (TRIO.gexp M r L d0 0 n) 0 (r + L) = par M 0 (r + L) := by
  apply par0_congr_e0
  intro q hq
  rcases Nat.lt_or_ge q (r + L) with h | h
  · exact e0_gexp_pre hlen hL hd0e (by omega) h
  · rw [show q = r + L by omega]; exact e0_gexp_x hlen hL hd0e hn

/-- **Children before `x`.** -/
theorem children_N_lt {i : Nat} (hi : i < r + L) :
    children (TRIO.gexp M r L d0 0 n) i = children M i := by
  have hlN := len_N (d0 := d0) hlen hn
  have hnL : L ≤ (n - 1) * L := by
    have := Nat.mul_le_mul_right L (show 1 ≤ n - 1 by omega); simpa using this
  unfold children
  rw [hlN, ← hlen, show r + L + (n - 1) * L = (r + L + 1) + ((n - 1) * L - 1) by omega,
    List.range_add, List.filter_append]
  have h2 : List.filter (fun c => decide (par (TRIO.gexp M r L d0 0 n) 0 c = some i))
      (List.map (fun c => r + L + 1 + c) (List.range ((n - 1) * L - 1))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
    have hc'' := List.mem_range.mp hc'
    obtain ⟨p, hp, hpx⟩ := par0_gexp_ge (d1 := 0) (n := n) hlen hL hA hd0e
      (c := r + L + 1 + c') (by omega) (by
        have : n * L = (n - 1) * L + L := by rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
        omega)
    rw [hp]; simp; omega
  rw [h2, List.append_nil]
  apply List.filter_congr
  intro c hc
  have hc' := List.mem_range.mp hc
  rcases Nat.lt_or_ge c (r + L) with h3 | h3
  · rw [par_gexp_pre hlen (by omega) 0 h3]
  · rw [show c = r + L by omega, par0_N_x hlen hL hA hd0e hn]

omit hA in
theorem upg_N_lt {i : Nat} (hi : i + 1 < r + L) :
    upg (TRIO.gexp M r L d0 0 n) i = upg M i := by
  rw [← upg_take _ hi, gexp_take_x hlen (by omega), upg_take M hi]

/-- `q`, the parent of `x`, is at or after `r`. -/
theorem q_ge_r {q : Nat} (hq : par M 0 (r + L) = some q) : r ≤ q :=
  par0_ge_of_anc hA (by omega) (Nat.le_refl _) hq

/-- **The upgrade at `x − 1`.** -/
theorem upg_N_xm1 (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0) :
    upg (TRIO.gexp M r L d0 0 n) (r + L - 1) = upg M (r + L - 1) := by
  have hlN := len_N (d0 := d0) hlen hn
  have hnL : L ≤ (n - 1) * L := by
    have := Nat.mul_le_mul_right L (show 1 ≤ n - 1 by omega); simpa using this
  have hi : r + L - 1 < r + L := by omega
  unfold upg
  rw [entry_gexp_pre hlen (by omega) 1 hi, entry_gexp_pre hlen (by omega) 2 hi,
    par_gexp_pre hlen (by omega) 1 hi]
  have hlenN : ¬ (r + L - 1 + 1 = (TRIO.gexp M r L d0 0 n).length) := by omega
  have hlenM : ¬ (r + L - 1 + 1 = M.length) := by omega
  by_cases hc : entry M 1 (r + L - 1) = 0 ∨ entry M 2 (r + L - 1) = 1
  · rw [if_pos (by rcases hc with h | h; exact Or.inl h; exact Or.inr (Or.inl h)),
      if_pos (by rcases hc with h | h; exact Or.inl h; exact Or.inr (Or.inl h))]
  · have hc1 : ¬ (entry M 1 (r + L - 1) = 0 ∨ entry M 2 (r + L - 1) = 1 ∨
        r + L - 1 + 1 = (TRIO.gexp M r L d0 0 n).length) := by
      intro h
      rcases h with h | h | h
      · exact hc (Or.inl h)
      · exact hc (Or.inr h)
      · exact hlenN h
    have hc2 : ¬ (entry M 1 (r + L - 1) = 0 ∨ entry M 2 (r + L - 1) = 1 ∨
        r + L - 1 + 1 = M.length) := by
      intro h
      rcases h with h | h | h
      · exact hc (Or.inl h)
      · exact hc (Or.inr h)
      · exact hlenM h
    rw [if_neg hc1, if_neg hc2]
    cases hm : par M 1 (r + L - 1) with
    | none => rfl
    | some m =>
      simp only
      have hmx : m < r + L - 1 := par_lt M 1 _ m hm
      rw [upgClimb_find, upgClimb_find, show r + L - 1 + 1 = r + L by omega, entry_gexp_pre hlen (by omega) 0 (show m < r + L by omega),
        entry_gexp_pre hlen (by omega) 2 (show m < r + L by omega)]
      -- the `i + 1` clause fails in `M` (row 2 of `x` is `0`) and in `N` (`x` would be a child of `m`)
      have hM : ¬ (par M 1 (r + L) = some m ∧ col M (r + L) =
          (entry M 0 m + 1, entry M 1 (r + L - 1), entry M 2 m + 1)) := by
        rintro ⟨_, h2⟩
        have : (col M (r + L)).2.2 = entry M 2 (r + L) := rfl
        rw [h2] at this; simp at this; omega
      have hN : ¬ (par (TRIO.gexp M r L d0 0 n) 1 (r + L) = some m ∧
          col (TRIO.gexp M r L d0 0 n) (r + L) =
            (entry M 0 m + 1, entry M 1 (r + L - 1), entry M 2 m + 1)) := by
        rintro ⟨h1, h2⟩
        rw [par1_root hlen hL hA hd0e hn hpath] at h1
        have hAm := anc0_of_par M 1 m r h1
        have hmr := par_lt M 1 r m h1
        have he : entry M 0 (r + L) = entry M 0 m + 1 := by
          have : (col (TRIO.gexp M r L d0 0 n) (r + L)).1 = entry (TRIO.gexp M r L d0 0 n) 0 (r + L) := rfl
          rw [h2, e0_gexp_x hlen hL hd0e hn] at this; simp at this; omega
        have hp0 : par M 0 (r + L) = some m := by
          rw [par0_spec]
          refine ⟨by omega, by omega, fun j hj1 hj2 => ?_⟩
          have := anc0_interval (hAm.trans hA) j hj1 (by omega)
          omega
        have := q_ge_r hlen hL hA hd0e hn hp0
        omega
      rw [if_neg hN, if_neg hM,
        ancL_N_pre hlen hL hA hd0e hn (by omega), e0_gexp_x hlen hL hd0e hn]
      apply find?_congr'
      intro q hq
      have := mem_ancL_lt hq
      rw [par_gexp_pre hlen (by omega) 1 (by omega), col_gexp_pre hlen (by omega) (by omega),
        entry_gexp_pre hlen (by omega) 0 (by omega)]

/-- **Topped before `x`.** -/
theorem topped_N_lt (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hqr : ∀ q, par M 0 (r + L) = some q → q ≠ r) {c : Nat} (hc : c < r + L) :
    topped (TRIO.gexp M r L d0 0 n) c = topped M c := by
  unfold topped
  rw [children_N_lt hlen hL hA hd0e hn hc]
  cases hd : (children M c).getLast? with
  | none => rfl
  | some d =>
    simp only
    have hdm := List.mem_of_getLast? hd
    have hdc := mem_children hdm
    have hb : bump (TRIO.gexp M r L d0 0 n) c = bump M c := by
      unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hc, entry_gexp_pre hlen (by omega) 1 hc]
    rw [hb]
    rcases Nat.lt_or_ge d (r + L) with h | h
    · rw [col_gexp_pre hlen (by omega) h]
    · have hdx : d = r + L := by omega
      subst hdx
      -- `c` is the parent of `x`, on the path, so row 1 of `c` exceeds row 1 of `r`
      have hpc := (mem_children_iff.mp hdm).2
      have hrc := q_ge_r hlen hL hA hd0e hn hpc
      have hcA : Anc0 M c (r + L) := Anc0.step hpc (Anc0.refl _)
      have hcr : c ≠ r := hqr c hpc
      have hrc' : Anc0 M r c := by
        rcases anc0_total hA hcA with h1 | h1
        · exact h1
        · have := h1.le; omega
      have h1c := hpath c hrc' hcA hcr (by omega)
      have hNx : (col (TRIO.gexp M r L d0 0 n) (r + L)).2.1 = entry M 1 r := by
        show entry (TRIO.gexp M r L d0 0 n) 1 (r + L) = entry M 1 r
        exact e1_root hlen hL hA hd0e hn
      have hMx : (col M (r + L)).2.2 = 0 := hx2
      rw [decide_eq_decide]
      constructor
      · intro h; rw [h] at hNx; unfold bump at hNx; simp at hNx; omega
      · intro h; rw [h] at hMx; unfold bump at hMx; simp at hMx


omit hL hA hd0e hn in
/-- The last column of `M` (row 2 is `0`) is not an upgrade target. -/
theorem isUpg_M_x (hx2 : entry M 2 (r + L) = 0) : isUpg M (r + L) = false := by
  unfold isUpg
  rw [Bool.eq_false_iff]
  intro h
  rw [List.any_eq_true] at h
  obtain ⟨k, hk, hkk⟩ := h
  have hk' := List.mem_range.mp hk
  have hu : upg M k = some (r + L) := of_decide_eq_true hkk
  have hle := upg_le hu
  unfold upg at hu
  split at hu
  · cases hu
  · rename_i hc
    split at hu
    · cases hu
    · rename_i m hm
      simp only at hu
      split at hu
      · rename_i hcl
        have hk1 : k + 1 = r + L := Option.some.inj hu
        have : (col M (k + 1)).2.2 = entry M 2 (k + 1) := rfl
        rw [hcl.2] at this; simp at this
        rw [hk1] at this
        omega
      · rw [upgClimb_find] at hu
        have := mem_ancL_lt (List.mem_of_find?_eq_some hu)
        have : k + 1 ≠ M.length := fun h => hc (Or.inr (Or.inr h))
        omega

omit hL hA hd0e hn in
/-- Below `x`, the reads of `v` (parent and upgrade) are below `x`. -/
theorem reads_lt_x (hx2 : entry M 2 (r + L) = 0) {i m : Nat} (hi : i < r + L)
    (h : par M 1 i = some m ∨ (entry M 2 i = 0 ∧ upg M i = some m)) : m < r + L := by
  rcases h with h | ⟨_, h⟩
  · have := par_lt M 1 i m h; omega
  · have hle := upg_le h
    rcases Nat.lt_or_ge m (r + L) with h1 | h1
    · exact h1
    · exfalso
      have hm : m = r + L := by omega
      subst hm
      have := isUpg_M_x hlen hx2
      unfold isUpg at this
      rw [Bool.eq_false_iff] at this
      apply this
      rw [List.any_eq_true]
      exact ⟨i, List.mem_range.mpr (by omega), decide_eq_true h⟩

/-- **The columns before `x` have the same structure**, given that being an upgrade target agrees. -/
theorem sameAt_lt (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hqr : ∀ q, par M 0 (r + L) = some q → q ≠ r)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false) :
    ∀ i, i < r + L → SameAt M (TRIO.gexp M r L d0 0 n) i := by
  intro i hi
  have hb : bump (TRIO.gexp M r L d0 0 n) i = bump M i := by
    unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hi, entry_gexp_pre hlen (by omega) 1 hi]
  have hcx : ∀ c ∈ children M i, c ≤ r + L := by
    intro c hc; have := (mem_children hc).2; omega
  -- the child `x` (if any): counted in both, no bump term
  have hxN : ∀ c ∈ children M i, c = r + L →
      col (TRIO.gexp M r L d0 0 n) c ≠ bump (TRIO.gexp M r L d0 0 n) i ∧ col M c ≠ bump M i := by
    intro c hc hcx'
    subst hcx'
    have hpc := (mem_children_iff.mp hc).2
    have hcr : i ≠ r := hqr i hpc
    have hcA : Anc0 M i (r + L) := Anc0.step hpc (Anc0.refl _)
    have hri := q_ge_r hlen hL hA hd0e hn hpc
    have hrc' : Anc0 M r i := by
      rcases anc0_total hA hcA with h1 | h1
      · exact h1
      · have := h1.le; omega
    have h1c := hpath i hrc' hcA hcr (by omega)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have : (col (TRIO.gexp M r L d0 0 n) (r + L)).2.1 = entry M 1 r := by
        show entry (TRIO.gexp M r L d0 0 n) 1 (r + L) = entry M 1 r
        exact e1_root hlen hL hA hd0e hn
      rw [h] at this; unfold bump at this; simp at this
      rw [entry_gexp_pre hlen (by omega) 1 hi] at this; omega
    · have : (col M (r + L)).2.2 = 0 := hx2
      rw [h] at this; unfold bump at this; simp at this
  refine ⟨entry_gexp_pre hlen (by omega) 1 hi, entry_gexp_pre hlen (by omega) 2 hi,
    par_gexp_pre hlen (by omega) 1 hi, ?_, children_N_lt hlen hL hA hd0e hn hi, ?_, ?_⟩
  · rcases Nat.lt_or_ge (i + 1) (r + L) with h | h
    · exact upg_N_lt hlen hL hd0e hn h
    · rw [show i = r + L - 1 by omega]; exact upg_N_xm1 hlen hL hA hd0e hn hpath hx2
  · intro c hc ρ
    rcases Nat.lt_or_ge c (r + L) with h | h
    · unfold cnt
      rw [col_gexp_pre hlen (by omega) h, hb, hiu c h,
        topped_N_lt hlen hL hA hd0e hn hpath hx2 hqr h]
    · have hcx' : c = r + L := by have := hcx c hc; omega
      obtain ⟨h1, h2⟩ := hxN c hc hcx'
      subst hcx'
      unfold cnt
      rw [if_neg h1, if_neg h2, hiux, isUpg_M_x hlen hx2]
      simp
  · intro c hc ρ
    rcases Nat.lt_or_ge c (r + L) with h | h
    · unfold bumpTerm
      rw [col_gexp_pre hlen (by omega) h, hb, children_N_lt hlen hL hA hd0e hn h]
    · have hcx' : c = r + L := by have := hcx c hc; omega
      obtain ⟨h1, h2⟩ := hxN c hc hcx'
      unfold bumpTerm
      rw [if_neg h1, if_neg h2]

end

end Ytosk
