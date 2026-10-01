/-
**3 行の構造の補題 (2)**: 上げの行き先（hiu・hiux）。

N = M[n] の上げの行き先が x より前なら、M にも同じ行き先への上げがある（`upg_refl`、n の帰納法）。
これで x より前の列が上げられるかは M と N で同じ（`hiu_t1`）、x は N で上げられない（`hiux_t1`）。
-/
import Ytosk.V3Struct1

namespace Ytosk

open T

theorem upg_ge_len {M : Mat} {k : Nat} (hk : M.length ≤ k) : upg M k = none := by
  unfold upg
  have : entry M 1 k = 0 := by
    unfold entry
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]; rfl
  rw [if_pos (Or.inl this)]

theorem upg_lt_len {M : Mat} {k c : Nat} (h : upg M k = some c) : k + 1 < M.length := by
  by_contra hk
  by_cases hk' : k + 1 = M.length
  · unfold upg at h; rw [if_pos (Or.inr (Or.inr hk'))] at h; cases h
  · rw [upg_ge_len (by omega)] at h; cases h

section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

omit hL hA hd0e in
theorem gexp_one_eq : TRIO.gexp M r L d0 0 1 = M.take (r + L) := by
  have hl : (TRIO.gexp M r L d0 0 1).length = r + 1 * L := TRIO.gexp_length hlen
  rw [← gexp_take_x (d0 := d0) (d1 := 0) hlen (le_refl 1), List.take_of_length_le (by omega)]

/-- **Upgrade targets before `x` come from `M`.** -/
theorem upg_refl (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0) (hz2 : entry M 2 r ≤ 1) :
    ∀ n, 1 ≤ n → ∀ k c, upg (TRIO.gexp M r L d0 0 n) k = some c → c < r + L →
      ∃ k', upg M k' = some c := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro k c h _
    rw [gexp_one_eq hlen] at h
    have hk := upg_lt_len h
    rw [List.length_take] at hk
    exact ⟨k, by rw [← upg_take M (show k + 1 < r + L by omega)]; exact h⟩
  | succ n hn ih =>
    intro k c h hc
    have hn2 : 2 ≤ n + 1 := by omega
    have hlN := len_N (d0 := d0) (n := n + 1) hlen hn2
    have hk := upg_lt_len h
    rcases Nat.lt_or_ge (k + 1) (r + L) with h1 | h1
    · exact ⟨k, by rw [← upg_N_lt hlen hL hd0e hn2 h1]; exact h⟩
    rcases Nat.eq_or_lt_of_le h1 with h2 | h2
    · have hkx : k = r + L - 1 := by omega
      subst hkx
      exact ⟨_, by rw [← upg_N_xm1 hlen hL hA hd0e hn2 hpath hx2]; exact h⟩
    rcases Nat.eq_or_lt_of_le (show r + L ≤ k by omega) with h3 | h3
    · subst h3
      rw [upg_root hlen hL hA hd0e hn2 hpath hz2] at h
      exact ih r c (by simpa using h) hc
    · have hj := upg_copy hlen hL hA hd0e hn2 hpath (j := k - (r + L)) (by omega) (by rw [hlN] at hk; omega)
      rw [show r + L + (k - (r + L)) = k by omega, h] at hj
      cases ht : upg (TRIO.gexp M r L d0 0 (n + 1 - 1)) (r + (k - (r + L))) with
      | none => rw [ht] at hj; cases hj
      | some t =>
        rw [ht] at hj
        simp only [Option.map_some] at hj
        have hct := Option.some.inj hj
        by_cases hrt : r < t
        · rw [if_pos hrt] at hct; omega
        · rw [if_neg hrt] at hct
          subst hct
          exact ih _ _ (by simpa using ht) hc

/-- **`hiu`**: before `x`, being upgraded is the same in `M` and `N`. -/
theorem hiu_t1 (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0) (hz2 : entry M 2 r ≤ 1)
    {n : Nat} (hn : 2 ≤ n) :
    ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c := by
  intro c hc
  have hlN := len_N (d0 := d0) (n := n) hlen hn
  unfold isUpg
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨k, _, hkk⟩
    obtain ⟨k', hk'⟩ := upg_refl hlen hL hA hd0e hpath hx2 hz2 n (by omega) k c
      (of_decide_eq_true hkk) hc
    exact ⟨k', List.mem_range.mpr (by have := upg_lt_len hk'; omega), decide_eq_true hk'⟩
  · rintro ⟨k, _, hkk⟩
    have hu : upg M k = some c := of_decide_eq_true hkk
    have hk := upg_lt_len hu
    refine ⟨k, List.mem_range.mpr (by omega), decide_eq_true ?_⟩
    rcases Nat.lt_or_ge (k + 1) (r + L) with h1 | h1
    · rw [upg_N_lt hlen hL hd0e hn h1]; exact hu
    · have hkx : k = r + L - 1 := by omega
      subst hkx
      rw [upg_N_xm1 hlen hL hA hd0e hn hpath hx2]; exact hu

/-- **`hiux`**: `x` is not upgraded in `N`. -/
theorem hiux_t1 (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0) (hz2 : entry M 2 r ≤ 1)
    {n : Nat} (hn : 2 ≤ n) : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false := by
  have hlN := len_N (d0 := d0) (n := n) hlen hn
  have hMx : isUpg M (r + L) = false := isUpg_M_x hlen hx2
  unfold isUpg at hMx ⊢
  rw [Bool.eq_false_iff] at hMx ⊢
  intro h
  rw [List.any_eq_true] at h
  obtain ⟨k, _, hkk⟩ := h
  have hu : upg (TRIO.gexp M r L d0 0 n) k = some (r + L) := of_decide_eq_true hkk
  have hk := upg_lt_len hu
  apply hMx
  rw [List.any_eq_true]
  rcases Nat.lt_or_ge (k + 1) (r + L) with h1 | h1
  · rw [upg_N_lt hlen hL hd0e hn h1] at hu
    exact ⟨k, List.mem_range.mpr (by omega), decide_eq_true hu⟩
  rcases Nat.eq_or_lt_of_le h1 with h2 | h2
  · have hkx : k = r + L - 1 := by omega
    subst hkx
    rw [upg_N_xm1 hlen hL hA hd0e hn hpath hx2] at hu
    exact ⟨_, List.mem_range.mpr (by omega), decide_eq_true hu⟩
  exfalso
  rcases Nat.eq_or_lt_of_le (show r + L ≤ k by omega) with h3 | h3
  · subst h3
    rw [upg_root hlen hL hA hd0e hn hpath hz2] at hu
    have := upgP_root_lt hlen hL hA hd0e hn hu
    omega
  · have hj := upg_copy hlen hL hA hd0e hn hpath (j := k - (r + L)) (by omega)
      (by rw [hlN] at hk; omega)
    rw [show r + L + (k - (r + L)) = k by omega, hu] at hj
    cases ht : upg (TRIO.gexp M r L d0 0 (n - 1)) (r + (k - (r + L))) with
    | none => rw [ht] at hj; cases hj
    | some t =>
      rw [ht] at hj
      simp only [Option.map_some] at hj
      have hct := Option.some.inj hj
      have htle := upg_le ht
      by_cases hrt : r < t
      · rw [if_pos hrt] at hct
        -- `t + L = r + L` contradicts `r < t`
        omega
      · rw [if_neg hrt] at hct; omega

end

end Ytosk
