/-
**3 行・t = 2・q ≠ r: 展開 N = gexp M r L d0 d1 n の構造（x より前）。**

V3T2S（q = r）の一般化。x の行 0 の親を r + qp（qp < L）、r を x の行 0 の祖先とする。
位置 x のコピーの根 x′ の親は r + qp、それより後ろの列の親は x 以後なので、x より前の列の子の並びは
N と M で同じ（`children_N2Q`）。
-/
import Ytosk.V3T2Q

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L d0 d1 n qp : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hp : par M 0 (r + L) = some (r + qp)) (hqp : qp < L) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 1 ≤ n)
include hlen hL hA hp hqp hd0e hn

omit hp hqp hd0e hn in
/-- The row-0 parent of a column of `B` after `r` is in `B`. -/
theorem par0_BQ {q p : Nat} (hq0 : 0 < q) (hq : q < L) (hpq : par M 0 (r + q) = some p) :
    r ≤ p ∧ p < r + q := by
  have hA : Anc0 M r (r + q) :=
    anc_between hA (r + q) (by omega) (by omega)
  exact ⟨(anc0_par hA (by omega) hpq).le, par_lt M 0 _ _ hpq⟩

/-- **The row-0 parent of a column of `N` at or after `x`**: `r` for `x` itself, else at or after `x`. -/
theorem par0_tail2Q {c : Nat} (hc0 : r + L ≤ c) (hc : c < r + n * L) :
    (c = r + L ∧ par (TRIO.gexp M r L d0 d1 n) 0 c = some (r + qp)) ∨
    (∃ p, par (TRIO.gexp M r L d0 d1 n) 0 c = some p ∧ r + L ≤ p ∧ p < c) := by
  obtain ⟨k, q, hk, hq, rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n) hL (by omega) hc
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    subst this; omega
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · subst hq0
    have := par0_gexp_root (d1 := d1) hlen hk hk1 hqp hd0e hp
    rcases Nat.eq_or_lt_of_le hk1 with hk' | hk'
    · subst hk'
      left
      refine ⟨by simp, ?_⟩
      rw [this]; simp
    · right
      refine ⟨_, this, ?_, ?_⟩
      · have : L ≤ (k - 1) * L := by
          have := Nat.mul_le_mul_right L (show 1 ≤ k - 1 by omega); simpa using this
        omega
      · have : (k - 1) * L + L = k * L := by
          rw [← Nat.succ_mul]; congr 1; omega
        omega
  · obtain ⟨p, hpq⟩ : ∃ p, par M 0 (r + q) = some p := by
      obtain ⟨p, hp'⟩ := par0_of_anc (anc_between hA (r + q) (by omega)
        (by omega)) (by omega)
      exact ⟨p, hp'⟩
    obtain ⟨hrp, hpq'⟩ := par0_BQ hlen hL hA hq0 hq hpq
    have h' : par M 0 (r + q) = some (r + (p - r)) := by rw [show r + (p - r) = p by omega]; exact hpq
    have := par0_gexp_mir (d0 := d0) (d1 := d1) hlen hk hq h'
    right
    refine ⟨_, this, ?_, by omega⟩
    have : L ≤ k * L := by have := Nat.mul_le_mul_right L hk1; simpa using this
    omega

/-- **The children before `x` are those of `M`.** -/
theorem children_N2Q (hn2 : 2 ≤ n) {i : Nat} (hi : i < r + L) :
    children (TRIO.gexp M r L d0 d1 n) i = children M i := by
  have hlN : (TRIO.gexp M r L d0 d1 n).length = r + n * L := TRIO.gexp_length hlen
  have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L hn
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
  apply eq_of_sorted_mem _ _ (children_sorted _ i) (children_sorted M i)
  intro c
  rw [mem_children_iff, mem_children_iff, hlN, ← hlen]
  constructor
  · rintro ⟨hc, hpc⟩
    rcases Nat.lt_or_ge c (r + L) with h | h
    · rw [par_gexp_pre hlen hn 0 h] at hpc; exact ⟨by omega, hpc⟩
    · rcases par0_tail2Q hlen hL hA hp hqp hd0e hn h hc with ⟨hcx, hpk⟩ | ⟨p', hp', hp'1, _⟩
      · rw [hpc] at hpk; cases hpk; rw [hcx]; exact ⟨by omega, hp⟩
      · rw [hpc] at hp'; cases hp'; omega
  · rintro ⟨hc, hpc⟩
    rcases Nat.lt_or_ge c (r + L) with h | h
    · rw [par_gexp_pre hlen hn 0 h]; exact ⟨by omega, hpc⟩
    · have : c = r + L := by omega
      subst this
      rw [hp] at hpc; cases hpc
      rcases par0_tail2Q hlen hL hA hp hqp hd0e hn (le_refl _) (by omega) with ⟨_, hpk⟩ | ⟨p', hp', hp'1, hp'2⟩
      · exact ⟨by omega, hpk⟩
      · omega

/-- Row 2 of the copy root `x′` (at position `x`) is that of `r`, and row 0 is that of `x`. -/
theorem entry_xprimeQ (hn2 : 2 ≤ n) :
    entry (TRIO.gexp M r L d0 d1 n) 2 (r + L) = entry M 2 r ∧
      entry (TRIO.gexp M r L d0 d1 n) 0 (r + L) = entry M 0 (r + L) := by
  have h := TRIO.gexp_getD_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := d1) (n := n)
    (k := 1) (q := 0) hlen (by omega) hL
  rw [show r + (1 * L + 0) = r + L by omega, Nat.add_zero] at h
  constructor
  · unfold entry; rw [h]; rfl
  · have h0 : entry (TRIO.gexp M r L d0 d1 n) 0 (r + L) = entry M 0 r + 1 * d0 := by
      unfold entry; rw [h]; rfl
    rw [h0, hd0e]; omega

/-- **The upgrade of `x − 1`** is that of `M` unless `M` upgrades `x − 1` to `x` (`x′` has row 2 zero). -/
theorem upg_N2_xm1Q (hn2 : 2 ≤ n) (he2r : entry M 2 r = 0) (hnu : upg M (r + L - 1) ≠ some (r + L)) :
    upg (TRIO.gexp M r L d0 d1 n) (r + L - 1) = upg M (r + L - 1) := by
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
  set i := r + L - 1 with hi
  have hix : i + 1 = r + L := by omega
  obtain ⟨hx2', hx0'⟩ := entry_xprimeQ hlen hL hA hp hqp hd0e hn hn2
  have hpre : ∀ y j, j < r + L → entry N y j = entry M y j := fun y j hj => entry_gexp_pre hlen hn y hj
  have hparpre : ∀ k j, j < r + L → par N k j = par M k j := fun k j hj => par_gexp_pre hlen hn k hj
  have hcolpre : ∀ j, j < r + L → col N j = col M j := fun j hj => col_gexp_pre hlen hn hj
  unfold upg
  rw [hpre 1 i (by omega), hpre 2 i (by omega), hparpre 1 i (by omega)]
  have hlenN : ¬ i + 1 = N.length := by omega
  have hlenM : ¬ i + 1 = M.length := by omega
  by_cases h : entry M 1 i = 0 ∨ entry M 2 i = 1
  · rw [if_pos (by rcases h with h | h; exact Or.inl h; exact Or.inr (Or.inl h)),
      if_pos (by rcases h with h | h; exact Or.inl h; exact Or.inr (Or.inl h))]
  · rw [if_neg (by rintro (h' | h' | h'); exact h (Or.inl h'); exact h (Or.inr h'); exact hlenN h'),
      if_neg (by rintro (h' | h' | h'); exact h (Or.inl h'); exact h (Or.inr h'); exact hlenM h')]
    split
    · rfl
    · rename_i m hm
      have hmi := par_lt M 1 i m hm
      simp only
      -- the first test fails in both
      have hN1 : ¬ (par N 1 (i + 1) = some m ∧ col N (i + 1) =
          (entry N 0 m + 1, entry M 1 i, entry N 2 m + 1)) := by
        rintro ⟨_, hc⟩
        have : entry N 2 (i + 1) = (col N (i + 1)).2.2 := rfl
        rw [hc] at this; simp at this; rw [hix, hx2', he2r] at this; omega
      have hM1 : ¬ (par M 1 (i + 1) = some m ∧ col M (i + 1) =
          (entry M 0 m + 1, entry M 1 i, entry M 2 m + 1)) := by
        intro hh
        apply hnu
        unfold upg
        rw [if_neg (by rintro (h' | h' | h'); exact h (Or.inl h'); exact h (Or.inr h'); exact hlenM h'),
          hm]
        simp only
        rw [if_pos hh, hix]
      rw [if_neg hN1, if_neg hM1, hpre 0 m (by omega), hpre 2 m (by omega), hparpre 0 i (by omega)]
      apply climb_congr (i + 1)
      · intro q hq; exact hparpre 0 q (by omega)
      · intro q hq
        rw [hparpre 1 q (by omega), hcolpre q (by omega), hpre 0 q (by omega), hix, hx0']
      · exact par_lt N 0
      · intro q h'; have := par_lt M 0 i q h'; omega

end

end Ytosk
