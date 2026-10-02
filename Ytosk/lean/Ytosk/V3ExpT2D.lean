/-
**3 行・t = 2: N = M[n] の x より前の構造（一般の q = P_0(x)）と、写しの列ののりしろ・topped・上げられる。**

x より前: 列・親・子は M と同じ（`children_N2g`）。上げは x − 1 だけが変わりうる（M で x へ上げるなら N では
どこへも上げない、x の写し x′ の行 2 は 0 なので）（`upg_N2g`）。
-/
import Ytosk.V3ExpT2C
import Ytosk.V3T2Top

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L q d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hq : par M 0 (r + L) = some q)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hq hd0e hn

theorem q_ge_r2 : r ≤ q := (anc0_par hA (by omega) hq).le

/-- **The row-0 parent of a column of `N` at or after `x`**: `q` for `x` itself, else at or after `x`. -/
theorem par0_tail2g {c : Nat} (hc0 : r + L ≤ c) (hc : c < r + n * L) :
    (c = r + L ∧ par (TRIO.gexp M r L d0 d1 n) 0 c = some q) ∨
    (∃ p, par (TRIO.gexp M r L d0 d1 n) 0 c = some p ∧ r + L ≤ p ∧ p < c) := by
  have hqr := q_ge_r2 hlen hL hA hq hd0e hn
  have hqx := par_lt M 0 _ _ hq
  obtain ⟨k, q', hk, hq', rfl⟩ := TRIO.gexp_pos_decomp (j0 := r) (Lb := L) (n := n) hL (by omega) hc
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    subst this; omega
  rcases Nat.eq_zero_or_pos q' with hq0 | hq0
  · subst hq0
    have h0 : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
    have := par0_gexp_root (d1 := d1) hlen hk hk1 (show q - r < L by omega) hd0e h0
    rcases Nat.eq_or_lt_of_le hk1 with hk' | hk'
    · subst hk'
      left
      refine ⟨by simp, ?_⟩
      rw [this]; simp; omega
    · right
      refine ⟨_, this, ?_, ?_⟩
      · have : L ≤ (k - 1) * L := by
          have := Nat.mul_le_mul_right L (show 1 ≤ k - 1 by omega); simpa using this
        omega
      · have : (k - 1) * L + L ≤ k * L := by
          rw [← Nat.succ_mul, show (k - 1).succ = k by omega]
        omega
  · obtain ⟨p, hpq⟩ := par0_of_anc (anc_between hA (r + q') (by omega) (by omega)) (by omega)
    have hrp : r ≤ p := (anc0_par (anc_between hA (r + q') (by omega) (by omega)) (by omega) hpq).le
    have hpq' := par_lt M 0 _ _ hpq
    have h' : par M 0 (r + q') = some (r + (p - r)) := by rw [show r + (p - r) = p by omega]; exact hpq
    have := par0_gexp_mir (d0 := d0) (d1 := d1) hlen hk hq' h'
    right
    refine ⟨_, this, ?_, by omega⟩
    have : L ≤ k * L := by have := Nat.mul_le_mul_right L hk1; simpa using this
    omega

/-- **The children before `x` are those of `M`** (general `q`). -/
theorem children_N2g {i : Nat} (hi : i < r + L) :
    children (TRIO.gexp M r L d0 d1 n) i = children M i := by
  have hlN : (TRIO.gexp M r L d0 d1 n).length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hm1 : 1 ≤ n := by omega
  apply eq_of_sorted_mem _ _ (children_sorted _ i) (children_sorted M i)
  intro c
  rw [mem_children_iff, mem_children_iff, hlN, ← hlen]
  constructor
  · rintro ⟨hc, hpc⟩
    rcases Nat.lt_or_ge c (r + L) with h | h
    · rw [par_gexp_pre hlen hm1 0 h] at hpc; exact ⟨by omega, hpc⟩
    · rcases par0_tail2g hlen hL hA hq hd0e hn h hc with ⟨hcx, hpk⟩ | ⟨p', hp', hp'1, _⟩
      · rw [hpc] at hpk; cases hpk; rw [hcx]; exact ⟨by omega, hq⟩
      · rw [hpc] at hp'; cases hp'; omega
  · rintro ⟨hc, hpc⟩
    rcases Nat.lt_or_ge c (r + L) with h | h
    · rw [par_gexp_pre hlen hm1 0 h]; exact ⟨by omega, hpc⟩
    · have : c = r + L := by omega
      subst this
      rw [hq] at hpc; cases hpc
      rcases par0_tail2g (d1 := d1) hlen hL hA hq hd0e hn (le_refl _) (by omega) with
        ⟨_, hpk⟩ | ⟨p', hp', hp'1, hp'2⟩
      · exact ⟨by omega, hpk⟩
      · omega

/-- Row 2 of the copy root at `x` is that of `r`; row 0 is that of `x`. -/
theorem entry_xprime_g :
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

/-- **Upgrades before `x`**: those of `M`, except that `x − 1` may lose its upgrade to `x`. -/
theorem upg_N2g (he2r : entry M 2 r = 0) {i k : Nat} (hi : i < r + L)
    (h : upg (TRIO.gexp M r L d0 d1 n) i = some k) : k < r + L ∧ upg M i = some k := by
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hm1 : 1 ≤ n := by omega
  rcases Nat.lt_or_ge (i + 1) (r + L) with hi1 | hi1
  · have he : upg N i = upg M i := by
      rw [← upg_take _ hi1, hN, gexp_take_x hlen hm1, upg_take M hi1]
    rw [he] at h
    refine ⟨?_, h⟩
    have := upg_le h; omega
  · have hix : i + 1 = r + L := by omega
    obtain ⟨hx2', hx0'⟩ := entry_xprime_g (d1 := d1) hlen hL hA hq hd0e hn
    have hpre : ∀ y j, j < r + L → entry N y j = entry M y j := fun y j hj => entry_gexp_pre hlen hm1 y hj
    have hparpre : ∀ k j, j < r + L → par N k j = par M k j := fun k j hj => par_gexp_pre hlen hm1 k hj
    have hcolpre : ∀ j, j < r + L → col N j = col M j := fun j hj => col_gexp_pre hlen hm1 hj
    have hlenN : ¬ i + 1 = N.length := by omega
    have hlenM : ¬ i + 1 = M.length := by omega
    unfold upg at h ⊢
    rw [hpre 1 i (by omega), hpre 2 i (by omega), hparpre 1 i (by omega)] at h
    by_cases hc : entry M 1 i = 0 ∨ entry M 2 i = 1
    · rw [if_pos (by rcases hc with h' | h'; exact Or.inl h'; exact Or.inr (Or.inl h'))] at h; cases h
    · rw [if_neg (by rintro (h' | h' | h'); exact hc (Or.inl h'); exact hc (Or.inr h'); exact hlenN h')] at h
      rw [if_neg (by rintro (h' | h' | h'); exact hc (Or.inl h'); exact hc (Or.inr h'); exact hlenM h')]
      cases hm : par M 1 i with
      | none => rw [hm] at h; cases h
      | some m =>
        rw [hm] at h
        simp only at h ⊢
        have hmi := par_lt M 1 i m hm
        -- the first test fails in `N`
        have hN1 : ¬ (par N 1 (i + 1) = some m ∧ col N (i + 1) =
            (entry N 0 m + 1, entry M 1 i, entry N 2 m + 1)) := by
          rintro ⟨_, hc'⟩
          have : entry N 2 (i + 1) = (col N (i + 1)).2.2 := rfl
          rw [hc'] at this; simp at this; rw [hix, hx2', he2r] at this; omega
        rw [if_neg hN1, hpre 0 m (by omega), hpre 2 m (by omega)] at h
        -- the climb is the same
        have hcl : climb (par N 0)
            (fun q => decide (par N 1 q = some m ∧
              col N q = (entry M 0 m + 1, entry M 1 i, entry M 2 m + 1) ∧ entry N 0 q < entry N 0 (i + 1)))
            (i + 1) (par N 0 i) =
          climb (par M 0)
            (fun q => decide (par M 1 q = some m ∧
              col M q = (entry M 0 m + 1, entry M 1 i, entry M 2 m + 1) ∧ entry M 0 q < entry M 0 (i + 1)))
            (i + 1) (par M 0 i) := by
          rw [hparpre 0 i (by omega)]
          apply climb_congr (i + 1)
          · intro q' hq'; exact hparpre 0 q' (by omega)
          · intro q' hq'
            rw [hparpre 1 q' (by omega), hcolpre q' (by omega), hpre 0 q' (by omega), hix, hx0']
          · exact par_lt N 0
          · intro q' h'; have := par_lt M 0 _ q' h'; omega
        rw [hcl] at h
        by_cases hM1 : par M 1 (i + 1) = some m ∧ col M (i + 1) =
            (entry M 0 m + 1, entry M 1 i, entry M 2 m + 1)
        · -- `M` upgrades `x − 1` to `x`: the climb in `N` finds nothing
          exfalso
          rw [upgClimb_find] at h
          have hk := List.find?_some h
          simp only [decide_eq_true_eq] at hk
          obtain ⟨_, hk2, hk3⟩ := hk
          have h0 : entry M 0 k = entry M 0 m + 1 := by
            have : entry M 0 k = (col M k).1 := rfl; rw [this, hk2]
          have h0' : entry M 0 (i + 1) = entry M 0 m + 1 := by
            have : entry M 0 (i + 1) = (col M (i + 1)).1 := rfl; rw [this, hM1.2]
          omega
        · rw [if_neg hM1]
          refine ⟨?_, h⟩
          rw [upgClimb_find] at h
          have := mem_ancL_lt (List.mem_of_find?_eq_some h); omega


/-- **`topped` before `x`**, except at `q` (whose last child `x` changes). -/
theorem topped_N2g {c : Nat} (hc : c < r + L) (hcq : c ≠ q) :
    topped (TRIO.gexp M r L d0 d1 n) c = topped M c := by
  have hm1 : 1 ≤ n := by omega
  apply topped_eq_of (children_N2g hlen hL hA hq hd0e hn hc)
  · intro d hd
    have hdx : d < r + L := by
      have := (mem_children hd).2
      rcases Nat.lt_or_ge d (r + L) with h | h
      · exact h
      · exfalso
        have hdx : d = r + L := by omega
        rw [hdx] at hd
        have := (mem_children_iff.mp hd).2; rw [hq] at this; cases this; exact hcq rfl
    exact col_gexp_pre hlen hm1 hdx
  · unfold bump; rw [entry_gexp_pre hlen hm1 0 hc, entry_gexp_pre hlen hm1 1 hc]

/-- **The counted children before `x`**: counted in `M`, or the new child `x` of `q`, or (`q ≠ r`) `q`
newly counted at its parent (`q` is no longer topped). -/
theorem counted_N2g (he2r : entry M 2 r = 0) (h1x : entry M 1 r < entry M 1 (r + L))
    (hUM : UAT M) (hUN : UAT (TRIO.gexp M r L d0 d1 n)) {i c : Nat} (hi : i < r + L)
    (hc : c ∈ children (TRIO.gexp M r L d0 d1 n) i) (hcnt : Counted (TRIO.gexp M r L d0 d1 n) i c) :
    Counted M i c ∨ (i = q ∧ c = r + L) ∨ (q ≠ r ∧ c = q ∧ par M 0 q = some i) := by
  have hm1 : 1 ≤ n := by omega
  have hlN : (TRIO.gexp M r L d0 d1 n).length = r + n * L := TRIO.gexp_length hlen
  have hcM : c ∈ children M i := by rw [← children_N2g hlen hL hA hq hd0e hn hi]; exact hc
  have hcl := mem_children hcM
  rcases Nat.lt_or_ge c (r + L) with hcx | hcx
  · have hcol : col (TRIO.gexp M r L d0 d1 n) c = col M c := col_gexp_pre hlen hm1 hcx
    have hb : bump (TRIO.gexp M r L d0 d1 n) i = bump M i := by
      unfold bump; rw [entry_gexp_pre hlen hm1 0 hi, entry_gexp_pre hlen hm1 1 hi]
    obtain ⟨hcb, hcu⟩ := hcnt
    rw [hcol, hb] at hcb
    by_cases hcq : c = q
    · by_cases hqr : q = r
      · -- `q = r`: `r` is topped in neither
        left
        refine ⟨hcb, fun ⟨_, ht⟩ => ?_⟩
        have hlast : (children M c).getLast? = some (r + L) := by
          apply getLast_of (children_sorted M c) (mem_children_iff.mpr ⟨by omega, by rw [hcq]; exact hq⟩)
          intro e he; have := (mem_children he).2; omega
        unfold topped at ht
        rw [hlast] at ht
        simp only [decide_eq_true_eq] at ht
        have := (bump_eq ht).2.1
        rw [col_eq_entries] at this; simp only at this
        rw [hcq, hqr] at this; omega
      · right; right
        refine ⟨hqr, hcq, ?_⟩
        rw [← hcq]; exact (mem_children_iff.mp hcM).2
    · left
      refine ⟨hcb, fun ⟨hu, ht⟩ => hcu ⟨?_, ?_⟩⟩
      · have hnL : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
        rw [isUpg_topped_take (M := M) (N := TRIO.gexp M r L d0 d1 n) (x := r + L) (by omega)
          (by rw [hlN]; omega) (gexp_take_x hlen hm1) hUM hUN hcx
          (by rw [topped_N2g hlen hL hA hq hd0e hn hcx hcq]; exact ht) ht]
        exact hu
      · rw [topped_N2g hlen hL hA hq hd0e hn hcx hcq]; exact ht
  · right; left
    have hcx' : c = r + L := by omega
    refine ⟨?_, hcx'⟩
    have := (mem_children_iff.mp hcM).2; rw [hcx', hq] at this; cases this; rfl

/-- **The bump children before `x`** are those of `M`, and their children are before `x`. -/
theorem bmp_N2g (he2r : entry M 2 r = 0) (hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i)
    {i j : Nat} (hi : i < r + L) (hj : j ∈ children (TRIO.gexp M r L d0 d1 n) i)
    (hjb : col (TRIO.gexp M r L d0 d1 n) j = bump (TRIO.gexp M r L d0 d1 n) i) :
    col M j = bump M i ∧ ∀ k ∈ children (TRIO.gexp M r L d0 d1 n) j, k < r + L := by
  have hm1 : 1 ≤ n := by omega
  have hjM : j ∈ children M i := by rw [← children_N2g hlen hL hA hq hd0e hn hi]; exact hj
  have hjl := mem_children hjM
  have hb : bump (TRIO.gexp M r L d0 d1 n) i = bump M i := by
    unfold bump; rw [entry_gexp_pre hlen hm1 0 hi, entry_gexp_pre hlen hm1 1 hi]
  have hjx : j < r + L := by
    rcases Nat.lt_or_ge j (r + L) with h | h
    · exact h
    · exfalso
      have hj' : j = r + L := by omega
      have := (bump_eq hjb).2.2
      have h2 : (col (TRIO.gexp M r L d0 d1 n) j).2.2 = entry (TRIO.gexp M r L d0 d1 n) 2 j := rfl
      rw [h2, hj', (entry_xprime_g (d1 := d1) hlen hL hA hq hd0e hn).1, he2r] at this
      omega
  rw [col_gexp_pre hlen hm1 hjx, hb] at hjb
  refine ⟨hjb, fun k hk => ?_⟩
  rw [children_N2g hlen hL hA hq hd0e hn hjx] at hk
  have hkl := mem_children hk
  rcases Nat.lt_or_ge k (r + L) with h | h
  · exact h
  · exfalso
    have hk' : k = r + L := by omega
    have hpk := (mem_children_iff.mp hk).2
    rw [hk', hq] at hpk; cases hpk
    exact hqb i (mem_children_iff.mp hjM).2 hjb

end

end Ytosk
