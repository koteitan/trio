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

/-! ## 写しの列ののりしろ・topped・上げられる・数える -/

/-- A column whose next column is its child upgrades only to an earlier column. -/
theorem upg_lt_of_child {G : Mat} {c t : Nat} (hA : Anc0 G c (c + 1)) (h : upg G c = some t) : t < c := by
  unfold upg at h
  split_ifs at h with h0
  cases hm : par G 1 c with
  | none => rw [hm] at h; cases h
  | some m =>
    rw [hm] at h
    simp only at h
    have hmc := anc0_of_par G 1 m c hm
    have hmc' := par_lt G 1 c m hm
    have h1 := anc0_e0_lt hmc (by omega)
    have h2 := anc0_e0_lt hA (by omega)
    split_ifs at h with h3
    · exfalso
      have : entry G 0 (c + 1) = (col G (c + 1)).1 := rfl
      rw [this, h3.2] at h2
      simp only at h2
      omega
    · rw [upgClimb_find] at h
      exact mem_ancL_lt (List.mem_of_find?_eq_some h)

theorem par1_same_of_eq {G : Mat} {p d m : Nat} (hd : d < G.length) (hpd : par G 0 d = some p)
    (he : entry G 1 d = entry G 1 p) (hm : par G 1 p = some m) : par G 1 d = some m := by
  obtain ⟨hmem, hlt, hmax⟩ := (par1_some_iff G p m).mp hm
  rw [par1_some_iff, ancL_eq hpd, he]
  refine ⟨List.mem_cons_of_mem _ hmem, hlt, fun y hy hmy => ?_⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · exact le_refl _
  · exact hmax y hy hmy

section
variable {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hd0 : 0 < d0) (hd1 : 0 < d1) (hgx : TRIO.le1 M r (r + L)) (he2r : entry M 2 r = 0)
include hlen hL hA hd0e hn hd0 hd1 hgx he2r

/-- **Bump children of a copy column** are the shifted ones. -/
theorem bump_copy2 (hBEP : BumpE2 (TRIO.gexp M r L d0 d1 (n - 1))) {a d : Nat} (ha : a < (n - 1) * L)
    (hd : d ∈ children (TRIO.gexp M r L d0 d1 (n - 1)) (r + a)) :
    col (TRIO.gexp M r L d0 d1 n) (d + L) = bump (TRIO.gexp M r L d0 d1 n) (r + L + a) ↔
      col (TRIO.gexp M r L d0 d1 (n - 1)) d = bump (TRIO.gexp M r L d0 d1 (n - 1)) (r + a) := by
  set P := TRIO.gexp M r L d0 d1 (n - 1) with hP
  have hlP : P.length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hdc := mem_children hd
  have hpd := (mem_children_iff.mp hd).2
  have hda : d - r < (n - 1) * L := by omega
  have hrA := ancP_r (d1 := d1) hlen hL hA hd0e hn hd0 hd1 hgx ha
  have hcd : col (TRIO.gexp M r L d0 d1 n) (d + L) =
      (entry P 0 d + d0, entry P 1 d + (if TRIO.le1 P r d then d1 else 0), entry P 2 d) := by
    rw [show d + L = r + L + (d - r) by omega, col_copy2 hlen hL hA hd0e hn hd0 hd1 hgx hda,
      show r + (d - r) = d by omega]
  have hbN : bump (TRIO.gexp M r L d0 d1 n) (r + L + a) =
      (entry P 0 (r + a) + d0 + 1, entry P 1 (r + a) + (if TRIO.le1 P r (r + a) then d1 else 0), 1) := by
    unfold bump
    rw [e0_copy2 hlen hL hA hd0e hn ha, show r + L + a = (r + a) + L by omega,
      e1_shift2 hlen hL hA hd0e hn hd0 hd1 hgx (by omega) (by omega)]
  rw [hcd, hbN, col_eq_entries P d]
  unfold bump
  simp only [Prod.mk.injEq]
  by_cases hgd : TRIO.le1 P r d <;> by_cases hgp : TRIO.le1 P r (r + a)
  · rw [if_pos hgd, if_pos hgp]; constructor <;> (rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h3⟩)
  · exact absurd (guard_par hrA hpd hdc.2 hgd) hgp
  · rw [if_neg hgd, if_pos hgp]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exfalso; exact hgd (guard_up hrA hpd hdc.2 hgp (by omega))
    · rintro ⟨h1, h2, h3⟩
      exfalso
      by_cases hpr : r + a = r
      · -- a bump child of `r` would give row 2 of `r` equal to `1`
        have hb : col P d = bump P (r + a) := by
          rw [col_eq_entries]; unfold bump; simp only [Prod.mk.injEq]; exact ⟨h1, h2, h3⟩
        have := hBEP _ _ hd hb
        rw [hpr, entry_gexp_pre hlen (show 1 ≤ n - 1 by omega) 2 (by omega), he2r] at this
        omega
      · obtain ⟨m, hm, hgm⟩ := le1_par1_down hgp hpr
        exact hgd (le1_par1_up hgm (par1_same_of_eq hdc.2 hpd h2 hm) hdc.2)
  · rw [if_neg hgd, if_neg hgp]; constructor <;> (rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h3⟩)

/-- **`topped` of a copy column** is the shifted one. -/
theorem topped_copy2 (hBEP : BumpE2 (TRIO.gexp M r L d0 d1 (n - 1))) {a : Nat} (ha : a < (n - 1) * L) :
    topped (TRIO.gexp M r L d0 d1 n) (r + L + a) = topped (TRIO.gexp M r L d0 d1 (n - 1)) (r + a) := by
  unfold topped
  rw [children_shift2 hlen hL hA hd0e hn ha, List.getLast?_map]
  cases h : (children (TRIO.gexp M r L d0 d1 (n - 1)) (r + a)).getLast? with
  | none => rfl
  | some c =>
    simp only [Option.map_some]
    have hc := List.mem_of_getLast? h
    rw [decide_eq_decide]
    exact bump_copy2 hlen hL hA hd0e hn hd0 hd1 hgx he2r hBEP ha hc

/-- **The copy root upgrades only to a column before `x`.** -/
theorem upg_rootN {t : Nat} (h : upg (TRIO.gexp M r L d0 d1 n) (r + L) = some t) : t < r + L := by
  have hlN : (TRIO.gexp M r L d0 d1 n).length = r + L + (n - 1) * L := by
    rw [TRIO.gexp_length hlen]
    have : n * L = (n - 1) * L + L := by rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
    omega
  rcases Nat.lt_or_ge 1 ((n - 1) * L) with h1 | h1
  · obtain ⟨S, -, hSN, -⟩ := ancL_copy2 (d1 := d1) hlen hL hA hd0e hn 1 (by omega) h1
    have hA1 : Anc0 (TRIO.gexp M r L d0 d1 n) (r + L) (r + L + 1) :=
      anc0_of_mem_ancL (by rw [hSN]; simp)
    exact upg_lt_of_child hA1 h
  · have := upg_lt_len h; omega

/-- **`r` in `P` upgrades only to an earlier column.** -/
theorem upgP_r {t : Nat} (h : upg (TRIO.gexp M r L d0 d1 (n - 1)) r = some t) : t < r := by
  have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
  rcases Nat.lt_or_ge 1 ((n - 1) * L) with h1 | h1
  · exact upg_lt_of_child (ancP_r (d1 := d1) hlen hL hA hd0e hn hd0 hd1 hgx h1) h
  · have := upg_lt_len h; omega

/-- **Being an upgrade target** of a copy column is the shifted one. -/
theorem isUpg_copy2 {d : Nat} (hrd : r < d) (hd : d < r + (n - 1) * L) :
    isUpg (TRIO.gexp M r L d0 d1 n) (d + L) = isUpg (TRIO.gexp M r L d0 d1 (n - 1)) d := by
  have hlN : (TRIO.gexp M r L d0 d1 n).length = r + L + (n - 1) * L := by
    rw [TRIO.gexp_length hlen]
    have : n * L = (n - 1) * L + L := by rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
    omega
  have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
  apply Bool.eq_iff_iff.mpr
  unfold isUpg
  simp only [List.any_eq_true, decide_eq_true_eq, List.mem_range]
  constructor
  · rintro ⟨k, hk, hu⟩
    rcases Nat.lt_or_ge k (r + L) with hkx | hkx
    · have := upg_le hu; omega
    · rcases Nat.eq_or_lt_of_le hkx with hkx | hkx
      · rw [← hkx] at hu; have := upg_rootN hlen hL hA hd0e hn hd0 hd1 hgx he2r hu; omega
      · have hu' := hu
        rw [show k = r + L + (k - (r + L)) by omega,
          upg_copy2 hlen hL hA hd0e hn hd0 hd1 hgx he2r (by omega) (by omega)] at hu'
        cases ht : upg (TRIO.gexp M r L d0 d1 (n - 1)) (r + (k - (r + L))) with
        | none => rw [ht] at hu'; cases hu'
        | some t =>
          rw [ht] at hu'
          simp only [Option.map_some, Option.some.injEq] at hu'
          refine ⟨r + (k - (r + L)), by omega, ?_⟩
          rw [ht]
          split_ifs at hu' with htr
          · congr 1; omega
          · omega
  · rintro ⟨k, hk, hu⟩
    rcases Nat.lt_or_ge k r with hkr | hkr
    · have := upg_le hu; omega
    · rcases Nat.eq_or_lt_of_le hkr with hkr | hkr
      · rw [← hkr] at hu; have := upgP_r hlen hL hA hd0e hn hd0 hd1 hgx he2r hu; omega
      · refine ⟨r + L + (k - r), by omega, ?_⟩
        rw [upg_copy2 hlen hL hA hd0e hn hd0 hd1 hgx he2r (by omega) (by omega),
          show r + (k - r) = k by omega, hu]
        simp; omega

/-- **Counted children of a copy column** are the shifted ones. -/
theorem counted_copy2 (hBEP : BumpE2 (TRIO.gexp M r L d0 d1 (n - 1))) {a d : Nat} (ha : a < (n - 1) * L)
    (hd : d ∈ children (TRIO.gexp M r L d0 d1 (n - 1)) (r + a)) :
    Counted (TRIO.gexp M r L d0 d1 n) (r + L + a) (d + L) ↔
      Counted (TRIO.gexp M r L d0 d1 (n - 1)) (r + a) d := by
  have hlP : (TRIO.gexp M r L d0 d1 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
  have hdc := mem_children hd
  unfold Counted
  rw [ne_eq, ne_eq, bump_copy2 hlen hL hA hd0e hn hd0 hd1 hgx he2r hBEP ha hd,
    isUpg_copy2 hlen hL hA hd0e hn hd0 hd1 hgx he2r (by omega) (by omega),
    show d + L = r + L + (d - r) by omega,
    topped_copy2 hlen hL hA hd0e hn hd0 hd1 hgx he2r hBEP (show d - r < (n - 1) * L by omega),
    show r + (d - r) = d by omega]

end

end Ytosk
