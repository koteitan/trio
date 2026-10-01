/-
**コピーのずらし（2 行・t = 1）。**

M[n] の列 x + p の値は M[n−1] の列 r + p の値に等しい（p < (n−1)·L、L = x − r）。
コピーの行 1 は上がらない（d1 = 0）ので行 1 は同じ、行 0 の親はコピーの番号を 1 つずらして対応する。
-/
import Ytosk.TwoRowP

namespace Ytosk

open T

/-- Children as a filtered range above a base. -/
theorem children_above (N : Mat) (base K h : Nat) (hlen : N.length = base + K)
    (hlow : ∀ c, c < base → par N 0 c ≠ some h) :
    children N h = ((List.range K).filter (fun j => decide (par N 0 (base + j) = some h))).map
      (base + ·) := by
  unfold children
  rw [hlen, List.range_add, List.filter_append]
  have h1 : (List.range base).filter (fun i => decide (par N 0 i = some h)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc; have := hlow c (List.mem_range.mp hc); simpa using this
  rw [h1, List.nil_append, List.filter_map]
  rfl

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- **Row-0 parents shift by one copy.** -/
theorem par0_gexp_shift {j : Nat} (hj0 : 0 < j) (hj : j < (n - 1) * L) :
    par (TRIO.gexp M r L d0 0 n) 0 (r + L + j) =
      (par (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + j)).map (· + L) := by
  obtain ⟨k, qb, hk, hqb, hjk⟩ := TRIO.gexp_pos_decomp (j0 := 0) (n := n - 1) (p := j) hL (Nat.zero_le _)
    (by simpa using hj)
  simp only [Nat.zero_add] at hjk
  subst hjk
  have hidx1 : r + L + (k * L + qb) = r + ((k + 1) * L + qb) := by rw [Nat.succ_mul]; omega
  rcases Nat.eq_zero_or_pos qb with hq0 | hq0
  · subst hq0
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp at hj0
      · exact h
    obtain ⟨q, hq⟩ := par0_some_of (show r < r + L by omega)
      (anc0_interval hA (r + L) (by omega) (Nat.le_refl _))
    have hrq : r ≤ q := by
      obtain ⟨_, _, hbet⟩ := (par0_spec M).mp hq
      rcases Nat.lt_or_ge q r with h4 | h4
      · have h5 := hbet r h4 (by omega)
        have h6 := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
      · exact h4
    have hqx := par_lt M 0 _ _ hq
    have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [hq]; congr 1; omega
    have h1 := par0_gexp_root (d1 := 0) (n := n) hlen (k := k + 1) (by omega) (by omega) (by omega)
      hd0e hq'
    have h2 := par0_gexp_root (d1 := 0) (n := n - 1) hlen (k := k) (by omega) hk1 (by omega) hd0e hq'
    rw [show r + L + (k * L + 0) = r + ((k + 1) * L + 0) by rw [Nat.succ_mul]; omega, h1,
      show r + (k * L + 0) = r + (k * L + 0) from rfl, h2]
    simp only [Option.map_some, Nat.add_sub_cancel]
    congr 1
    have hkL : k * L = (k - 1) * L + L := by
      rw [← Nat.succ_mul, show (k - 1).succ = k by omega]
    omega
  · obtain ⟨pa, hpa⟩ := par0_some_of (show r < r + qb by omega)
      (anc0_interval hA (r + qb) (by omega) (by omega))
    have hge := par0_ge_of_anc hA (show r < r + qb by omega) (by omega) hpa
    have hlt := par_lt M 0 _ _ hpa
    have hpa' : par M 0 (r + qb) = some (r + (pa - r)) := by rw [hpa]; congr 1; omega
    have h1 := par0_gexp_mir (d0 := d0) (d1 := 0) (n := n) hlen (k := k + 1) (by omega) hqb hpa'
    have h2 := par0_gexp_mir (d0 := d0) (d1 := 0) (n := n - 1) hlen (k := k) hk hqb hpa'
    rw [hidx1, h1, h2]
    simp only [Option.map_some]
    congr 1
    rw [Nat.succ_mul]; omega

omit hL hA hd0e hn in
theorem entry1_gexp_d1z {k q : Nat} {m : Nat} (hk : k < m) (hq : q < L) :
    entry (TRIO.gexp M r L d0 0 m) 1 (r + (k * L + q)) = entry M 1 (r + q) := by
  unfold entry
  rw [TRIO.gexp_getD_mir hlen hk hq]
  simp [TRIO.entry]

/-- **Copy shift (two rows, `t = 1`).** -/
theorem o2r_gexp_shift (hF1n : F1 (TRIO.gexp M r L d0 0 n)) (hF1p : F1 (TRIO.gexp M r L d0 0 (n - 1))) :
    ∀ p, p < (n - 1) * L →
      o2r (TRIO.gexp M r L d0 0 n) (r + L + p) = o2r (TRIO.gexp M r L d0 0 (n - 1)) (r + p) := by
  have hlenN : (TRIO.gexp M r L d0 0 n).length = r + L + (n - 1) * L := by
    rw [TRIO.gexp_length hlen]
    have : n * L = (n - 1) * L + L := by rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
    omega
  have hlenP : (TRIO.gexp M r L d0 0 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen
  have key : ∀ m p, (n - 1) * L - p ≤ m → p < (n - 1) * L →
      o2r (TRIO.gexp M r L d0 0 n) (r + L + p) = o2r (TRIO.gexp M r L d0 0 (n - 1)) (r + p) := by
    intro m
    induction m with
    | zero => intro p h1 h2; omega
    | succ m ih =>
      intro p hm hp
      obtain ⟨k, qb, hk, hqb, hpk⟩ := TRIO.gexp_pos_decomp (j0 := 0) (n := n - 1) (p := p) hL
        (Nat.zero_le _) (by simpa using hp)
      simp only [Nat.zero_add] at hpk
      apply o2r_congr
      · rw [vr_eq_nT hF1n, vr_eq_nT hF1p]
        congr 1
        rw [show r + L + p = r + ((k + 1) * L + qb) by rw [hpk, Nat.succ_mul]; omega,
          entry1_gexp_d1z hlen (by omega) hqb, hpk,
          entry1_gexp_d1z hlen hk hqb]
      · rw [children_above _ (r + L) ((n - 1) * L) _ hlenN (fun c hc h => by
            have := par_lt _ 0 c _ h; omega),
          children_above _ r ((n - 1) * L) _ hlenP (fun c hc h => by
            have := par_lt _ 0 c _ h; omega)]
        have hF : (List.range ((n - 1) * L)).filter
              (fun j => decide (par (TRIO.gexp M r L d0 0 n) 0 (r + L + j) = some (r + L + p))) =
            (List.range ((n - 1) * L)).filter
              (fun j => decide (par (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + j) = some (r + p))) := by
          apply List.filter_congr
          intro j hj
          have hj' := List.mem_range.mp hj
          rcases Nat.eq_zero_or_pos j with h0 | h0
          · subst h0
            have e1 : par (TRIO.gexp M r L d0 0 n) 0 (r + L + 0) ≠ some (r + L + p) := by
              intro h; have := par_lt _ 0 _ _ h; omega
            have e2 : par (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + 0) ≠ some (r + p) := by
              intro h; have := par_lt _ 0 _ _ h; omega
            rw [decide_eq_false e1, decide_eq_false e2]
          · rw [par0_gexp_shift hlen hL hA hd0e hn h0 hj']
            cases par (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + j) with
            | none => simp
            | some v => simp; omega
        rw [hF, List.map_map, List.map_map]
        apply List.map_congr_left
        intro j hj
        rw [List.mem_filter] at hj
        have hjl := List.mem_range.mp hj.1
        have hpar : par (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + j) = some (r + p) := by
          simpa using hj.2
        have hjp : p < j := by have := par_lt _ 0 _ _ hpar; omega
        exact ih j (by omega) hjl
  exact fun p hp => key _ p (Nat.le_refl _) hp

end

end Ytosk
