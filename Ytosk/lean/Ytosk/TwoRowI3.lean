/-
**(I2) 展開で不変条件 Inv2 が保たれる: t = 1（2 行）。**

N = M[n] = gexp M r L d0 0 n、P = M[n−1]。写しの領域（x 以降）は P の r 以降をずらしたもの（値・子・状態・添字）。
x 以前は経路の外が同じ、経路の上が小さい。つなぎ目は (q, x) の枠だけ。
-/
import Ytosk.TwoRowI2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

theorem lenN_t1 : (TRIO.gexp M r L d0 0 n).length = r + L + (n - 1) * L := by
  rw [TRIO.gexp_length hlen]
  have : n * L = (n - 1) * L + L := by rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
  omega

theorem lenP_t1 : (TRIO.gexp M r L d0 0 (n - 1)).length = r + (n - 1) * L := TRIO.gexp_length hlen

/-- **Children shift by one copy.** -/
theorem children_shift {p : Nat} (hp : p < (n - 1) * L) :
    children (TRIO.gexp M r L d0 0 n) (r + L + p) =
      (children (TRIO.gexp M r L d0 0 (n - 1)) (r + p)).map (· + L) := by
  have hlenN := lenN_t1 hlen hL hA hd0e hn
  have hlenP := lenP_t1 hlen hL hA hd0e hn
  rw [children_above _ (r + L) ((n - 1) * L) _ hlenN (fun c hc h => by
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
  rw [hF, List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp]; omega

theorem vr_shift (hF1n : F1 (TRIO.gexp M r L d0 0 n)) (hF1p : F1 (TRIO.gexp M r L d0 0 (n - 1)))
    {p : Nat} (hp : p < (n - 1) * L) :
    vr (TRIO.gexp M r L d0 0 n) (r + L + p) = vr (TRIO.gexp M r L d0 0 (n - 1)) (r + p) := by
  obtain ⟨k, qb, hk, hqb, hpk⟩ := TRIO.gexp_pos_decomp (j0 := 0) (n := n - 1) (p := p) hL
    (Nat.zero_le _) (by simpa using hp)
  simp only [Nat.zero_add] at hpk
  rw [vr_eq_nT hF1n, vr_eq_nT hF1p]
  congr 1
  rw [show r + L + p = r + ((k + 1) * L + qb) by rw [hpk, Nat.succ_mul]; omega,
    entry1_gexp_d1z hlen (by omega) hqb, hpk, entry1_gexp_d1z hlen hk hqb]

/-- **The state in a copy frame is the shifted state.** -/
theorem bst_shift (hF1n : F1 (TRIO.gexp M r L d0 0 n)) (hF1p : F1 (TRIO.gexp M r L d0 0 (n - 1)))
    {p1 p2 : Nat} (hp1 : p1 < (n - 1) * L) (hp12 : p1 < p2) (hp2 : p2 < (n - 1) * L) :
    bst (TRIO.gexp M r L d0 0 n) (r + L + p1) (r + L + p2) =
      bst (TRIO.gexp M r L d0 0 (n - 1)) (r + p1) (r + p2) := by
  unfold bst
  rw [vr_shift hlen hL hA hd0e hn hF1n hF1p hp1, children_shift hlen hL hA hd0e hn hp1,
    List.filter_map, List.map_map]
  congr 2
  have hfe : (children (TRIO.gexp M r L d0 0 (n - 1)) (r + p1)).filter
      ((fun d => decide (d < r + L + p2)) ∘ (· + L)) =
      (children (TRIO.gexp M r L d0 0 (n - 1)) (r + p1)).filter (fun d => decide (d < r + p2)) := by
    apply List.filter_congr; intro d _; simp only [Function.comp, decide_eq_decide]; omega
  rw [hfe]
  apply List.map_congr_left
  intro d hd
  rw [List.mem_filter] at hd
  have hdc := mem_children hd.1
  rw [lenP_t1 hlen hL hA hd0e hn] at hdc
  simp only [Function.comp]
  rw [show d + L = r + L + (d - r) by omega,
    o2r_gexp_shift hlen hL hA hd0e hn hF1n hF1p (d - r) (by omega), show r + (d - r) = d by omega]

end

end Ytosk
