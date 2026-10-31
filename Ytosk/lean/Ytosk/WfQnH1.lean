/-
**WfQnH1 (2026-11-01): the structural residual `hu0` of WfQnL8 is a theorem.**
In `P = M[n-1]` the column `r + 1` is a row-0 child of the bad root `r` (inside the bad part when `L ≥ 2`,
the first copy column with row 0 raised by `d0 > 0` when `L = 1`), so `upg P r` is an earlier column
(`upg_lt_of_child`).  Hence `hndN_of_hnd` needs only `hnd`.
-/
import Ytosk.WfQnL8
import Ytosk.V3EqSibS1
import Ytosk.V3ExpT2D

namespace Ytosk.WfQnH1
open T Ytosk

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- In `P = M[n-1]`, the column after the bad root is its row-0 child (when it exists). -/
theorem par0_succ_root_P (h1 : r + 1 < (TRIO.gexp M r L d0 0 (n - 1)).length) :
    par (TRIO.gexp M r L d0 0 (n - 1)) 0 (r + 1) = some r := by
  have hlP := len_P (d0 := d0) (n := n) hlen
  rw [hlP] at h1
  apply par0_next
  have hr0 : entry (TRIO.gexp M r L d0 0 (n - 1)) 0 r = entry M 0 r :=
    entry_gexp_pre hlen (by omega) 0 (by omega)
  rw [hr0]
  by_cases hL2 : 2 ≤ L
  · rw [entry_gexp_pre hlen (by omega) 0 (by omega)]
    have hc := child_succ hA (by omega)
    exact anc0_e0_lt (anc0_of_par M 0 r (r + 1) hc) (by omega)
  · have hL1 : L = 1 := by omega
    have hn3 : 2 ≤ n - 1 := by
      subst hL1
      have : 1 < (n - 1) * 1 := by omega
      omega
    have hd : 0 < d0 := by
      have := anc0_e0_lt hA (by omega); omega
    have ha : (0 : Nat) < (n - 1 - 1) * L := by
      subst hL1; omega
    have hc := e0_copy (M := M) (r := r) (L := L) (d0 := d0) (n := n - 1) hlen hL hn3 ha
    rw [show r + L + 0 = r + 1 by omega, show r + 0 = r by omega] at hc
    rw [hc, entry_gexp_pre hlen (by omega) 0 (by omega)]
    omega

/-- **`hu0`**: the upgrade target of the bad root in `P = M[n-1]` is an earlier column. -/
theorem hu0 : ∀ g, upg (TRIO.gexp M r L d0 0 (n - 1)) r = some g → g ≤ r := by
  intro g hg
  have hlt := upg_lt_len hg
  have hp := par0_succ_root_P hlen hL hA hd0e hn hlt
  have := upg_lt_of_child (anc0_of_par _ 0 r (r + 1) hp) hg
  omega

/-- `hndN_of_hnd` without the residual `hu0`. -/
theorem hndN_of_hnd'
    (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L → entry M 1 r < entry M 1 s)
    (hz2 : entry M 2 r ≤ 1)
    (hnd : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ¬ DepX M (r + L) false g) :
    ∀ a, a < (n - 1) * L → ∀ g, g < r + L →
      (par (TRIO.gexp M r L d0 0 n) 1 (r + L + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 n) (r + L + a) = some g) → ¬ DepX M (r + L) false g :=
  WfQnL8.hndN_of_hnd hlen hL hA hd0e hn hpath hz2 hnd (hu0 hlen hL hA hd0e hn)

end

end Ytosk.WfQnH1
