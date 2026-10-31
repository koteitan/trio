/-
**WfQnL8 (2026-11-01): `hndN` (WfQnL5) from the `hnd` of `val_N_t1`.**
The copy columns of `N = M[n]` read below `x` only the row-1 parents / upgrade targets `g ≤ r` read by `P = M[n-1]`
(`par1_copy`, `upg_copy`, `par1_root`, `upg_root`).  The upgrade target of the copy root needs `g ≤ r` (`hu0`).
-/
import Ytosk.WfQnL5

namespace Ytosk.WfQnL8
open T Ytosk

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L → entry M 1 r < entry M 1 s)
  (hz2 : entry M 2 r ≤ 1)
include hlen hL hA hd0e hn hpath hz2

theorem hndN_of_hnd
    (hnd : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ¬ DepX M (r + L) false g)
    (hu0 : ∀ g, upg (TRIO.gexp M r L d0 0 (n - 1)) r = some g → g ≤ r) :
    ∀ a, a < (n - 1) * L → ∀ g, g < r + L →
      (par (TRIO.gexp M r L d0 0 n) 1 (r + L + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 n) (r + L + a) = some g) → ¬ DepX M (r + L) false g := by
  intro a ha g hg hr
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    rw [Nat.add_zero] at hr
    rcases hr with hp | hu
    · rw [par1_root hlen hL hA hd0e hn hpath] at hp
      have hgr := par_lt M 1 r g hp
      apply hnd g (by omega) 0 ha
      left
      rw [Nat.add_zero, par_gexp_pre hlen (by omega) 1 (by omega)]
      exact hp
    · rw [upg_root hlen hL hA hd0e hn hpath hz2] at hu
      exact hnd g (hu0 g hu) 0 ha (Or.inr (by rw [Nat.add_zero]; exact hu))
  · rcases hr with hp | hu
    · rw [par1_copy hlen hL hA hd0e hn hpath hpos ha] at hp
      obtain ⟨p, hp', he⟩ := Option.map_eq_some_iff.mp hp
      by_cases hrp : r ≤ p
      · rw [if_pos hrp] at he; omega
      · rw [if_neg hrp] at he
        subst he
        exact hnd p (by omega) a ha (Or.inl hp')
    · rw [upg_copy hlen hL hA hd0e hn hpath hpos ha] at hu
      obtain ⟨t, hu', he⟩ := Option.map_eq_some_iff.mp hu
      by_cases hrt : r < t
      · rw [if_pos hrt] at he; omega
      · rw [if_neg hrt] at he
        subst he
        exact hnd t (by omega) a ha (Or.inr hu')

end

end Ytosk.WfQnL8
