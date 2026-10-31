/-
**WfExQ3 (2026-11-01): the frame residual `FrameAtN` of WfExQ2 from the global `HFrameV3`.**
`M[n] = expand M n` is standard when `M` is (as in `expT1Out_of_res`), so the global frame residual for every
standard matrix gives the frame fields at every `M[n]` of a `t = 1` expansion.
-/
import Ytosk.WfExQ2

namespace Ytosk.WfExQ3
open T Ytosk Ytosk.WfExQ1 Ytosk.WfExQ2

theorem frameAtN_of_glob (hF : HFrameV3) {M : Mat} {r L : Nat} (hM : Std M)
    (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    FrameAtN M r L (entry M 0 (r + L) - entry M 0 r) := by
  intro n hn σ rk hC hR hG
  have hx : M.length - 1 = r + L := by omega
  have he1 : 0 < entry M 1 (r + L) := by have := par1_entry_lt h1; omega
  have ht : TRIO.srow M (M.length - 1) = 1 := by
    unfold TRIO.srow
    rw [hx]
    have h2 : ¬ 0 < TRIO.entry M 2 (r + L) := by
      show ¬ 0 < entry M 2 (r + L); omega
    have h1' : 0 < TRIO.entry M 1 (r + L) := he1
    rw [if_neg h2, if_pos h1']
  have hz : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := by
    rw [hx]; intro h
    have : entry M 1 (r + L) = 0 := h.2.1
    omega
  have hexp := expand_eq_gexp_t1 M n (by omega) hz (by rw [ht, hx]; exact h1) ht
  rw [hx] at hexp
  simp only [Nat.add_sub_cancel_left] at hexp
  have hStd : Std (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) := by
    rw [← hexp]; exact Std.exp n hM
  have hE : TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [len_N (d0 := entry M 0 (r + L) - entry M 0 r) hlen hn]
    omega
  exact hF _ σ rk hStd (ne_SRO_of_rk hR) hE hC hR hG

end Ytosk.WfExQ3
