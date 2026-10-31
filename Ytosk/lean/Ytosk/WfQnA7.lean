/-
**WfQnA7 (2026-11-01): Good3 of `M[n]` for the true valuation, t = 1, q ≠ r, with the bad closure.**
`good3_N_t1B`: `WfQnA6.good3_N_gen` with the off-`D` and copy values from (E1) off the closure, the values on
`D \ closure` from the glue (`fsD(·, ζ)`), and the values on the closure from the `◁` engine (`hEng`, the
conclusion of `WfQnA3.engine_t1B`).
-/
import Ytosk.WfQnA6

namespace Ytosk.WfQnA7
open T Ytosk Ytosk.WfQnE3

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

theorem good3_N_t1B (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP σ : Valn} {ζ : T} {B : Nat → Prop} (hB : ∀ i, B i → DepX M (r + L) false i)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons (TRIO.gexp M r L d0 0 n) σ)
    (hGP : Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (hE1o : ∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ (i < r + L ∧ DepXB M B true i) →
      σ.o i = (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => ζ)).o i)
    (hE1v : ∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ (i < r + L ∧ DepXB M B false i) →
      σ.v i = (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => ζ)).v i)
    (hOTD : ∀ b j, j < r + L → DepX M (r + L) b j → isOT (fsD (valB ρ b j) ζ) = true)
    (hleD : ∀ c, c < r + L → DepX M (r + L) true c → fsD (ρ.o c) ζ ≤ ρ.o c ∧ fsD (ρ.o c) ζ ≠ z)
    (hEng : ∀ b i, DepXB M B b i → i < r + L → Lhd z (valB σ b i) (valB ρ b i) ∧ isOT (valB σ b i) = true)
    (hlex : ρP.o r ≤ ρ.o (r + L) ∧ ρP.o r ≠ z) :
    Good3 (TRIO.gexp M r L d0 0 n) σ := by
  have hlN := len_N (d0 := d0) (n := n) hlen hn
  have hxN : r + L < (TRIO.gexp M r L d0 0 n).length := by
    rw [hlN]; have := Nat.mul_le_mul_right L (show 1 ≤ n - 1 by omega); simp at this; omega
  have hoff := WfQnH8.hoff_of_E1 hB hxN hE1o hE1v
  apply WfQnA6.good3_N_gen hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hC hG hGP hOS
    (fun i hi hnd => (hoff i hi).1 hnd) (fun i hi hnd => (hoff i hi).2 hnd)
    (fun i hi hiN => by rw [hE1o i hiN (fun h => by omega), glueZ_o_ge _ _ _ hi])
    (fun i hi hiN => by rw [hE1v i hiN (fun h => by omega), glueZ_v_ge _ _ _ hi])
  · intro i hi hd
    by_cases hb : DepXB M B true i
    · exact (hEng true i hb hi).2
    · rw [hE1o i (by omega) (fun h => hb h.2), glueZ_o_dep _ _ _ hi hd]; exact hOTD true i hi hd
  · intro i hi hd
    by_cases hb : DepXB M B false i
    · exact (hEng false i hb hi).2
    · rw [hE1v i (by omega) (fun h => hb h.2), glueZ_v_dep _ _ _ hi hd]; exact hOTD false i hi hd
  · intro c hc hd
    by_cases hb : DepXB M B true c
    · obtain ⟨hl, hot⟩ := hEng true c hb hc
      refine ⟨le_of_lt hl.1, ?_⟩
      obtain ⟨s, y, he⟩ := o_psi_form hCN (show c < (TRIO.gexp M r L d0 0 n).length by omega)
      change σ.o c ≠ z
      rw [he]; simp
    · rw [hE1o c (by omega) (fun h => hb h.2), glueZ_o_dep _ _ _ hc hd]; exact hleD c hc hd
  · exact hlex

end

end Ytosk.WfQnA7
