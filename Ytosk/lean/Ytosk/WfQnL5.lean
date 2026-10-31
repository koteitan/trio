/-
**WfQnL5 (2026-11-01): the closure in `N = M[n]` is the closure in `M`, and (E1) off the closure in `M`.**
- `depXB_M_of_N`: given that no copy column reads a `v` of `D` below `x` (`hndN`, the `N`-form of the `hnd` of
  `val_N_t1`), every call of `DepXB N B` lies below `x` and is in `DepXB M B`.
- `hndN_of_hnd`: `hndN` at the copy columns `a > 0` from the `hnd` of `val_N_t1` (`par1_copy`, `upg_copy`).
- `E1_M`: a solution of the equations of `N` equals the glue at every call outside `DepXB M B`.
-/
import Ytosk.WfQnL4

namespace Ytosk.WfQnL5
open T Ytosk Ytosk.WfQnE3 Ytosk.WfQnL4

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
  (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L → entry M 1 r < entry M 1 s)
  (hx2 : entry M 2 (r + L) = 0)
  (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
  (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
  (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
  {rkM : Bool → Nat → Nat} (hRM : Rk M rkM) {B : Nat → Prop} (hB : ∀ i, B i → DepX M (r + L) false i)
  (hndN : ∀ a, a < (n - 1) * L → ∀ g, g < r + L →
      (par (TRIO.gexp M r L d0 0 n) 1 (r + L + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 n) (r + L + a) = some g) → ¬ DepX M (r + L) false g)
include hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux hRM hB hndN

/-- **The closure in `N` lies below `x` and inside the closure in `M`.** -/
theorem depXB_M_of_N : ∀ {b i}, DepXB (TRIO.gexp M r L d0 0 n) B b i → i < r + L ∧ DepXB M B b i := by
  have hlN := len_N (d0 := d0) hlen hn
  have hbN : ∀ i, i < r + L → bump (TRIO.gexp M r L d0 0 n) i = bump M i := by
    intro i hi
    unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hi, entry_gexp_pre hlen (by omega) 1 hi]
  have hcopy : ∀ i, r + L ≤ i → entry (TRIO.gexp M r L d0 0 n) 1 i ≠ 0 → ∀ g, g < r + L →
      (par (TRIO.gexp M r L d0 0 n) 1 i = some g ∨ upg (TRIO.gexp M r L d0 0 n) i = some g) →
      ¬ DepX M (r + L) false g := by
    intro i hi h1 g hg hr
    have hiN : i < (TRIO.gexp M r L d0 0 n).length := by
      by_contra hc; exact h1 (entry_ge (by omega))
    have := hndN (i - (r + L)) (by omega) g hg
    rw [show r + L + (i - (r + L)) = i by omega] at this
    exact this hr
  intro b i h
  induction h with
  | leaf h0 =>
    exact ⟨depXB_lt hRM (by omega) hB (DepXB.leaf h0), DepXB.leaf h0⟩
  | @ochild i c hc hb hu _ ih =>
    obtain ⟨hcx, hd⟩ := ih
    have hic := (mem_children hc).1
    have hix : i < r + L := by omega
    rw [children_N_lt hlen hL hA hd0e hn hix] at hc
    rw [col_gexp_pre hlen (by omega) hcx, hbN i hix] at hb
    rw [hiu c hcx, topped_N_lt hlen hL hA hd0e hn hpath hx2 hxnb hcx] at hu
    exact ⟨hix, DepXB.ochild hc hb hu hd⟩
  | @ov i _ ih => exact ⟨ih.1, DepXB.ov ih.2⟩
  | @vpar i m h1 hm _ ih =>
    obtain ⟨hmx, hd⟩ := ih
    rcases Nat.lt_or_ge i (r + L) with hix | hix
    · rw [entry_gexp_pre hlen (by omega) 1 hix] at h1
      rw [par_gexp_pre hlen (by omega) 1 hix] at hm
      exact ⟨hix, DepXB.vpar h1 hm hd⟩
    · exact absurd (DepXB.sub hB hd) (hcopy i hix h1 m hmx (Or.inl hm))
  | @vupg i k h1 h2 hk _ ih =>
    obtain ⟨hkx, hd⟩ := ih
    rcases Nat.lt_or_ge i (r + L) with hix | hix
    · have SA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux i hix
      rw [SA.e1] at h1; rw [SA.e2] at h2; rw [SA.upg] at hk
      exact ⟨hix, DepXB.vupg h1 h2 hk hd⟩
    · exact absurd (DepXB.sub hB hd) (hcopy i hix h1 k hkx (Or.inr hk))
  | @vbump i j k h1 h2 hj hb hk _ ih =>
    obtain ⟨hkx, hd⟩ := ih
    have hjk := (mem_children hk).1
    have hij := (mem_children hj).1
    have hjx : j < r + L := by omega
    have hix : i < r + L := by omega
    rw [entry_gexp_pre hlen (by omega) 1 hix] at h1
    rw [entry_gexp_pre hlen (by omega) 2 hix] at h2
    rw [children_N_lt hlen hL hA hd0e hn hix] at hj
    rw [col_gexp_pre hlen (by omega) hjx, hbN i hix] at hb
    rw [children_N_lt hlen hL hA hd0e hn hjx] at hk
    exact ⟨hix, DepXB.vbump h1 h2 hj hb hk hd⟩

/-- **(E1) off the closure in `M`**: below `x`, a solution of `N` equals the glue off `DepXB M B`;
from `x` on it equals the glue everywhere. -/
theorem E1_M (hz2 : entry M 2 r ≤ 1) {ρ ρP : Valn} {Z : Nat → T} (hC : Cons M ρ)
    (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hagree : ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) →
      (glueZ M (r + L) ρ (shiftV ρP L) Z).v g = ρP.v g)
    (hF : ∀ i, i < r + L →
      (DepX M (r + L) true i → ¬ DepXB M B true i →
        oRhs M (glueZ M (r + L) ρ (shiftV ρP L) Z) i = fsD (ρ.o i) (Z i)) ∧
      (DepX M (r + L) false i → ¬ DepXB M B false i →
        vRhs M (glueZ M (r + L) ρ (shiftV ρP L) Z) i = fsD (ρ.v i) (Z i)))
    {σ : Valn} {rkN : Bool → Nat → Nat} (hCN : Cons (TRIO.gexp M r L d0 0 n) σ)
    (hRN : Rk (TRIO.gexp M r L d0 0 n) rkN) :
    (∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ (i < r + L ∧ DepXB M B true i) →
      σ.o i = (glueZ M (r + L) ρ (shiftV ρP L) Z).o i) ∧
    (∀ i, i < (TRIO.gexp M r L d0 0 n).length → ¬ (i < r + L ∧ DepXB M B false i) →
      σ.v i = (glueZ M (r + L) ρ (shiftV ρP L) Z).v i) := by
  have hE := E1_N hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux hRM hB hz2 hC hCP hagree hF hCN hRN
  exact ⟨fun i hi hnb => hE.1 i hi (fun hd => hnb (depXB_M_of_N hlen hL hA hd0e hn hpath hx2 hxnb hiu
      hiux hRM hB hndN hd)),
    fun i hi hnb => hE.2 i hi (fun hd => hnb (depXB_M_of_N hlen hL hA hd0e hn hpath hx2 hxnb hiu
      hiux hRM hB hndN hd))⟩

end

end Ytosk.WfQnL5
