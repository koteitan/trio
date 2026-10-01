/-
**3 行・t = 1・q ≠ r の基底を落とす補題から。**

`t1_main2` の基底の仮定（v(r) 不変、seed の標準形、seed ◁ o(r)、写しが読む v の一致）を、
落とす補題 `drop_all` の結論から出す。seed ◁ o(r) の狭義性（o(r) が実際に変わること）は仮定に残す。
-/
import Ytosk.V3DropMain
import Ytosk.V3BaseT1

namespace Ytosk

open T

section
variable {M : Mat} {r L : Nat} (hlen : r + L + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  {ρ ρ1 : Valn} {rk : Bool → Nat → Nat}
  (hC : Cons M ρ) (hG : Good3 M ρ) (hC1 : Cons (M.take (r + L)) ρ1) (hRk1 : Rk (M.take (r + L)) rk)
include hlen hR0 hZ2 hSD hZ1 hUAT hUAB hC hG hC1 hRk1

/-- **`v(r)` in the base.** -/
theorem base_v_r (hA : Anc0 M r (r + L)) (hrx : r ≠ r + L) (hqr : par M 0 (r + L) ≠ some r)
    (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L → entry M 1 r < entry M 1 s) :
    ρ1.v r = ρ.v r := by
  have hr : r < r + L := lt_of_le_of_ne hA.le hrx
  exact (chg_off hlen hC hG hC1 hRk1 r hr).2
    (v_r_not_chg hlen hR0 hZ2 hSD hZ1 hUAT hUAB hA hrx hqr hpath)

/-- **The `v` read by the copies is unchanged in the base.** -/
theorem base_v_read {g a : Nat} (hg : g ≤ r) (ha : a < L)
    (h : par (M.take (r + L)) 1 (r + a) = some g ∨ upg (M.take (r + L)) (r + a) = some g) :
    ρ.v g = ρ1.v g := by
  have hd : r + a < r + L := by omega
  have hgd : g < r + L := by omega
  symm
  apply (chg_off hlen hC hG hC1 hRk1 g hgd).2
  apply v_read_not_chg hlen hR0 hZ2 hSD hZ1 hUAT hUAB hd
  rcases h with h | h
  · left; rwa [par_take M 1 (r + a) hd] at h
  · right
    have hd1 : r + a + 1 < r + L := by
      by_contra hn
      have : r + a = r + L - 1 := by omega
      rw [this, upg_take_last M (by omega) (by omega)] at h; cases h
    rw [upg_take M hd1] at h
    refine ⟨h, ?_⟩
    obtain ⟨_, _, _, _, hcase⟩ := upg_spec h
    rcases hcase with h' | ⟨_, h'⟩
    · omega
    · exact h'

/-- **The seed relation in the base** from the drop lemma at `r`, given that `o(r)` changes. -/
theorem base_seed (hrx : r < r + L) (hPO : PO ρ ρ1 r) (hv : ρ1.v r = ρ.v r) (hne : ρ1.o r ≠ ρ.o r) :
    Lhd z (ρ1.o r) (ρ.o r) ∧ isOT (ρ1.o r) = true := by
  refine ⟨?_, hPO.2.1⟩
  have hrM : r < M.length := by omega
  have hrT : r < (M.take (r + L)).length := by rw [List.length_take]; omega
  rcases hPO.1 with h | ⟨⟨w', w, X, hw', hw, hW⟩, _⟩
  · rcases h with h | h
    · exact absurd h hne
    · exact h
  · exfalso
    obtain ⟨y1, hy1⟩ := o_psi_sub hC1 hrT
    obtain ⟨y0, hy0⟩ := o_psi_sub hC hrM
    rw [hw'] at hy1; rw [hw] at hy0
    simp only [psi.injEq] at hy1 hy0
    have hvot : isOT (ρ.v r) = true := hG.ot_v r hrM
    rw [hy1.1, hy0.1, hv] at hW
    exact lt_irrefl' _ hW.1

end

end Ytosk
