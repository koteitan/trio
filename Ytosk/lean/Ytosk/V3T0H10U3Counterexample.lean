/-
A kernel-checked standard counterexample to the overstrong U3 proposal.
The explicit expansion trace starts at SRO. Strong absorption still holds,
so this is not a counterexample to T0BadSeedsH10.
-/
import Ytosk.V3T0H10Core

namespace Ytosk.T0H10U3Counterexample
open T T0H10Core
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def M : Mat := [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (5, 2, 0), (3, 2, 1), (4, 2, 1), (5, 1, 0), (6, 2, 1), (7, 2, 1), (8, 2, 0), (6, 2, 1), (7, 2, 1), (8, 1, 0), (7, 0, 0), (1, 1, 0), (2, 2, 1), (3, 2, 1), (4, 2, 0), (2, 2, 1), (3, 2, 1), (4, 2, 0), (2, 2, 1), (3, 2, 0), (4, 3, 1), (5, 3, 1), (6, 3, 0), (4, 3, 1), (5, 3, 1), (6, 2, 0), (7, 3, 1), (8, 3, 1), (9, 3, 0), (7, 3, 1), (8, 3, 1), (9, 2, 0), (8, 0, 0)]

def trace : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 0, 1, 1, 1, 2, 0, 1, 1, 1, 2, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 2, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0, 2, 0, 0, 1, 1, 1, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 2, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0, 1, 2, 0, 0, 1, 1, 1, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 2, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 2, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0, 0, 2]

private theorem std_fold : ∀ (ns : List Nat) (N : Mat), Std N → Std (ns.foldl expand N)
  | [], _, h => h
  | n :: ns, N, h => std_fold ns (expand N n) (Std.exp n h)

theorem standard : Std M := by
  have h : trace.foldl expand SRO = M := by decide
  rw [← h]
  exact std_fold trace SRO Std.sro

theorem ne_sro : M ≠ SRO := by decide

theorem frame : Frame M 40 3 36 := by
  constructor <;> decide

theorem preceding_upgrade : upg M 39 = some 40 := by decide

theorem final_upgrade : upg M 42 = some 29 := by decide

theorem final_parent : par M 1 42 = some 22 := by decide

theorem nonzero_parent : entry M 1 22 = 1 := by decide

theorem not_parent_zero : ¬ ParentZeroAt M 40 3 := by
  intro h
  obtain ⟨p, hp, he⟩ := h preceding_upgrade 29 final_upgrade
  change par M 1 42 = some p at hp
  rw [final_parent] at hp
  cases hp
  rw [nonzero_parent] at he
  cases he

theorem not_universal_parent_zero :
    ¬ (∀ N, Std N → N ≠ SRO → ∀ r L g, Frame N r L g → ParentZeroAt N r L) := by
  intro h
  exact not_parent_zero (h M standard ne_sro 40 3 36 frame)

/-- The parent has value one under every consistent valuation. -/
theorem parent_value_one {ρ : Valn} (hC : Cons M ρ) : ρ.v 22 = one := by
  have hv0 : ρ.v 0 = z := v_z_of_e1 hC (by decide) (by decide)
  have hp : par M 1 22 = some 0 := by decide
  have hu : upg M 22 = none := by decide
  have he1 : entry M 1 22 ≠ 0 := by decide
  have he2 : entry M 2 22 = 0 := by decide
  have hv := (hC 22 (by decide)).2
  rw [vRhs, if_neg he1, if_pos he2, hp, hu, vOpt, hv0] at hv
  exact hv

/-- The counterexample has strong absorption for every consistent valuation. -/
theorem strong {ρ : Valn} (hC : Cons M ρ) : UpgAbsX M 43 ρ := by
  intro i k W hix _ _ _ q hq hlt
  have hi : i = 42 := by omega
  subst i
  have hv : vOpt ρ (par M 1 42) = one := by
    rw [final_parent]
    exact parent_value_one hC
  rw [hv] at hq
  have heq : q = one := by simpa [summands, one] using hq
  subst q
  exact lhd_one hlt

/-- Thus this standard U3 counterexample does not satisfy Bad2. -/
theorem not_bad2 : ¬ Bad2 M := by
  rintro ⟨_, p, g, hp, hg, hb, hbad | hbad⟩
  · obtain ⟨_, ρ, hC, hnot⟩ := hbad
    have hx : M.length - 1 = 43 := by decide
    rw [hx] at hnot
    exact hnot (strong hC)
  · have hne := hbad.2.1
    have hz : entry M 1 (M.length - 1) = 0 := by decide
    exact hne hz

end Ytosk.T0H10U3Counterexample
