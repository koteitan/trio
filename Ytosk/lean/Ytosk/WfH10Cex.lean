/-
A standard matrix on which the H10 conclusion fails: Bad2 holds, the H10 frame holds
with entry1(g) = 2, and upg(r - 1) = r.  The matrix is reached from SRO by an explicit
expansion trace (143 steps).  Bad2 is witnessed by an explicit consistent valuation whose
strong absorption at x fails (summand omega of v(P1(x-1)) is not lhd Omega_omega).
The statement refuted here is H10Big without its Inv3V2 premise; the Python probes
(tmp/wf/WfH10) find every Inv3V2 field true on the actual valuation.
The consumer field of T0BadSeedsH6 (r stays counted at g in M[n]) also fails here.
-/
import Ytosk.V3T0H10Core
import Ytosk.TwoRowZ

namespace Ytosk.WfH10Cex
open T T0H10Core
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def M : Mat := [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (5, 2, 0), (3, 2, 1), (4, 2, 1), (5, 2, 0), (3, 2, 1), (4, 2, 1), (5, 1, 0), (4, 2, 0), (5, 3, 1), (6, 3, 1), (7, 3, 0), (5, 3, 1), (6, 3, 1), (7, 2, 0), (6, 0, 0)]

def trace : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

private theorem std_fold : ∀ (ns : List Nat) (N : Mat), Std N → Std (ns.foldl expand N)
  | [], _, h => h
  | n :: ns, N, h => std_fold ns (expand N n) (Std.exp n h)

theorem standard : Std M := by
  have h : trace.foldl expand SRO = M := by decide
  rw [← h]
  exact std_fold trace SRO Std.sro

theorem ne_sro : M ≠ SRO := by decide

theorem frame : Frame M 25 3 21 := by
  constructor <;> decide

theorem big : 2 ≤ entry M 1 21 := by decide

theorem preceding_upgrade : upg M 24 = some 25 := by decide

theorem final_upgrade : upg M 27 = some 18 := by decide

def oTab : List T := [(psi z (psi (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z (psi (psi (psi (psi z (psi z z z) z) z z) z z) (psi z z z) z)) z), (psi (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z), (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z), (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z z) z) z z) z z) z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z (psi (psi (psi (psi z (psi z z z) z) z z) z z) (psi z z z) z)) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z (psi (psi (psi (psi z (psi z z z) z) z z) z z) (psi z z z) z)) z), (psi (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z), (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z), (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) z z) z z) z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi (psi z (psi z z z) z) z z) (psi (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z (psi (psi (psi (psi z (psi z z z) z) z z) z z) (psi z z z) z)) z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi z (psi z z z) z) z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi (psi z (psi z z z) z) z z) (psi (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z (psi (psi (psi (psi z (psi z z z) z) z z) z z) (psi z z z) z)) z), (psi (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z z), (psi (psi (psi z (psi z z z) z) z (psi z (psi z z z) z)) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z), (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z), (psi (psi (psi (psi z (psi z z z) z) z z) z z) (psi z z z) z), (psi (psi (psi z (psi z z z) z) z (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) z z) z z) z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi z z z)]
def vTab : List T := [z, (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z), (psi z (psi z z z) z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi z (psi z z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi z (psi z z z) z) z z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) z z), (psi (psi z (psi z z z) z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi z (psi z z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z), (psi (psi z (psi z z z) z) z (psi z (psi z z z) z)), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi z (psi z z z) z) z (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) z z), z]

def ρ : Valn := ⟨fun i => oTab.getD i z, fun i => vTab.getD i z⟩

theorem cons : Cons M ρ := by
  unfold Cons
  decide

/-- The strong absorption at the last column fails for this valuation. -/
theorem not_strong : ¬ UpgAbsX M 28 ρ := by
  intro h
  have hl := h 27 18 (psi (psi z (psi z z z) z) z z) rfl final_upgrade (by decide) (by decide)
    (psi z (psi z z z) z) (by decide) (by decide)
  obtain ⟨_, hall⟩ := hl
  have hd := hall z (psi (psi z z z) z z) (by decide) (by decide)
  have hm : psi z z z ∈ comps z (psi z (psi z z z) z) := by decide
  obtain ⟨y, hy, hle⟩ := hd _ hm
  have hno : ∀ y ∈ comps z (psi (psi z z z) z z) ++ Gc z z,
      ¬ (lt (psi z z z) y = true ∨ psi z z z = y) := by decide
  exact hno y hy hle

theorem bad2 : Bad2 M := by
  refine ⟨⟨18, by decide⟩, 26, 25, by decide, by decide, by decide, Or.inl ⟨Or.inl ?_, ρ, cons, ?_⟩⟩
  · exact anc0_of_par M 0 25 (M.length - 1) (by decide)
  · exact not_strong

/-- H10Big without its Inv3V2 premise is false. -/
theorem h10_core_false :
    ¬ (∀ N, Std N → N ≠ SRO → Bad2 N → ∀ r L g, Frame N r L g → 2 ≤ entry N 1 g →
        upg N (r - 1) ≠ some r) := by
  intro h
  exact h M standard ne_sro bad2 25 3 21 frame big preceding_upgrade

/-- The copy root r = 25 is counted at g = 21 in M but not in M[2]. -/
theorem counted_M : Counted M 21 25 := by
  unfold Counted
  decide

theorem not_counted_exp2 : ¬ Counted (expand M 2) 21 25 := by
  unfold Counted
  decide

/-- The same in the form read by T0BadSeedsH6's third field. -/
theorem not_counted_gexp2 : ¬ Counted (TRIO.gexp M 25 3 0 0 2) 21 25 := by
  have h := expand_eq_gexp_t0 M 2 (by decide) (by decide) (r := 25) (by decide) (by decide)
  have hl : M.length - 1 - 25 = 3 := by decide
  rw [hl] at h
  rw [← h]
  exact not_counted_exp2

/-- The structural core of T0BadSeedsH6's third field (without Inv3V2) is false. -/
theorem h6_counted_core_false :
    ¬ (∀ N, Std N → N ≠ SRO → Bad2 N → ∀ r L, r + L + 1 = N.length → 0 < L →
        par N 0 (r + L) = some r → entry N 1 (r + L) = 0 →
        ∀ n, 2 ≤ n → ∀ g, par N 0 r = some g → r ≠ r + L - 1 → Counted N g r →
          Counted (TRIO.gexp N r L 0 0 n) g r) := by
  intro h
  exact not_counted_gexp2 (h M standard ne_sro bad2 25 3 (by decide) (by decide) (by decide) (by decide)
    2 le_rfl 21 (by decide) (by decide) counted_M)

end Ytosk.WfH10Cex
