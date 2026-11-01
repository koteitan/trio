/-
**V3AbsUpgShape (2026-11-01): the upgrade shape of a bad absorption column, and the bad set `BdXU`.**

`WfAbsW.AbsWNx` (the input `hBX` of the V3 translation entry) is false on a standard 41-column matrix
(`V3T2AbsXFalse`): the absorption fails at a column `i` that is not in `BadAbsShape`, because `c = i − 1` upgrades
to `i` and `i` is not counted by its parent.  All six such frames of the measured data
(tmp/claude/abs_slack.py, tmp/claude/upg-shape-design.md) have the shape `UpgAbsShape` below, and only `i` and `c`
carry slack.

- `UpgAbsShape`: the measured shape (all fields true on the six frames).
- `AbsWNxU`: `AbsWNx` with the extra alternative `UpgAbsShape`.  `AbsWNx.toU`: the old input implies the new one.
- `BdXU`: the bad set of the engine `WfT2X.deps_lhd_otXU`: the old bad columns `BdX`, the upgrade-shape columns,
  and their upgraders.
- `bdxu_absX`, `bdxu_up`, `bdxu_F`, `bdxu_cl`, `notBumpKidXU_of`: the engine hypotheses `hAbsX`, `hBdUp`, `hBdF`,
  the `CL = []` fact and `hBdK` for `BdXU`.
-/
import Ytosk.WfT2X1U
import Ytosk.WfT2X3

namespace Ytosk.WfT2X

open T Ytosk.WfAbsW

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The upgrade shape** at a bump-type column `i` whose absorption fails: `m = P₀ i = P₁ i` does not count `i`,
`i` has no counted children, exactly one column `c` upgrades to `i`, nothing upgrades to `c`, `c` has no counted
children, and is counted by its parent `p`; neither `m` nor `p` is a bump child; every component of `v(m)` is below
the new `o(c)`. -/
def UpgAbsShape (M N : Mat) (ρ σ : Valn) (i : Nat) : Prop :=
  ∃ m c p, par M 0 i = some m ∧ par M 1 i = some m ∧ CL M i = [] ∧ CL N i = [] ∧
    i ∉ CL M m ∧ upg M c = some i ∧ (∀ j, upg M j = some i → j = c) ∧ (∀ j, upg M j ≠ some c) ∧
    par M 0 c = some p ∧ CL M c = [] ∧ CL N c = [] ∧
    (∀ q, par M 0 m = some q → col M m ≠ bump M q) ∧ (∀ q, par M 0 p = some q → col M p ≠ bump M q) ∧
    (∀ u, ∀ g ∈ comps u (ρ.v m), g < σ.o c)

/-- **The repaired absorption input**: absorption, the bad shape, or the upgrade shape. -/
def AbsWNxU (M N : Mat) (bnd : Nat) (ρ σ : Valn) : Prop :=
  ∀ i, i < bnd → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
    AbsAt M N ρ σ i ∨ BadAbsShape M N ρ σ i ∨ UpgAbsShape M N ρ σ i

theorem AbsWNx.toU {M N : Mat} {bnd : Nat} {ρ σ : Valn} (h : AbsWNx M N bnd ρ σ) : AbsWNxU M N bnd ρ σ :=
  fun i hi h1 h2 => (h i hi h1 h2).elim Or.inl (fun h => Or.inr (Or.inl h))

/-- An upgrade-shape bad column. -/
def BdU (M N : Mat) (ρ σ : Valn) (bnd i : Nat) : Prop :=
  i < bnd ∧ entry M 1 i ≠ 0 ∧ entry M 2 i ≠ 0 ∧ ¬ AbsAt M N ρ σ i ∧ UpgAbsShape M N ρ σ i

/-- **The bad set**: old bad columns, upgrade-shape columns, and the columns that upgrade to the latter. -/
def BdXU (M N : Mat) (ρ σ : Valn) (bnd i : Nat) : Prop :=
  BdX M N ρ σ bnd i ∨ BdU M N ρ σ bnd i ∨ ∃ k, upg M i = some k ∧ BdU M N ρ σ bnd k

theorem bdxu_absX {M N : Mat} {bnd : Nat} {ρ σ : Valn} (h : AbsWNxU M N bnd ρ σ) :
    ∀ i, i < bnd → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → AbsAt M N ρ σ i ∨ BdXU M N ρ σ bnd i := by
  intro i hi h1 h2
  by_cases hA : AbsAt M N ρ σ i
  · exact Or.inl hA
  · rcases (h i hi h1 h2).resolve_left hA with hS | hU
    · exact Or.inr (Or.inl ⟨hi, h1, h2, hA, hS⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hi, h1, h2, hA, hU⟩))

/-- **Closure under upgrades** (`hBdUp`). -/
theorem bdxu_up {M N : Mat} {bnd : Nat} {ρ σ : Valn} :
    ∀ i k, upg M i = some k → BdXU M N ρ σ bnd k → BdXU M N ρ σ bnd i := by
  intro i k hu hk
  rcases hk with hX | hU | ⟨k', hk', hU'⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, hnu⟩ := hX.2.2.2.2
    exact absurd hu (hnu i)
  · exact Or.inr (Or.inr ⟨k, hu, hU⟩)
  · obtain ⟨m, c, p, _, _, _, _, _, hc, huniq, hnoc, _⟩ := hU'.2.2.2.2
    have hkc : k = c := huniq k hk'
    subst hkc
    exact absurd hu (hnoc i)

/-- **Bad columns have no counted children.** -/
theorem bdxu_cl {M N : Mat} {bnd : Nat} {ρ σ : Valn} :
    ∀ i, BdXU M N ρ σ bnd i → CL M i = [] ∧ CL N i = [] := by
  intro i hi
  rcases hi with hX | hU | ⟨k, hk, hU⟩
  · obtain ⟨_, _, _, _, hcM, hcN, _⟩ := hX.2.2.2.2
    exact ⟨hcM, hcN⟩
  · obtain ⟨_, _, _, _, _, hcM, hcN, _⟩ := hU.2.2.2.2
    exact ⟨hcM, hcN⟩
  · obtain ⟨m, c, p, _, _, _, _, _, hc, huniq, _, _, hcM, hcN, _⟩ := hU.2.2.2.2
    have hic : i = c := huniq i hk
    subst hic
    exact ⟨hcM, hcN⟩

/-- **The frame shape** (`hBdF`). -/
theorem bdxu_F {M N : Mat} {bnd : Nat} {ρ σ : Valn} :
    ∀ i c, BdXU M N ρ σ bnd c → c ∈ CL M i → CL M c = [] ∧ CL N c = [] ∧
      (par M 1 c = some i ∨ ∀ u, ∀ g ∈ comps u (vOpt ρ (par M 1 c)), g < σ.o c) := by
  intro i c hc hcl
  have hp0 : par M 0 c = some i := (mem_children_iff.mp (cl_mem_children hcl)).2
  obtain ⟨hcM, hcN⟩ := bdxu_cl c hc
  refine ⟨hcM, hcN, ?_⟩
  rcases hc with hX | hU | ⟨k, hk, hU⟩
  · obtain ⟨m', _, hq0, hq1, _⟩ := hX.2.2.2.2
    rw [hp0] at hq0
    rw [← Option.some.inj hq0] at hq1
    exact Or.inl hq1
  · obtain ⟨m, c', p, hq0, _, _, _, hnot, _⟩ := hU.2.2.2.2
    rw [hp0] at hq0
    rw [← Option.some.inj hq0] at hnot
    exact absurd hcl hnot
  · obtain ⟨m, c', p, _, hk1, _, _, _, _, huniq, _, _, _, _, _, _, hsm⟩ := hU.2.2.2.2
    have hcc : c = c' := huniq c hk
    subst hcc
    right
    obtain ⟨m'', hm1, hm2, _⟩ := upg_spec hk
    rw [hk1] at hm2
    rw [hm1, ← Option.some.inj hm2]
    exact hsm

/-- **The parent of a bad column is not a bump child**, from the old residual on `BdX` and the shape fields. -/
def NotBumpKidXU (M N : Mat) (bnd : Nat) (ρ σ : Valn) : Prop :=
  ∀ i m p, BdXU M N ρ σ bnd i → par M 0 i = some m → par M 0 m = some p → col M m ≠ bump M p

theorem notBumpKidXU_of {M N : Mat} {bnd : Nat} {ρ σ : Valn} (h : NotBumpKidX M N bnd ρ σ) :
    NotBumpKidXU M N bnd ρ σ := by
  intro i m p hi hm hp
  rcases hi with hX | hU | ⟨k, hk, hU⟩
  · exact h i m p hX hm hp
  · obtain ⟨m', c, p', hq0, _, _, _, _, _, _, _, _, _, _, hnbm, _⟩ := hU.2.2.2.2
    rw [hm] at hq0
    rw [← Option.some.inj hq0] at hnbm
    exact hnbm p hp
  · obtain ⟨m', c, p', _, _, _, _, _, _, huniq, _, hpc, _, _, _, hnbp, _⟩ := hU.2.2.2.2
    have hic : i = c := huniq i hk
    subst hic
    rw [hm] at hpc
    rw [← Option.some.inj hpc] at hnbp
    exact hnbp p hp

end Ytosk.WfT2X
