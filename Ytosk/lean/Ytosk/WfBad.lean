/-
**WfBad (2026-11-01): the shared definition of the bad bump call** (t = 1, both q = r and q ≠ r engines).
A bump call `i` is bad for the node `A = o(r)` and the index `ζ` when
  * it has the bad shape `BadShape1 M i` (`m = P₀ i = P₁ i`, `CL i = []`, `CL m = Lc ++ [i]`, nothing upgrades to `i`),
  * rows 1 and 2 of `i` are nonzero (a bump frame),
  * its bump term is the node itself: `bumpW M ρ i = ρ.o r`,
  * some summand `q` of `v(P₁ i)` lies in the window `A[ζ] ≤ q < A` (absorbed by `A`, not by `A[ζ]`).
`BadSet M x ρ r ζ` = bad calls of `D` (`i < x`, `DepX M x false i`); its `DepX`-closure is `WfQnE3.DepXB`.
-/
import Ytosk.WfQnE2
import Ytosk.WfQnE3

namespace Ytosk.WfBad
open T Ytosk Ytosk.WfQnE2

/-- **The bad bump call.** -/
def BadCall (M : Mat) (ρ : Valn) (r : Nat) (ζ : T) (i : Nat) : Prop :=
  BadShape1 M i ∧ entry M 1 i ≠ 0 ∧ entry M 2 i ≠ 0 ∧ bumpW M ρ i = ρ.o r ∧
    ∃ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i ∧ ¬ q < fsD (bumpW M ρ i) ζ

/-- The bad calls of `D`. -/
def BadSet (M : Mat) (x : Nat) (ρ : Valn) (r : Nat) (ζ : T) (i : Nat) : Prop :=
  i < x ∧ DepX M x false i ∧ BadCall M ρ r ζ i

/-- The closure of the bad calls stays inside `D`. -/
theorem badSet_depX {M : Mat} {x : Nat} {ρ : Valn} {r : Nat} {ζ : T} {b : Bool} {i : Nat}
    (h : WfQnE3.DepXB M (BadSet M x ρ r ζ) b i) : DepX M x b i :=
  WfQnE3.DepXB.sub (fun _ hj => hj.2.1) h

/-- **Not bad = absorbed**: at a bump call of `D` that is not bad and has `W = o(r)` or not, every summand of
`v(P₁ i)` absorbed by `W` is absorbed by `W[ζ]`, as soon as the window statement fails only at bad calls. -/
theorem absorbed_of_not_bad {M : Mat} {ρ : Valn} {r : Nat} {ζ : T} {i : Nat}
    (hX : ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i →
      q < fsD (bumpW M ρ i) ζ ∨ (BadShape1 M i ∧ bumpW M ρ i = ρ.o r))
    (h1 : entry M 1 i ≠ 0) (h2 : entry M 2 i ≠ 0) (hnb : ¬ BadCall M ρ r ζ i) :
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i → q < fsD (bumpW M ρ i) ζ := by
  intro q hq hlt
  by_contra hn
  rcases hX q hq hlt with h | ⟨hs, hw⟩
  · exact hn h
  · exact hnb ⟨hs, h1, h2, hw, q, hq, hlt, hn⟩

end Ytosk.WfBad
