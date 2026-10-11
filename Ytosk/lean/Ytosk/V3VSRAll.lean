/-
**VSmallRA をすべての数える子の枠に強めた形 `VSmallRAll`（2026-10-12、t0-exp）。**

t2 の VSmallRA（V3DepRWU）は最後の数える子の枠（CL M k = Lc ++ [c]）だけ。t = 0 の展開 N = M[n] の中間の写しでは、
根の最後の数える子が M と違う（x は写さない）。M ではそれが最後でない子の枠なので、すべての数える子の枠（CL M k = Lc ++ c :: R）で
段を運ぶ形が要る。最後の子の形はその R = [] の場合（`VSmallRAll.toLast`）。
-/
import Ytosk.V3DepRWU

namespace Ytosk

open T

/-- **The levels of the rewriting frames above**, at every counted child. -/
inductive PathLvAll (M : Mat) (ρ : Valn) : Nat → T → Prop
  | top {k c : Nat} {Lc R : List Nat} {s y : T} : CL M k = Lc ++ c :: R → ρ.o c = psi s y z →
      (lt (spArg (ρ.v k) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v k) z z) (psi s y z) = true) →
      PathLvAll M ρ c (ρ.v k)
  | step {k c : Nat} {Lc R : List Nat} {s y u : T} : CL M k = Lc ++ c :: R → ρ.o c = psi s y z →
      (lt (spArg (ρ.v k) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v k) z z) (psi s y z) = true) →
      PathLvAll M ρ k u → PathLvAll M ρ c u

/-- **`VSmallR` at the levels of the rewriting frames above, at every counted child.** -/
def VSmallRAll (M : Mat) (ρ : Valn) : Prop :=
  ∀ k c (Lc R : List Nat) s y, CL M k = Lc ++ c :: R → ρ.o c = psi s y z →
    (lt (spArg (ρ.v k) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v k) z z) (psi s y z) = true) →
    (split y (psi (succ s) z z)).1 ≠ z →
    ∀ u, (u = ρ.v k ∨ PathLvAll M ρ k u) → ¬ lt (ρ.v k) u = true → ∀ g ∈ comps u s,
      g ≤ psi s z z ∨ g ≤ spArg (ρ.v k) z (sumN (Lc.map ρ.o)) ∨ ∃ d ∈ comps u (ρ.v k), g ≤ d

theorem PathLvA.toAll {M : Mat} {ρ : Valn} {i : Nat} {u : T} (h : PathLvA M ρ i u) : PathLvAll M ρ i u := by
  induction h with
  | top hcl hsy ht => exact PathLvAll.top hcl hsy ht
  | step hcl hsy ht _ ih => exact PathLvAll.step hcl hsy ht ih

/-- **The last-child form** (t2's `VSmallRA`) is the case `R = []`. -/
theorem VSmallRAll.toLast {M : Mat} {ρ : Valn} (h : VSmallRAll M ρ) : VSmallRA M ρ :=
  fun k c Lc s y hcl hsy ht hhz u hu => h k c Lc [] s y hcl hsy ht hhz u (hu.imp id PathLvA.toAll)

end Ytosk
