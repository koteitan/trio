/-
**WfQnH6 (2026-11-01): (E3) at the root in the `◁` form.**
Measured (tmp/wf/WfQnH/meas.py `LZ.cl`): at every call of the closure `DepXB M B`, the true value of `N = M[n]` is
`◁` (`Lhd z`) the old value; at the bad leaves `sf(v(P₁ i) + A[ζ]) ◁ A` (`LZ.leaf`).  The glue values off the
closure are NOT `◁` the old values (`LZ.glue` fails), so the `◁` engine must be seeded at the bad leaves only.
- `e3_of_lhd`: `◁` and standard form at the root give the `hE3` of `WfQnH5.t1_rootB` / `WfQnL7.root_N_E3`.
-/
import Ytosk.WfQnH5

namespace Ytosk.WfQnH6
open T Ytosk Ytosk.WfQnE3

/-- **`◁` at the root gives (E3) at the root.** -/
theorem e3_of_lhd {N : Mat} {ρ σ : Valn} {Rt : Nat} (hCN : Cons N σ) (hRN : Rt < N.length)
    (hl : Lhd z (σ.o Rt) (ρ.o Rt)) (hot : isOT (σ.o Rt) = true) :
    Single (σ.o Rt) ∧ σ.o Rt < ρ.o Rt :=
  ⟨⟨hot, o_psi_form hCN hRN⟩, hl.1⟩

end Ytosk.WfQnH6
