/-
TReflect1.lean — M3: the Σ_2 reflection (`TReflect1`), the reflect_one analog.
DECISIVE de-risking test: does the term-structural reflection route stay tractable
at Σ_2, or does the core appear already here?

External mirror (public): github.com/koteitan/dh-bms-wf-formal, `reflect_one`
(`Pattern/Reflect.lean:133`): from a label α ◁₁ β (α is Σ_2-elem in β), copy a
block y below β to y' below α, preserving the LEVEL-0 (≤₁) connections to the top.

## What reflect_one actually uses (read off its proof, lines 133-179)
- `e = Elem 2 α β` — the Σ_2 reflection ENGINE (reflect the Σ_2 statement Sig D [s,s]);
- `lev0_of_forall` — CONTINUITY of the level-0 (≤₁) relation (its `top0` step);
- `lev0_of_le`, `succ_lt_of_lab0` — level-0 algebra.
It does NOT use `exists_lev0_below` — that (the ≤₁-predecessors-of-α-are-cofinal
fact, which itself needs the α ◁₂ β hypothesis) appears ONLY in `reflect_two`.

## VERDICT (this file, leanman-green)
The Σ_2 layer is a CLEAN REDUCTION: reflect_one's level-0 preservation is exactly
[Σ_2 reflection engine] ∘ [≤₁-continuity].  The core-flavored predecessor-cofinality
step (`exists_lev0_below`, needing ◁₂) does NOT appear at Σ_2.  So the term-structural
route STAYS TRACTABLE at Σ_2; the research core is at Σ_3 (reflect_two / M5), which
adds the ◁₂-requiring `exists_lev0_below`.

`Refl1` (the level-1 reflection clause carried by `Tlev 1` in TElem) is realised as
the Σ_2 engine below.  `R0` is the level-0 (≤₁) relation, kept as a parameter with
exactly the ONE property reflect_one needs of it (continuity); the order instance
(`TReflect1_order`) discharges everything from `trio_cofinality`, and the genuinely
structural R0 (trio's row-1 hasParent/domT dominance) plugs the same continuity slot
— establishing that slot is the sole M3→M4 obligation, NOT the Σ_3 core.
-/
import TElem
import TReflect

namespace TRIO
namespace TReflect1

open Three TElem TReflect Classical

/-- **TReflect1 — the reflect_one reduction (single-block essential content).**

`R0` is the level-0 (≤₁) relation.  `hcont` is its CONTINUITY (external
`lev0_of_forall`: `u` relates `R0` to `α` once it relates to every proper `t <o α`
above it).  `hengine` is the Σ_2 reflection's output: a copy `u <o α` for which the
reflected level-0 clause holds cofinally below `α`.  The conclusion — the copy
preserves the level-0 connection to the (now) top `α` — is exactly reflect_one's
`top0` step, and it is JUST continuity applied to the reflected clause.  No
`exists_lev0_below`, no ◁₂. -/
theorem reflect1_step
    (R0 : Three → Three → Prop)
    (hcont : ∀ (u a : Three), u ≤o a → (∀ t, u ≤o t → t <o a → R0 u t) → R0 u a)
    {α : Three}
    (hengine : ∃ u, u <o α ∧ ∀ t, u ≤o t → t <o α → R0 u t) :
    ∃ u, u <o α ∧ R0 u α := by
  obtain ⟨u, huα, hcl⟩ := hengine
  exact ⟨u, huα, hcont u α (Or.inl huα) hcl⟩

/-- The Σ_2 reflection engine, named: `Refl1 R0 α β` says α reflects β's
level-0-preserving copy statement — the trio analog of `Elem 2 α β`.  This is the
`Refl1` clause that `Tlev 1`/`Tlab 1` (TElem) carry; supplying it is the M5/M6
obligation, and it is strictly WEAKER than the Σ_3 core `Refl2` (reflect_two). -/
def Refl1 (R0 : Three → Three → Prop) (α β : Three) : Prop :=
  ∀ y : Three, y <o β → R0 y β →
    ∃ u, u <o α ∧ ∀ t, u ≤o t → t <o α → R0 u t

/-- Assembled reflect_one over `Three`: from the engine `Refl1` + continuity of the
level-0 relation, the copy below α preserves the level-0 connection. -/
theorem TReflect1_of_engine
    (R0 : Three → Three → Prop)
    (hcont : ∀ (u a : Three), u ≤o a → (∀ t, u ≤o t → t <o a → R0 u t) → R0 u a)
    {α β : Three} (hR : Refl1 R0 α β)
    {y : Three} (hy : y <o β) (hyconn : R0 y β) :
    ∃ u, u <o α ∧ R0 u α :=
  reflect1_step R0 hcont (hR y hy hyconn)

/-! ## The level-0 (magnitude / order) instance is FREE.

Taking `R0 = ≤o` (the plain order), continuity is trivial and the engine's copy
is trio's unconditional cofinality (`TReflect0`).  This shows the magnitude-level
connection preservation carries no content — as expected, since trio's Σ_1
reflection is unconditional (`trio_cofinality`).  The genuinely structural `R0`
(trio's row-1 hasParent/domT dominance) plugs the SAME `hcont` slot; whether that
row-1 continuity is free is the lone M3→M4 obligation. -/

/-- Order continuity: trivial (`u ≤o a` is the very hypothesis). -/
theorem ole_cont (u a : Three) (hua : u ≤o a)
    (_ : ∀ t, u ≤o t → t <o a → u ≤o t) : u ≤o a := hua

/-- The order-level TReflect1 is fully green: the magnitude connection is free. -/
theorem TReflect1_order {α : Three}
    (hengine : ∃ u, u <o α ∧ ∀ t, u ≤o t → t <o α → u ≤o t) :
    ∃ u, u <o α ∧ u ≤o α :=
  reflect1_step (fun a b => a ≤o b) ole_cont hengine

/-- And the order-level engine is discharged by trio cofinality: below β = translate M
(a standard form, |M|>1), the fundamental-sequence approximant `translate (M⟦n⟧)`
is a copy `<o α` for α = translate M itself — i.e. the order engine is unconditional.
(Stated at α = β = translate M: the approximant witnesses the engine.) -/
theorem order_engine_of_cofinal {M N : TrioSeq} (hM : ST_TS M) (hN : ST_TS N)
    (hlen : 1 < M.length) (h : translate N <o translate M) :
    ∃ u, u <o translate M ∧ u ≤o translate M := by
  obtain ⟨n, _, _, hlt⟩ := TReflect0 hM hN hlen h
  exact ⟨translate (M⟦n⟧), hlt, Or.inl hlt⟩

end TReflect1
end TRIO
