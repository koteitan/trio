/-
TElem.lean — M1: syntactic level relations on the `Three` notation (Term.lean:16),
for the option-1 syntactic Σ_3 reflection (see TElem-design.md).

External mirror (public): github.com/koteitan/dh-bms-wf-formal, `Pattern/Basic.lean`.
There the relations `a ≤_{j+1} b` (= α is a Σ_{j+1}-elementary substructure of β)
are defined by WELL-FOUNDED RECURSION ON THE ORDINAL β (`RFix`, via
`wellFounded_lt (Ordinal)`): `α ≤_{j+1} β` consults `≤_{k+1}` only at pairs whose
top is `< β` in the order.

## THE GROUNDING CRUX (addressed explicitly — see `grounding` section below)
Going syntactic, we must ground WITHOUT set-theoretic ordinals. The obstruction,
made concrete here in Lean:

  The order `olt` (`<o`, Term.lean:26) does NOT respect structural size.  For ANY
  term `t`, `P 0 0 t t <o P 1 0 Z Z` (leading pair (0,0) <lex (1,0)), so the
  `<o`-predecessors of the FIXED term `P 1 0 Z Z` are structurally UNBOUNDED
  (`olt_pred_size_unbounded`).  Hence there is NO structural-subterm/size measure
  `μ` with `b <o β → μ b < μ β`; any such `μ` is an olt-monotone map into a
  well-order, i.e. a proof that `olt` is well-founded on `Three` — which (via
  `translate`) implies `Rst` well-founded implies trio termination = the GOAL.

  ⇒ The mirrored `Elem`/`RFix` recursion (global quantification over the
    `<o`-predecessors of β) CANNOT be grounded structurally "for free": doing so
    is provably ≥ the termination goal.  This is a genuine finding, not a defect
    of effort.

  RESOLUTION (Buchholz's method, and why option 1 is still viable): the ORDER
  `olt` itself IS already structurally grounded — it recurses only into the
  subterms `b, c` (Lean accepts its definition).  What is not structural is the
  *global-predecessor* elementarity of the external proof.  So we do NOT mirror
  `Elem` as a predecessor-quantified recursion.  Instead:
   - level 0 (Σ_1) = the order `≤o` itself, with reflection supplied SEPARATELY by
     trio's existing, unconditional `trio_cofinality` (Core:4602) — no recursion;
   - levels 1,2 (Σ_2, Σ_3) carry the extra reflection as a NAMED PROPERTY on top
     of the order (`TReflectN`, built in TReflect.lean by structural work on the
     `Three` terms + cofinality), NOT as an ordinal recursion.
  The relations below are therefore all FLAT over the order (no self-referential
  recursion), so they are well-defined for free; the content moves to TReflect.
-/
import Term
import Core

namespace TRIO
namespace TElem

open Three Classical

/-! ## Grounding obstruction (concrete, leanman-green) -/

/-- Structural size of a `Three` term (node count). -/
def tsize : Three → ℕ
  | Z => 0
  | P _ _ b c => 1 + tsize b + tsize c

/-- For ANY term `t`, `P 0 0 t t` is `<o` the fixed term `P 1 0 Z Z`
(leading pair `(0,0) <lex (1,0)`), regardless of `t`. -/
theorem olt_pred_any (t : Three) : P 0 0 t t <o P 1 0 Z Z := by
  simp only [olt_P_P]
  exact Or.inl Nat.one_pos

/-- A depth-`n` witness term, of structural size `n`. -/
def chain : ℕ → Three
  | 0 => Z
  | n + 1 => P 0 0 (chain n) Z

@[simp] theorem tsize_chain (n : ℕ) : tsize (chain n) = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [chain, tsize, ih]; omega

/-- **The obstruction.**  The `<o`-predecessors of the FIXED term `P 1 0 Z Z`
have UNBOUNDED structural size.  So no structural/size measure can bound the
predecessors — the mirrored elementarity recursion cannot be grounded
structurally (see the header). -/
theorem olt_pred_size_unbounded :
    ∀ n : ℕ, ∃ t : Three, t <o P 1 0 Z Z ∧ n < tsize t := by
  intro n
  refine ⟨P 0 0 (chain (n + 1)) (chain (n + 1)), olt_pred_any _, ?_⟩
  simp [tsize]; omega

/-! ## `ole` is a preorder (order algebra we DO have, structurally) -/

theorem ole_refl (a : Three) : a ≤o a := Or.inr rfl

theorem ole_trans {a b c : Three} (hab : a ≤o b) (hbc : b ≤o c) : a ≤o c := by
  rcases hab with h | rfl
  · exact Or.inl (olt_ole_trans h hbc)
  · exact hbc

theorem olt_of_olt_ole {a b c : Three} (hab : a <o b) (hbc : b ≤o c) : a <o c :=
  olt_ole_trans hab hbc

theorem ole_olt_trans {a b c : Three} (hab : a ≤o b) (hbc : b <o c) : a <o c := by
  rcases hab with h | rfl
  · exact olt_trans h hbc
  · exact hbc

/-! ## The three level relations (r = 3), FLAT over the order.

`Tlev j` = "`a ≤_{j+1} b`", `Tlab j` = "`a <_{j+1} b`".  Level 0 is the order.
Levels 1,2 add a reflection property `Refl1/Refl2 : Three → Three → Prop` supplied
later (TReflect.lean); here they are parameters so the algebra (refl/trans/mono)
is proved once, uniformly, and independently of how the reflection is realised.
This is the point of the flat design: NO predecessor-recursion, so no grounding
debt at the definition level. -/

variable (Refl1 Refl2 : Three → Three → Prop)

/-- `a ≤_{j+1} b`. -/
def Tlev : ℕ → Three → Three → Prop
  | 0 => fun a b => a ≤o b
  | 1 => fun a b => a ≤o b ∧ Refl1 a b
  | 2 => fun a b => a ≤o b ∧ Refl1 a b ∧ Refl2 a b
  | _ + 3 => fun _ _ => False

/-- `a <_{j+1} b`. -/
def Tlab (j : ℕ) (a b : Three) : Prop := a <o b ∧ Tlev Refl1 Refl2 j a b

theorem Tlev_le {j : ℕ} {a b : Three} (h : Tlev Refl1 Refl2 j a b) : a ≤o b := by
  match j, h with
  | 0, h => exact h
  | 1, h => exact h.1
  | 2, h => exact h.1

theorem Tlab_lt {j : ℕ} {a b : Three} (h : Tlab Refl1 Refl2 j a b) : a <o b := h.1

/-- Level-0 reflexivity. -/
theorem Tlev0_refl (a : Three) : Tlev Refl1 Refl2 0 a a := ole_refl a

/-- Downward monotonicity in the level: `≤_{j'+1}` ⇒ `≤_{j+1}` for `j ≤ j'`
(drop the higher reflection clauses). -/
theorem Tlev_mono {j j' : ℕ} (hjj' : j ≤ j') {a b : Three}
    (h : Tlev Refl1 Refl2 j' a b) : Tlev Refl1 Refl2 j a b := by
  match j', h with
  | 0, h =>
    obtain rfl : j = 0 := Nat.le_zero.mp hjj'
    exact h
  | 1, h =>
    match j, hjj' with
    | 0, _ => exact h.1
    | 1, _ => exact h
  | 2, h =>
    match j, hjj' with
    | 0, _ => exact h.1
    | 1, _ => exact ⟨h.1, h.2.1⟩
    | 2, _ => exact h
  | (n + 3), h => exact h.elim

theorem Tlab_mono {j j' : ℕ} (hjj' : j ≤ j') {a b : Three}
    (h : Tlab Refl1 Refl2 j' a b) : Tlab Refl1 Refl2 j a b :=
  ⟨h.1, Tlev_mono Refl1 Refl2 hjj' h.2⟩

end TElem
end TRIO
