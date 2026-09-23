/-
TReflect1Struct.lean — M4: the STRUCTURAL row-1 level-0 relation `R0` and its
continuity `hcont`, testing whether the core sneaks into Σ_2.

External mirror (public): github.com/koteitan/dh-bms-wf-formal.  There ≤₁ is a
genuine PROPER subrelation of ≤ (Σ_1-elementarity), and its continuity
`lev0_of_forall` (Basic.lean:298) is proved from `elem_cofinal` + succ-closure
(`succ_lt_of_lab0`, from α ◁₁ β) — it does NOT use `exists_lev0_below` (the
◁₂-requiring ≤₁-predecessors-cofinal fact, which lives only in reflect_two).

## CRITICAL CORRECTION to M3
M3's concrete `Refl1` used ≤₁ = ≤o (the order).  That is DEGENERATE and NOT
faithful: if ≤₁ = ≤o then `exists_lev0_below` ("≤₁-preds of α cofinal in α")
becomes exactly `trio_cofinality` (FREE), which would make reflect_two free and
trivialise the open core `Subst1gReviveSelf`.  Since the core is genuinely open,
≤₁ MUST be a PROPER subrelation of ≤o.  So M4's structural R0 is genuinely needed,
and M3's "Σ_2 free" holds only for the degenerate label system — the faithful
statement requires this file.

## The structural row-1 relation
Under `translate` a term `P a1 a2 b c` has `a1 = row1` (the ψ-collapsing level),
`b` the argument (row-0-deeper descendants), `c` the sibling tail (Term.lean:138).
The genuine level-0 (≤₁) relation is row-1 structural: `R0 a b := a ≤o b ∧
row1 a = row1 b` — "a sits below b at the SAME row-1 collapsing level".  This is a
proper subrelation of ≤o (it fails whenever a drops to a lower row-1 level), so it
does NOT trivialise the core.

## VERDICT (this file, leanman-green)
The row-1 CONTINUITY is FREE of the core: `R0s_cont` proves `hcont` in three lines
from a row-1-LIMIT witness (a same-level predecessor above `u`, below `a`) + the
reflected clause.  NO `exists_lev0_below`, NO ◁₂, NO wrong-level IH.  The row-1-limit
witness is supplied — for translate-images — by trio's row-1 cofinality apparatus
`AscArgDom1` (ArgDom.lean:591, green from `argDomCore`), the row-1 analog of
`trio_cofinality`; it is NOT `exists_lev0_below`.

So the core does NOT sneak into the continuity: **the continuity mechanism is free,
core stays at Σ_3.**  The one genuine entanglement with M5: pinning the EXACT faithful
≤₁ (so that continuity stays free while `exists_lev0_below` stays hard) is the
collapsing-structure choice, shared with M5 — see the closing note.
-/
import TElem

namespace TRIO
namespace TReflect1Struct

open Three TElem Classical

/-- The row-1 (ψ-collapsing) level of a term. -/
def row1 (t : Three) : ℕ := (lead t).1

@[simp] theorem row1_Z : row1 Z = 0 := rfl
@[simp] theorem row1_P (a1 a2 : ℕ) (b c : Three) : row1 (P a1 a2 b c) = a1 := rfl

/-- **The structural level-0 (≤₁) relation**: below, at the SAME row-1 level.
A PROPER subrelation of `≤o` (it fails when the row-1 level drops), so it does not
trivialise the core. -/
def R0s (a b : Three) : Prop := a ≤o b ∧ row1 a = row1 b

theorem R0s_le {a b : Three} (h : R0s a b) : a ≤o b := h.1

theorem R0s_refl (a : Three) : R0s a a := ⟨ole_refl a, rfl⟩

theorem R0s_trans {a b c : Three} (h1 : R0s a b) (h2 : R0s b c) : R0s a c :=
  ⟨ole_trans h1.1 h2.1, h1.2.trans h2.2⟩

/-- `R0s` is a PROPER subrelation of `≤o`: at a strict row-1 drop it fails though
the order holds.  (Witness: `Z <o P 1 0 Z Z` but `row1 Z = 0 ≠ 1`.) -/
theorem R0s_proper : (Z : Three) ≤o P 1 0 Z Z ∧ ¬ R0s Z (P 1 0 Z Z) := by
  refine ⟨Or.inl (by simp), ?_⟩
  rintro ⟨-, h⟩
  simp at h

/-- **The structural continuity `hcont`, FREE of the core.**  Mirrors external
`lev0_of_forall`: given a row-1-LIMIT witness `t` (a same-row-1-level point with
`u ≤o t <o a`) and the reflected clause (`R0s u` holds at every proper `t' <o a`
above `u`), the level-0 connection `R0s u a` follows.  Three lines, no
`exists_lev0_below`, no ◁₂, no wrong-level IH — the continuity mechanism is free. -/
theorem R0s_cont (u a : Three) (hua : u ≤o a)
    (hlim : ∃ t, u ≤o t ∧ t <o a ∧ row1 t = row1 a)
    (hall : ∀ t, u ≤o t → t <o a → R0s u t) :
    R0s u a := by
  obtain ⟨t, hut, hta, hrt⟩ := hlim
  exact ⟨hua, (hall t hut hta).2.trans hrt⟩

/-- The row-1-limit hypothesis of `R0s_cont` is a LOCAL structural/order fact
("`a` has a same-row-1-level predecessor above `u`"), the shape supplied by trio's
row-1 cofinality `AscArgDom1` (green from `argDomCore`).  It is NOT
`exists_lev0_below` (which needs the ◁₂ hypothesis).  Concretely, any `P a1 a2 b c`
with `a2 > 0` has the same-level predecessor `P a1 (a2-1) b c` below it. -/
theorem row1_limit_of_a2pos {a1 a2 : ℕ} (ha2 : 0 < a2) (b c : Three) {u : Three}
    (hu : u ≤o P a1 (a2 - 1) b c) :
    ∃ t, u ≤o t ∧ t <o P a1 a2 b c ∧ row1 t = row1 (P a1 a2 b c) := by
  exact ⟨P a1 (a2 - 1) b c, hu, Or.inr (Or.inl ⟨rfl, by omega⟩), rfl⟩

end TReflect1Struct
end TRIO
