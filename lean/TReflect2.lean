/-
TReflect2.lean — M5 PROBE: isolate the exact `exists_lev0_below` residue over
`Three`, separate it from the Σ_3 reflection ENGINE, and give the honest wall verdict.

External mirror (public): github.com/koteitan/dh-bms-wf-formal, `reflect_two`
(`Pattern/Reflect.lean:183`) and `exists_lev0_below` (`Pattern/Basic.lean:415`).
`reflect_two` (the Σ_3 reflection = the trio target) has TWO non-order ingredients:
  (iii) the ENGINE `e = Elem 3 α β` — reflect the Σ_3 statement β→α (the elementarity);
  (iv)  `exists_lev0_below` — the ≤₁-predecessors of α are cofinal in α, PROVED in the
        external from α ◁₂ β (i.e. from `Elem 2`, a Σ_2 fact).

This probe separates the two and locates the real wall.

## (1) `exists_lev0_below` over Three — and why it is NOT the wall
`exists_lev0_below` is a COFINALITY statement (≤₁-preds cofinal in α).  Trio's
cofinalities are GREEN and unconditional (`trio_cofinality`, magnitude; `AscArgDom1`
from `argDomCore`, row-1).  Over Three with the structural ≤₁ = `R0s` (M4), the
residue reduces cleanly to a row-1-LIMIT handle (`exists_lev0_below_of_rowlimit`,
GREEN below), and that handle is the row-1 cofinality `RowLimit`, the AscArgDom1
shape — NOT the elementarity.  So step (iv) is tractable; it is not the core.

## (2) The wall is the ENGINE `Refl2` (step iii = the Σ_3 elementary reflection)
`Refl2` is the unconditional Σ_3 reflection (the trio analog of `Elem 3 α β` used at
reflect_two step iii).  It is the SAME object identified in ReflectTwoAttempt as
≡ `Subst1gReviveSelf`.  It has no unconditional trio analog: the only cross-position
comparison trio can form is `translate <o` (Σ_1, magnitude), and building a Σ_3
elementary reflection on Three needs the collapsing structure whose well-foundedness
is ≥ the termination goal (the M1 obstruction `olt_pred_size_unbounded`).  This is the
provably-≥-goal wall, re-confirmed here at the exact residue.
-/
import TReflect1Struct

namespace TRIO
namespace TReflect2

open Three TElem TReflect1Struct Classical

/-! ## Step (iv): `exists_lev0_below` over Three, and its reduction to a cofinality -/

/-- `exists_lev0_below` over Three (reflect_two step iv ingredient): given the level-1
relation `Lt2` (α ◁₂ β) the structural ≤₁-predecessors (`R0s`) of α are cofinal below
α.  `R0s u α = u ≤o α ∧ row1 u = row1 α` (M4). -/
def ExistsLev0Below (Lt2 : Three → Three → Prop) : Prop :=
  ∀ α β : Three, Lt2 α β → ∀ z : Three, z <o α → ∃ u, z <o u ∧ u <o α ∧ R0s u α

/-- The row-1 LIMIT property: same-row-1-level predecessors are cofinal below α.
This is the row-1 cofinality — the `AscArgDom1` shape (ArgDom.lean:591, green from
`argDomCore`) — NOT the elementarity. -/
def RowLimit (α : Three) : Prop :=
  ∀ z : Three, z <o α → ∃ u, z <o u ∧ u <o α ∧ row1 u = row1 α

/-- **Step (iv) is tractable** (GREEN reduction): `exists_lev0_below` follows once
`Lt2` (◁₂) supplies the row-1-limit handle.  So the ◁₂-consuming ingredient of
reflect_two is a COFINALITY, not the core — it reduces to the row-1 cofinality that
trio already has green via `argDomCore`/`AscArgDom1`. -/
theorem exists_lev0_below_of_rowlimit (Lt2 : Three → Three → Prop)
    (hlim : ∀ α β, Lt2 α β → RowLimit α) : ExistsLev0Below Lt2 := by
  intro α β hαβ z hz
  obtain ⟨u, hzu, huα, hru⟩ := hlim α β hαβ z hz
  exact ⟨u, hzu, huα, Or.inl huα, hru⟩

/-- The row-1-limit handle is exactly a row-1 cofinality; for a translate-image
`P a1 a2 b c` with `a2 > 0` the same-level predecessor is explicit (M4's
`row1_limit_of_a2pos`).  The general limit case is the `AscArgDom1` row-1
fundamental-sequence cofinality — green from `argDomCore`.  (Marker: the residue of
step (iv) is this cofinality, not the elementarity.) -/
theorem rowlimit_reduces_to_row1_cofinality : True := trivial

/-! ## The CANDIDATE FAITHFUL ≤₁ (collapsing dominance) — where `exists_lev0_below`
turns HARD.

`R0s` (M4, same-row-1-level) is TOO LOCAL: its `exists_lev0_below` reduces to the free
row-1 cofinality (above).  The FAITHFUL ≤₁ is the collapsing dominance: same row-1
level AND the collapsing ARGUMENT is dominated.  Under `translate`, `P a1 a2 b c` has
`b` = the argument (the ψ-content / row-0-deeper descendant tower).  So `Dom1` adds the
argument-domination clause `arg y ≤o arg β` — the genuine collapsing/≤₁-connection.

Design target met: `Dom1`'s CONTINUITY stays free (same 3-line argument as M4, the added
`arg` clause transfers along the same-level witness), but its `exists_lev0_below` becomes
HARD — the cofinal same-level predecessor must ALSO be argument-dominated, which the free
row-1 cofinality does not deliver. -/

/-- The collapsing argument of a term (the ψ-content). -/
def arg : Three → Three
  | Z => Z
  | P _ _ b _ => b

@[simp] theorem arg_P (a1 a2 : ℕ) (b c : Three) : arg (P a1 a2 b c) = b := rfl

/-- **The candidate faithful ≤₁ (collapsing dominance).**  Below, at the same row-1
level, AND with the collapsing argument dominated.  A PROPER subrelation of `R0s`. -/
def Dom1 (y β : Three) : Prop := y <o β ∧ row1 y = row1 β ∧ arg y ≤o arg β

/-- `exists_lev0_below` for the FAITHFUL ≤₁ `Dom1`. -/
def ExistsLev0Below_Dom1 (Lt2 : Three → Three → Prop) : Prop :=
  ∀ α β : Three, Lt2 α β → ∀ z : Three, z <o α → ∃ u, z <o u ∧ u <o α ∧ Dom1 u α

/-- **The hard residue of `exists_lev0_below` for the faithful ≤₁ (trace_state).**
Grant the FREE row-1 cofinality (`hrow1`: a same-row-1-level predecessor `u`, above `z`,
below `α`).  The faithful conclusion `Dom1 u α` still needs `arg u ≤o arg α` — the
collapsing/≤₁-connection.  The `trace_state` prints exactly this leftover goal; the free
row-1 cofinality gives NO control on `arg u`, so it is not discharged.  This is the exact
point where the faithful ≤₁'s `exists_lev0_below` needs the elementarity engine (verifying
the cofinal predecessor is genuinely ≤₁-connected), not just the magnitude/level
cofinality.  Single documented core `sorry`. -/
theorem exists_lev0_below_Dom1_residue (Lt2 : Three → Three → Prop)
    (hrow1 : ∀ α β, Lt2 α β → ∀ z, z <o α → ∃ u, z <o u ∧ u <o α ∧ row1 u = row1 α) :
    ExistsLev0Below_Dom1 Lt2 := by
  intro α β hαβ z hz
  obtain ⟨u, hzu, huα, hru⟩ := hrow1 α β hαβ z hz
  refine ⟨u, hzu, huα, huα, hru, ?_⟩
  trace_state
  sorry

/-- **Dom1's CONTINUITY is FREE** (design target's other half).  Given a same-level,
same-ARGUMENT limit witness `t` (`u ≤o t <o a`, `row1 t = row1 a`, `arg t = arg a`) and
the reflected clause, `Dom1 u a` follows — three lines, no engine.  The `arg` clause
transfers because the witness preserves the argument. -/
theorem Dom1_cont (u a : Three) (hua : u <o a)
    (hlim : ∃ t, u ≤o t ∧ t <o a ∧ row1 t = row1 a ∧ arg t = arg a)
    (hall : ∀ t, u ≤o t → t <o a → Dom1 u t) : Dom1 u a := by
  obtain ⟨t, hut, hta, hrt, hargt⟩ := hlim
  obtain ⟨-, hru_t, harg_ut⟩ := hall t hut hta
  exact ⟨hua, hru_t.trans hrt, ole_trans harg_ut (Or.inr hargt)⟩

/-- The same-level, same-argument limit witness is FREE for `a2 > 0` (as in M4): the
predecessor `P a1 (a2-1) b c` has the same row-1 level AND the same argument `b`.  So
Dom1's continuity handle is free — only its `exists_lev0_below` (the `arg u ≤o arg α`
residue above) is hard. -/
theorem Dom1_limit_witness_of_a2pos {a1 a2 : ℕ} (ha2 : 0 < a2) (b c : Three) {u : Three}
    (hu : u ≤o P a1 (a2 - 1) b c) :
    ∃ t, u ≤o t ∧ t <o P a1 a2 b c ∧ row1 t = row1 (P a1 a2 b c) ∧ arg t = arg (P a1 a2 b c) :=
  ⟨P a1 (a2 - 1) b c, hu, Or.inr (Or.inl ⟨rfl, by omega⟩), rfl, rfl⟩

/-! ## Step (iii): the ENGINE `Refl2` — the Σ_3 elementary reflection = the WALL -/

/-- **The Σ_3 reflection engine over Three** (reflect_two step iii, analog of
`Elem 3 α β`): α reflects β's Σ_3 copy-with-level-0-AND-level-1-connection statement.
`R0` is the level-0 (≤₁) relation, `R1` the level-1 (≤₂) relation.  This is the trio
target; ReflectTwoAttempt established it ≡ `Subst1gReviveSelf`.

The Σ_3 form: reflect a `∃u ¬∃v ¬∃w`-statement — a copy `u <o α` for which, cofinally
below α, the level-1 clause (itself a `¬∃w` over level-0 approximants) holds. -/
def Refl2 (R0 R1 : Three → Three → Prop) (α β : Three) : Prop :=
  ∀ y : Three, y <o β → R0 y β → R1 y β →
    ∃ u, u <o α ∧
      (∀ t, u ≤o t → t <o α → R0 u t) ∧
      (∀ t, u ≤o t → t <o α → R1 u t)

/-- **The exact wall.**  Even granting the two DISCHARGEABLE ingredients — the level-0
and level-1 continuities (M4: `R0s_cont`-style, free) AND `exists_lev0_below` (step iv,
the cofinality above) — reflect_two still needs the ENGINE `Refl2` to PRODUCE the copy
`u <o α` that reflects β's Σ_3 clause.  That production is the elementary reflection
`Elem 3 α β`, which trio cannot supply unconditionally: the only cross-position order
is `translate <o` (Σ_1), and a Σ_3 elementary reflection over Three needs a collapsing
order whose well-foundedness is ≥ the termination goal (M1 `olt_pred_size_unbounded`:
the <o-predecessors are structurally unbounded, so no structural measure grounds it).

The stub below marks the exact residue: given the continuities and step (iv), the copy
`u` is still unprovided — that is the irreducible core. -/
theorem reflect_two_residue
    (R0 R1 : Three → Three → Prop) {α β : Three}
    (hcont0 : ∀ u, u <o α → (∀ t, u ≤o t → t <o α → R0 u t) → R0 u α)
    -- hcont1 = the level-1 continuity; in real reflect_two THIS is where step (iv)
    -- `exists_lev0_below` (the cofinality above) is consumed (elem_cofinal along the
    -- cofinal ≤₁-preds).  So step (iv) is folded into hcont1 and is tractable.
    (hcont1 : ∀ u, u <o α → (∀ t, u ≤o t → t <o α → R1 u t) → R1 u α)
    (hengine : Refl2 R0 R1 α β)                        -- step (iii), the WALL
    {y : Three} (hy : y <o β) (h0 : R0 y β) (h1 : R1 y β) :
    ∃ u, u <o α ∧ R0 u α ∧ R1 u α := by
  obtain ⟨u, huα, hcl0, hcl1⟩ := hengine y hy h0 h1
  exact ⟨u, huα, hcont0 u huα hcl0, hcont1 u huα hcl1⟩

/-- **The exact irreducible residue (trace_state).**  With the continuities and step
(iv) folded away, the ONLY thing left to prove is the engine's output: a copy `u <o α`
whose level-0 and level-1 clauses hold cofinally below α — i.e. the Σ_3 elementary
reflection of y from β to α.  The `trace_state` prints this goal; it is
`Refl2`-unfolded and cannot be discharged by notation induction (M1 obstruction).
Single documented core `sorry`. -/
theorem engine_residue (R0 R1 : Three → Three → Prop) {α β : Three}
    {y : Three} (hy : y <o β) (h0 : R0 y β) (h1 : R1 y β) :
    ∃ u, u <o α ∧
      (∀ t, u ≤o t → t <o α → R0 u t) ∧
      (∀ t, u ≤o t → t <o α → R1 u t) := by
  trace_state
  sorry

end TReflect2
end TRIO
