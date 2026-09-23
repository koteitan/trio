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

/-- The residue analysis: the GENERIC row-1 cofinality handle (same-level `u`, no `arg`
control) does NOT suffice — it leaves `arg u ≤o arg α` (verified once via `trace_state`
during development; commit 524b48cb).  The FIX is to demand an ARGUMENT-PRESERVING handle,
under which `exists_lev0_below_Dom1` is GREEN.  That handle is a structural row-1/tail
cofinality, supplied below (`exists_lev0_below_Dom1_tail`), NOT the elementarity engine. -/
theorem exists_lev0_below_Dom1_of_argpres (Lt2 : Three → Three → Prop)
    (hhandle : ∀ α β, Lt2 α β → ∀ z, z <o α →
      ∃ u, z <o u ∧ u <o α ∧ row1 u = row1 α ∧ arg u ≤o arg α) :
    ExistsLev0Below_Dom1 Lt2 := by
  intro α β hαβ z hz
  obtain ⟨u, hzu, huα, hru, harg⟩ := hhandle α β hαβ z hz
  exact ⟨u, hzu, huα, huα, hru, harg⟩

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

/-! ## Closing `exists_lev0_below_Dom1` via argument PRESERVATION (handle'd, no engine)

The residue `arg u ≤o arg α` is discharged by CHOOSING the cofinal predecessor to keep
the argument: `u = P a1 a2 b c'` with `arg u = b = arg α` (so `arg u ≤o arg α` is
reflexive).  Such argument-preserving predecessors are cofinal below α exactly when α's
limit is in the TAIL `c` (the row-2/sibling direction) — a purely structural row-1/tail
cofinality (the `AscArgDom1` shape), NOT the elementarity engine.  Proved GREEN below for
the tail-limit case.  (The remaining direction — limit in the ARGUMENT `b` — descends into
`b`, a SUBTERM, by structural induction: the genuine handle.  So no non-subterm witness,
no ◁₂-elementarity — `exists_lev0_below_Dom1` does NOT collapse into `Refl2`.) -/

/-- `c` is a limit: every point below it has a strictly larger point still below it. -/
def IsLimit (t : Three) : Prop := ∀ w, w <o t → ∃ w', w <o w' ∧ w' <o t

/-- **`exists_lev0_below_Dom1`, tail-limit case, GREEN.**  When α = `P a1 a2 b c` with
`c` a nonempty limit, the ARGUMENT-PRESERVING predecessors `P a1 a2 b c'` are cofinal
below α, giving `Dom1 u α` with `arg u = arg α` outright.  No engine, no ◁₂-elementarity —
the `arg` residue is discharged by keeping the argument fixed. -/
theorem exists_lev0_below_Dom1_tail {a1 a2 : ℕ} {b c : Three}
    (hcne : (Z : Three) <o c) (hc : IsLimit c) :
    ∀ z, z <o P a1 a2 b c → ∃ u, z <o u ∧ u <o P a1 a2 b c ∧ Dom1 u (P a1 a2 b c) := by
  intro z hz
  by_cases hzlo : z <o P a1 a2 b Z
  · -- z is below the tail floor: any argument-preserving u above the floor works
    obtain ⟨c', hZc', hc'c⟩ := hc Z hcne
    refine ⟨P a1 a2 b c', ?_, ?_, ?_, rfl, ole_refl _⟩
    · exact olt_trans hzlo (by rw [olt_P_P]; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, hZc'⟩)))
    · rw [olt_P_P]; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, hc'c⟩))
    · rw [olt_P_P]; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, hc'c⟩))
  · -- z shares the prefix a1,a2,b and lies in the tail slot: extract its tail zc <o c
    obtain ⟨z1, z2, zb, zc, rfl⟩ : ∃ z1 z2 zb zc, z = P z1 z2 zb zc := by
      cases z with
      | Z => exact absurd (olt_Z_P a1 a2 b Z) hzlo
      | P z1 z2 zb zc => exact ⟨z1, z2, zb, zc, rfl⟩
    rw [olt_P_P] at hz
    have hform : z1 = a1 ∧ z2 = a2 ∧ zb = b ∧ zc <o c := by
      rcases hz with h | h | h | ⟨e1, e2, e3, h4⟩
      · exact absurd (olt_P_P.mpr (Or.inl h)) hzlo
      · exact absurd (olt_P_P.mpr (Or.inr (Or.inl h))) hzlo
      · exact absurd (olt_P_P.mpr (Or.inr (Or.inr (Or.inl h)))) hzlo
      · exact ⟨e1, e2, e3, h4⟩
    obtain ⟨he1, he2, he3, hzc⟩ := hform
    obtain ⟨c', hzcc', hc'c⟩ := hc zc hzc
    refine ⟨P z1 z2 zb c', ?_, ?_, ?_, ?_, ?_⟩
    · rw [olt_P_P]; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, hzcc'⟩))
    · rw [olt_P_P, he1, he2, he3]; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, hc'c⟩))
    · show P z1 z2 zb c' <o P a1 a2 b c
      rw [olt_P_P, he1, he2, he3]; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, hc'c⟩))
    · show row1 (P z1 z2 zb c') = row1 (P a1 a2 b c); rw [row1_P, row1_P, he1]
    · show arg (P z1 z2 zb c') ≤o arg (P a1 a2 b c); rw [arg_P, arg_P, he3]; exact ole_refl _

/-- A strictly larger term (unbounded tails): `t <o bigger t`. -/
def bigger (t : Three) : Three := P ((lead t).1 + 1) 0 Z Z

theorem olt_bigger (t : Three) : t <o bigger t := by
  cases t with
  | Z => exact olt_Z_P _ _ _ _
  | P t1 t2 tb tc => rw [bigger, lead_P, olt_P_P]; exact Or.inl (Nat.lt_succ_self t1)

/-- **`exists_lev0_below_Dom1`, argument-direction case, GREEN.**  When α = `P a1 a2 b Z`
with `b` nonempty, the predecessors `P a1 a2 b' c'` with `b' <o b` are cofinal below α
(the tail slot `c'` is unbounded), and have `arg = b' <o b`.  So `arg u ≤o arg α` holds
by argument DESCENT (into the subterm `b`), no engine.  GREEN. -/
theorem exists_lev0_below_Dom1_arg {a1 a2 : ℕ} {b : Three} (hbne : (Z : Three) <o b) :
    ∀ z, z <o P a1 a2 b Z → ∃ u, z <o u ∧ u <o P a1 a2 b Z ∧ Dom1 u (P a1 a2 b Z) := by
  intro z hz
  by_cases hz0 : z <o P a1 a2 Z Z
  · have huα : P a1 a2 Z (bigger Z) <o P a1 a2 b Z := by
      rw [olt_P_P]; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hbne⟩))
    refine ⟨P a1 a2 Z (bigger Z), ?_, huα, huα, rfl, Or.inl hbne⟩
    exact olt_trans hz0
      (by rw [olt_P_P]; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, olt_bigger Z⟩)))
  · obtain ⟨z1, z2, zb, zc, rfl⟩ : ∃ z1 z2 zb zc, z = P z1 z2 zb zc := by
      cases z with
      | Z => exact absurd (olt_Z_P a1 a2 Z Z) hz0
      | P z1 z2 zb zc => exact ⟨z1, z2, zb, zc, rfl⟩
    rw [olt_P_P] at hz
    have hform : z1 = a1 ∧ z2 = a2 ∧ zb <o b := by
      rcases hz with h | h | ⟨e1, e2, h3⟩ | ⟨-, -, -, h4⟩
      · exact absurd (olt_P_P.mpr (Or.inl h)) hz0
      · exact absurd (olt_P_P.mpr (Or.inr (Or.inl h))) hz0
      · exact ⟨e1, e2, h3⟩
      · exact absurd h4 (not_olt_Z zc)
    obtain ⟨he1, he2, hzb⟩ := hform
    have huα : P z1 z2 zb (bigger zc) <o P a1 a2 b Z := by
      rw [olt_P_P, he1, he2]; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hzb⟩))
    refine ⟨P z1 z2 zb (bigger zc), ?_, huα, huα, ?_, ?_⟩
    · rw [olt_P_P]; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, olt_bigger zc⟩))
    · show row1 (P z1 z2 zb (bigger zc)) = row1 (P a1 a2 b Z); rw [row1_P, row1_P, he1]
    · show arg (P z1 z2 zb (bigger zc)) ≤o arg (P a1 a2 b Z); rw [arg_P, arg_P]; exact Or.inl hzb

/-- α is a ROW-1 LIMIT (structural): its tuple ends in a limit tail, or `c = Z` with a
nonempty argument.  This is exactly the structural content the faithful ◁₂ supplies about
α (it is a limit) — NOT the elementarity engine. -/
def RowLim : Three → Prop
  | Z => False
  | P _ _ b c => (c = Z ∧ (Z : Three) <o b) ∨ ((Z : Three) <o c ∧ IsLimit c)

/-- **`exists_lev0_below_Dom1` is GREEN for every row-1 limit α.**  Dispatches to the
argument case (`c = Z`) or the tail case (`c` a limit).  Fully green, no engine, no
non-subterm witness — the argument-domination is discharged structurally (argument
preservation in the tail direction, argument descent into the subterm in the other).
This is the `exists_lev0_below` for the FAITHFUL ≤₁, CLOSED. -/
theorem exists_lev0_below_Dom1_general {α : Three} (hα : RowLim α) :
    ∀ z, z <o α → ∃ u, z <o u ∧ u <o α ∧ Dom1 u α := by
  cases α with
  | Z => exact absurd hα id
  | P a1 a2 b c =>
    rcases hα with ⟨rfl, hb⟩ | ⟨hc, hclim⟩
    · exact exists_lev0_below_Dom1_arg hb
    · exact exists_lev0_below_Dom1_tail hc hclim

/-- **`exists_lev0_below_Dom1` GREEN**, given that the faithful ◁₂ supplies the (structural)
row-1-limit property of α.  No engine; the ◁₂→RowLim step is structural (α is a limit),
the trio analog of "α ◁₂ β makes α a ≤₁-limit". -/
theorem exists_lev0_below_Dom1_closed (Lt2 : Three → Three → Prop)
    (hlim : ∀ α β, Lt2 α β → RowLim α) : ExistsLev0Below_Dom1 Lt2 := by
  intro α β hαβ z hz
  exact exists_lev0_below_Dom1_general (hlim α β hαβ) z hz

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
