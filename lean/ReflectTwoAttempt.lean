/-
ReflectTwoAttempt.lean — RESEARCH scratch (team-lead task): mirror the external
`reflect_two` (Σ_3 finite-pattern reflection) into trio, isolate the residue.

External source (public): github.com/koteitan/dh-bms-wf-formal
  `reflect_two` : from a label `α ◁₂ β` (= α is a Σ_3-elementary substructure of
  the ordinal β), COPY a block y from below β down to y' below α, preserving the
  atomic diagram over params AND the connections-to-top at levels 0 and 1.

Its proof is a 4-step skeleton:
  (i)   build a Σ_3 matrix (∃u ¬∃v ¬∃w) whose clauses say "u copies y, and at
        each level m<2 the connection to the top is witnessed by nested
        cofinal approximants v (level 0) and w (level 1)";
  (ii)  the Σ_3 sentence σ is TRUE at β (witnessed by the original block y);
  (iii) REFLECT σ down to α using the hypothesis `Elem (RN N) 3 α β`  ← THE ENGINE;
  (iv)  cofinal-approximation / continuity: upgrade "connection to a predecessor"
        into "connection to α" via `elem_cofinal` (continuity of ≤_j, j≤2) and
        `exists_lev0_below` (the ≤₁-predecessors of α are cofinal in α).

  Steps (iii) and the level-1,2 parts of (iv) are THEOREMS proved from the
  DEFINITION of the elementary-substructure relation `Elem` (a well-founded
  recursion on the ordinal β).  There is NO induction on the block y or on any
  notation term — the only recursion is on the ordinal β itself.

TRIO TARGET.  The trio transcription of `reflect_two`'s conclusion (copy a
higher-level block down to a lower position preserving the parent/revive
connections at levels 0,1,2) IS the open core `Subst1gReviveSelf` (Wtower2).
This file records, with leanman-checked Lean:

  (A) what PORTS: the level-0 (Σ_1) half of step (iv) — trio's UNCONDITIONAL
      `trio_cofinality` is exactly the cofinal-approximation on the level-0
      order `translate <o`.  GREEN.
  (B) what the notation-induction already gives: `end_subst_of_revive` is the
      Buchholz-style recursion on the BLOCK's W-datum; it factors everything
      EXCEPT the revive residue `Subst1gRevive`.  GREEN (as a reduction).
  (C) the residue: the exact stuck goal that mirrors `reflect_two` step (iii),
      with NO reflection hypothesis available to discharge it (trace_state).
-/
import Wtower2
import Core

namespace TRIO
namespace ReflectTwoAttempt

open Wset Three Classical

/-! ## (A) The level-0 (Σ_1) half of step (iv) PORTS: `trio_cofinality`.

`reflect_two` step (iv) needs, at level 0, exactly: "a point below the top is
approximated by a fundamental-sequence predecessor".  Trio has this
UNCONDITIONALLY.  This is the P4'/P7' analog RESTRICTED to level 0 (the `≤`
relation): the cofinal-approximation on `translate <o`.  It is the whole of what
transfers — trio has no level-1 / level-2 analog (see (C)). -/
theorem trioReflect_step_iv_level0
    {M N : TrioSeq} (hM : ST_TS M) (hN : ST_TS N)
    (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) :=
  trio_cofinality hM hN h

/-! ## (B) The notation-induction on the block's datum already exists.

`end_subst_of_revive` IS the "prove the copy by recursion on the block C's
W-datum" that the syntactic route calls for.  Its statement takes `Subst1gRevive`
as a HYPOTHESIS: the block recursion discharges every case EXCEPT the one where
C's trailing orphan is revived by the CONTEXT.  So the notation induction has
been carried out, and its irreducible leftover is precisely the revive residue.

The type below is the honest record of that fact (no new proof; we alias the
existing theorem so this file's `#check` pins the shape). -/
theorem notation_induction_leaves_revive (hrev : Subst1gRevive) {u : ℕ} {S : TrioSeq}
    (hS : S ∈ W u) (hSne : S ≠ []) :
    ∀ C : TrioSeq, C ∈ W (lev S (S.length - 1)) → C ≠ [] →
      entry C 0 0 = entry S 0 (S.length - 1) →
      (∀ q ∈ C, entry S 0 (S.length - 1) ≤ q.1) →
      (S.dropLast ++ C) ∈ W u :=
  end_subst_of_revive hrev hS hSne

/-! ## (C) The residue = `reflect_two` step (iii) with no reflection hypothesis.

`Subst1gReviveSelf` is the trio transcription of `reflect_two`'s conclusion:
substitute a Wself block `C` (of level `lev C 0 ≤ lev S p`) at position `p` into
`S ∈ Wself`, preserving the parent/revive structure, and land back in `Wself`.

The clauses map to `reflect_two` as:
  `S ∈ Wself`                      ↔ the ambient labelled structure below β
  `C ∈ Wself`, `lev C 0 ≤ lev S p` ↔ the block y with `α ≤ y_i < β` at its level
  `entry C 0 0 = entry S 0 p`,
  `(∀ q ∈ C, entry S 0 p ≤ q.1)`   ↔ the params/anchoring (`X ⊂ α`, `SameBits`)
  the `hasParent … / disjunction` ↔ the connections-to-top clauses (c),(d)
  goal `… ∈ Wself`                 ↔ the copy y' exists below α with those clauses

Attempting the 4-step skeleton: steps (i),(ii) (build+truth of the matrix) and
step (iv) LEVEL 0 all have trio analogs (part (A)).  But step (iii) needs to
TRANSFER the level-1,2 connection down across the substitution, and its input
`Elem (RN N) 3 α β` (α is Σ_3-elem in β) has NO trio analog: trio's only
cross-position comparison is `translate <o` (`Rst`), which is level-0 (Σ_1) and
FLATTENS the subscript to a pair of ℕ (`P a1 a2 …`), so it cannot even state
"the block at p is a Σ_3-elementary substructure of the top".  `trio_cofinality`
fires only for that level-0 order; the level-1,2 clauses `lev0_of_le`,
`exists_lev0_below`, `elem_cofinal (j=2)` have nothing to fire on.

The `trace_state` below prints the exact goal that survives: the Wself-membership
of the substituted sequence, i.e. reflect_two's "copy exists below α" conclusion,
with the hypotheses providing only the level-0 data.  This is the irreducible
residue.  (Single documented `sorry`.) -/
theorem reflect_two_trio_stuck : Subst1gReviveSelf := by
  intro p S C hS hp hCne hCself hClev hhead hdeep hRp hdisj hz2
  -- what ports (level 0): translate is monotone under the substitution, so it
  -- gives NO strictly-decreasing measure across the cross-level revive.
  -- what is needed (step iii): a Σ_3 reflection transferring the level-1,2
  -- connection down to the substituted position — ABSENT in trio.
  trace_state
  sorry

/-- Pin the shape of the external engine's trio counterpart-that-does-not-exist:
    the level-0 order is all trio can compare with. -/
example {a b : TrioSeq} (h : translate a <o translate b) : translate a <o translate b := h

end ReflectTwoAttempt
end TRIO
