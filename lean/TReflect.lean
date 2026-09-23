/-
TReflect.lean — M2: the Σ_1 reflection (`TReflect0`), tied to trio's existing,
unconditional Σ_1 machinery. Validates the level-0 architecture of TElem.

External mirror (public): github.com/koteitan/dh-bms-wf-formal, `reflect_zero`
(`Pattern/Reflect.lean`): from a label α ◁₀ β (α is Σ_1-elem in β), a finite
config `y` below β copies to `y'` below α.  Its Σ_1 content is that β is a proper
`<o`-LIMIT: every point below β is captured below a proper predecessor.

Trio ALREADY has this, unconditionally:
- `trio_cofinality` (Core:4602): `translate N <o translate M →
  ∃ n≥1, translate N ≤o translate (M⟦n⟧)`  — the point below β=translate M is
  captured ≤o the fundamental-sequence approximant translate(M⟦n⟧);
- `m_step_decreases` (Decrease.lean): `1<|M| → 1≤n → translate(M⟦n⟧) <o translate M`
  — that approximant is a PROPER predecessor.

So the level-0 reflection needs NO ordinal recursion and NO new content: it is
trio's Bachmann cofinality.  In the TElem framework `Tlev 0 = ≤o` and the
reflection is supplied here, separately — exactly the flat design M1 set up.
-/
import TElem
import Core
import Decrease

namespace TRIO
namespace TReflect

open Three TElem Classical

/-- **TReflect0 — the Σ_1 reflection, unconditional.**

At the term level β = `translate M` (M a standard form of length > 1), every point
γ = `translate N` strictly below β is captured `≤o` a PROPER `<o`-predecessor
`translate (M⟦n⟧)` (a fundamental-sequence approximant, itself `<o β`).  This is
the trio transcription of the external `reflect_zero` at the single-point level,
and it is exactly trio's unconditional Bachmann cofinality
(`trio_cofinality`) sharpened by the proper-descent fact (`m_step_decreases`). -/
theorem TReflect0 {M N : TrioSeq} (hM : ST_TS M) (hN : ST_TS N)
    (hlen : 1 < M.length) (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) ∧ translate (M⟦n⟧) <o translate M := by
  obtain ⟨n, hn, hle⟩ := trio_cofinality hM hN h
  exact ⟨n, hn, hle, m_step_decreases hlen hn⟩

/-- The level-0 relation of the TElem framework (`Tlab _ _ 0 = <o`) reflects via
trio cofinality: this is the Σ_1 reflection property realised on the flat level-0
relation defined in TElem.  (`Refl1 Refl2` are the higher-level reflection
parameters; level 0 does not use them.) -/
theorem Tlab0_reflects (Refl1 Refl2 : Three → Three → Prop)
    {M N : TrioSeq} (hM : ST_TS M) (hN : ST_TS N) (hlen : 1 < M.length)
    (h : Tlab Refl1 Refl2 0 (translate N) (translate M)) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) ∧ translate (M⟦n⟧) <o translate M :=
  TReflect0 hM hN hlen h.1

end TReflect
end TRIO
