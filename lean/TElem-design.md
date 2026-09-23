# TElem construction — syntactic Σ_3 reflection for trio (option 1)

## Goal
Prove `psiI ∈ W 0` **unconditionally and syntactically**, by supplying trio's single
open core `Subst1gReviveSelf` (Wtower2.lean:3274 = `CLoadTie` ChildLoadC.lean:131)
with a **syntactic Σ_3 reflection**, built by *structural recursion on the `Three`
notation* — no set-theoretic ordinals (`Ordinal.{0}`).

## Background (why this is the only syntactic route)
The external proof (public: github.com/koteitan/dh-bms-wf-formal) proves BM4
termination for every number of rows via Carlson Σ_N-elementary substructures R_N.
It factors through a `LabelSystem` interface:
- a **combinatorial half** (height-descent + copy lemma C1–C6) — trio already has its
  own equivalent (the whole W-world is green *modulo* the core), so we do NOT port it;
- **two non-syntactic black boxes**: (1) initial labels via an ω₁ closure; (2) the
  `reflect` clause (d).

We established (this session, `ReflectTwoAttempt.lean`, commit ee1d38e5):
**reflect clause (d) ≡ trio's `Subst1gReviveSelf`** — both say "copy a higher-level
block down to a lower position preserving the connections-to-top at each level 0,1,2."
The external side discharges it for r=3 via `reflect_two` (Σ_3 reflection), whose
engine is `Elem (RN N) 3 α β` (α is a Σ_3-elementary substructure of β), defined by
well-founded recursion on the **ordinal** β. Trio has only the Σ_1 half
(`trio_cofinality`/`domT`/`translate <o`, all green); the missing piece is the
**Σ_2/Σ_3 `Elem` relation**. Notation induction on existing trio objects cannot supply
it (the IH lands at the wrong level — see `end_subst_of_revive` residue). So we must
ADD the level-1,2 reflection relation to the notation. That is this construction.

## Key design decision
`Three` (`Term.lean:16`, `Three = Z | P (a1 a2 : ℕ) (b c : Three)`) is an **inductive
type**, so structural recursion on `Three` terms is well-founded for free. We therefore
define the whole `Sig`/`Elem`/`rel`/`lev`/`lab` machinery **on `Three`, by structural
recursion on the term**, mirroring the external `Pattern/Basic.lean` but replacing
`Ordinal.{0}` with `Three` and `wellFounded_lt (Ordinal)` with structural recursion.
This is exactly Buchholz's method (recursion on finite notation terms). The
collapsing-order well-foundedness becomes a *separate theorem* proved via reflection,
not an assumed `wellFounded_lt`.

`Three` is a countable carrier (finite trees, ℕ labels) and — by the project's design
(BMOCF-isomorphic, `translate` the parse) — rich enough to reach ψ(I). The relations
`Trel j` (not the type) carry the collapsing/level structure.

## Architecture (mirror external `Basic.lean` / `General.lean` over `Three`)
Files to create under `lean/` (small, split per `split-lean-file` rule):
- `TElem.lean`   — `TSig`, `TElem j`, `Trel j` (j<3), `Tlev`, `Tlab`; basic props
  (refl/trans/mono; analogs of `rel_iff`, `lev_trans`, `lev_mono`, Basic.lean:176-222).
- `TReflect.lean` — the reflect ladder:
  - `TReflect0` (Σ_1, external `reflect_zero`): copy a finite config below α; ≈ "α is a
    limit". Should connect to trio's existing Σ_1 (`trio_cofinality`/`domT`).
  - `TReflect1` (Σ_2, external `reflect_one`).
  - `TReflect2` (Σ_3, external `reflect_two`) = **the trio target**.
  - `TElem_cofinal` (external `elem_cofinal`, Basic.lean:256, j≤2): continuity along the
    cofinal set — the P4'/P7' analog, proved from `Three`'s collapsing-order cofinality.
- `TWf.lean`     — the collapsing order `<c` on `Three` is well-founded (distinguished-sets
  method, using `TReflect`).  [may fold into the connect step]
- `TSubst.lean`  — discharge `Subst1gReviveSelf` from `TReflect2`; then
  `Cpsi.psiI_mem` → `psiI ∈ W 0` unconditional.

## Milestones (multi-session; COMMIT every 30–60 min — session death loses unsaved work)
- **M1** defs + basic props (`TElem.lean`). Tractable.
- **M2** `TReflect0` (Σ_1) end-to-end, tied to trio's existing Σ_1. Tractable; **validates
  the architecture** — do this fully before M5.
- **M3** `TReflect1` (Σ_2). Harder.
- **M4** `TElem_cofinal` (continuity). Research.
- **M5** `TReflect2` (Σ_3) = the research core.
- **M6** discharge `Subst1gReviveSelf` → `psiI ∈ W 0`. Connect.

## Honest scale
M5 is the ψ(I)-level proof-theoretic content — the real research. The external proof
takes it "for free" only by using set-theoretic ordinals (its black box 1). Validating
M1–M2–M3 end-to-end first de-risks the design before investing in M5. This is a
Buchholz-style ordinal-analysis construction; it is expected to span sessions.

## Rules
- Verify every Lean claim with `leanman check -C lean FILE.lean` (`LEANMAN_TIMEOUT=900`
  for heavy files). Use `trace_state` before a sorry to read the goal.
- Verify matrix expansions with `tools/trio.py` / `bms`, never by hand.
- Publication: refer to the external proof only by the public URL
  github.com/koteitan/dh-bms-wf-formal — never a local path — in any committed file.
- `git add` named files only (never `-A`/`.`).
