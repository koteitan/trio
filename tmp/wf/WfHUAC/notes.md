# WfHUAC notes (HUACShape residual)

## Goal
Old residual: `HUACShapes.HUACShape` (V3HUACShape.lean):
Danger(v(P1 n), W) -> lev W = 0 ∨ ReturnWitness ∨ SupportWitness, where
SupportWitness = first surviving bump child j of k, its first child c,
Support(v(P1 m), v(c)) ∧ Support(increment m, v(c)).

Notation: n upgrades to ancestor k (k < n), m = P0(k) = P1(n), V = v(m),
W = bumpW(k) = ω^P, P = 1 + Σ_j bumpTerm(k, j).
Row-1 chain of m: a_0 = m, a_{l+1} = P1(a_l).

## Observation 1 (deep return)
Measured (deep_return.py): in EVERY dangerous positive frame the chosen grandchild c
returns to the row-1 level of some a_i on the row-1 chain of m:
e1(c) = e1(a_i), e2(c) = e2(a_i) = 0, P1(c) = P1(a_i), upg(c) = upg(a_i), so v(c) = v(a_i).
The old ReturnWitness is i = 0.  Counts (graftBb2St): i=0 14588, i=1 634, i=2 58.
Increments of chain columns below a_i: type P (+1) or U (+ last v(upg a_l)).

## Lean (Ytosk/lean/Ytosk/WfHUACDeep.lean, green)
Proved (no residual):
- `Up1 M a x` (a reached from x by row-1 parent steps), `up1_le`, `up1_anc0`,
  `up1_e1_le`, `up1_hi`, `up1_split`, `up1_par1`, `up1_e2`, `up1_trans`.
- `deep_return`: structural.  c child of bump child j of k, c < n, Up1 a m,
  e1 c = e1 a, e2 c = 0, e2 a = 0  ->  P1 c = P1 a ∧ upg c = upg a.
  (generalizes HUACCopy.return_copy; same proof idea along `ancL`.)
- `value_eq_of_same_rhs`: then v c = v a (Cons).
- `support_up1` / `dom_up1`: Support / comps-domination of v(x) by v(a) along the
  row-1 chain, from the U-increments only (P-increments are 1; e2 = 0 on the
  chain is proved from Z1C via `par1_e2_ne_one`).
- `dom_of_grandchild_dom`: Dom(v m -> v c) + survival -> HUAC conclusion.
- `dom_of_deep`, bridge `hUAC_of_deep : HUACDeepShape → HUAC`.

New residual `WfHUACDeep.HUACDeepShape`:
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ →
   ∀ n k m, upg N n = some k → k < n → par N 0 k = some m →
   Danger (vOpt σ (par N 1 n)) (bumpW N σ k) →
   lev (bumpW N σ k) = z ∨ ReturnWitness N n k m ∨ DeepWitness N σ n k m
DeepWitness N σ n k m :=
  ∃ L j R c a, children k = L ++ j :: R ∧ col j = bump k ∧ (∀ d ∈ R, col d ≠ bump k) ∧
    c ∈ children j ∧ o c ∈ summands (Σ o(children j)) ∧ c < n ∧
    Up1 a m ∧ e1 c = e1 a ∧ e2 c = 0 ∧ StepDom σ a m
(j = LAST bump child: its survival in P is proved by `bp_dom_of_last`.  In every
measured danger witness the first surviving bump child IS the last one, and c is the
first child of j.)
StepDom σ a m := ∀ y, Up1 a y → Up1 y m → y ≠ a → ∀ t, upg y = some t →
    ∀ u, Dom (comps u (last (v t))) (comps u (v a) ++ [0])

Compared with SupportWitness: Support(v(P1 m), v(c)) and Support(inc m, v(c))
are gone; the value content is only the U-increments strictly between m and a,
and only as component domination (weaker than support).  Plain chains (all P)
make StepDom vacuous.

## Measurements of the new residual (deep_exist.py; witness searched over all
surviving bump children j, surviving children c, chain index; Support and the
per-step U-support (which implies StepDom) recorded)
| set | anc. upgrades | danger | zero | i=0 | i=1 | i=2+ | no witness (danger, positive) | step fail |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| graftBb2St | 148,761 | 15,597 | 317 | 14,588 | 634 | 58 | 0 | 0 |
| b2grow2 | 150,781 | 79,421 | 0 | 79,327 | 76 | 18 | 0 | 0 |
| b2grow1 | 61,604 | 27,878 | 0 | 27,878 | 0 | 0 | 0 | 0 |
| d3s | 74,319 | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| graftB | 665,561 | 105,360 | 790 | 99,144 | 5,173 | 253 | 0 | 0 |
| graftBn | 661,529 | 103,848 | 790 | 97,632 | 5,173 | 253 | 0 | 0 |
| graftBn2 | 250,597 | 50,011 | 154 | 47,574 | 2,273 | 10 | 0 | 0 |
ext2 had 0 danger frames (codex full6 rerun).

## Choice that fails (do not use)
LAST bump child / LAST child c (survival automatic) fails: 21 danger frames in
graftBb2St where the last child has row 1 = 0 (v(a) = 0).  Smallest:
(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(4,1,1)(5,1,1)(6,1,0)(4,1,1)(5,1,1)(6,0,0)(7,1,1)(8,1,1)(9,1,0)(7,1,1)(8,1,0)(9,2,1)(10,2,1)(11,2,0)(9,2,0)(10,3,1)(11,3,1)(12,2,0)(13,3,1)(14,3,1)(15,1,0)(15,0,0)(14,3,0)(15,4,1)(16,4,1)(17,1,0)(17,0,0)
n=29, k=25, m=24, j=26, last c=28 (15,0,0) returns to a=12 (6,0,0); V = ω+1 not supported by v(a) = 0.
So survival must stay explicit (or come from BumpKidsDec/BumpTermDec, which HUAC's
context does not have).

## U-steps (ustep.py)
graftBb2St: 154 U-steps, all with t = upg y an ancestor, P(t) = 1 (t has no bump
child), last v(t) = ω = v(a) exactly.  So StepDom reduces there to comps(ω) ⊑ comps(v a).
Example: (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(4,1,1)(5,1,1)(6,1,0)(4,1,1)(5,1,1)(6,0,0)(7,1,1)(8,1,1)(9,1,0)(7,1,1)(8,1,0)(9,2,1)(10,2,1)(11,2,0)(9,2,1)(10,2,0)(11,3,1)(12,3,1)(13,1,0)(14,2,0)(12,3,0)(13,4,1)(14,4,1)(15,1,0)(16,2,0)
n=27, k=23, m=22, c=25, a=17, y=22, t=21; V=ω+ω, W=Ω_ω-ish, v(a)=ω, last v(t)=ω.

## More sets (deep_exist.py), 0 exceptions
| set | anc. upgrades | danger | zero | i=0 | i=1 | i=2+ | no witness | step fail |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| graftBb2 | 414,964 | 55,349 | 636 | 51,570 | 2,900 | 243 | 0 | 0 |
| graftBb2G | 263,707 | 38,816 | 319 | 36,046 | 2,266 | 185 | 0 | 0 |
| graftBb2S | 151,257 | 16,533 | 317 | 15,524 | 634 | 58 | 0 | 0 |
| graftA | 42,715 | 3,844 | 33 | 3,646 | 150 | 15 | 0 | 0 |

## U-steps on more sets (ustep.py)
graftB 708, graftBn2 84, graftBb2 624, graftBb2G 470, graftA 42 U-steps (b2grow2 none):
every one has P(t) = 1 (upgrade target t has no bump child), last v(t) = ω = v(a),
t an ancestor of y.

## Sufficient form (proved in Lean, NOT adopted as residual)
`stepDom_of_noBump`: (every upgrade target t strictly below a has no bump child)
∧ (∃ g ∈ comps 0 (v a), 1 ≤ g)  ->  StepDom.  Uses `last_v_noBump` (last v(t) = ω)
and `dom_omega_of_comp`.  Kept as a tool; the residual stays the weaker StepDom.

## Targeted family (graft_family.py -> deepfam.pkl, not committed: 1.6 GB)
Seeds: 933 bms-standard matrices from graftBb2St, b2grow2, graftA having a dangerous
frame without the last-child return.  + 59,467 bms-standard one-column extensions
(of 227,906 candidates), + one round of expansions n=0..4 with all prefixes
(len <= 160, below SRO).  Total 4,015,492 matrices, 42,820,878 ancestor upgrades.

Run 1 (run_fam.py = deep_exist.py, LITERAL Support used to pick a): 12,651,393 danger
positive frames; i=0 3,885,285, i=1 8,086,464, i=2+ 679,644; jlast and cfirst always;
156 frames with NO witness under literal Support.  Smallest (bms -s = 1), n=64:
(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)(6,2,1)(7,2,1)(8,2,0)(6,2,1)(7,2,1)(8,1,0)(4,2,0)(5,3,1)(6,3,1)(7,2,0)(6,3,0)(7,4,1)(8,4,1)(9,2,0)(8,4,0)(9,5,1)(10,5,1)(11,2,0)(5,3,0)(6,4,1)(7,4,1)(8,2,0)(7,4,0)(8,5,1)(9,5,1)(10,2,0)(6,4,1)(7,4,0)(8,5,1)(9,5,1)(10,2,0)(9,5,0)(10,6,1)(11,6,1)(12,2,0)(8,5,1)(9,5,0)(10,6,1)(11,6,1)(12,2,0)(11,6,0)(12,7,1)(13,7,1)(14,2,0)(10,6,1)(11,6,0)(12,7,1)(13,7,1)(14,2,0)(13,7,0)(14,8,1)(15,8,1)(16,2,0)(12,7,1)
k=61, m=60, chain 60,51,42,33,21,8,0; c=63 (14,2,0) returns to a=21 (4,2,0);
V = X+ω+ω+ω with X = v(21) = ψ_ω(ψ_{ψ_{ψ_ω(0)}(0)}(0)); U-steps 60,51,42 add ω, which is
NOT a summand of v(a) = X but IS comps-dominated (index ω of X).  So literal
Support (and StepSupport, and the old SupportWitness-style certificate) is false here,
while the Lean residual StepDom holds.  This is why StepDom (Dom, not Support) is the
residual.  HUAC holds on this frame.

Run 2 (deep_exist2.py, exact Lean DeepWitness with StepDom): see deep_exist2_deepfam.json.

## The old residual HUACShape is FALSE (Lean, green)
Ytosk/lean/Ytosk/WfHUACShapeFalse.lean: `not_HUACShape : ¬ HUACShapes.HUACShape`
(axioms propext, Quot.sound).  Matrix (48 columns, bms -s = 1, below SRO; `standard`
via an explicit Std.exp trace from SRO, reach48.json):
(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)(6,2,1)(7,2,1)(8,2,0)(6,2,1)(7,2,1)(8,1,0)(4,2,0)(5,3,1)(6,3,1)(7,2,0)(6,3,0)(7,4,1)(8,4,1)(9,2,0)(8,4,0)(9,5,1)(10,5,1)(11,2,0)(5,3,0)(6,4,1)(7,4,1)(8,2,0)(7,4,0)(8,5,1)(9,5,1)(10,2,0)(6,4,1)(7,4,0)(8,5,1)(9,5,1)(10,2,0)(9,5,0)(10,6,1)
Frame n=46, k=43, m=42 (P1 chain 42 -> 33 -> 21 -> 8 -> 0).  The canonical valuation
(tables oT, vT, ranks rkO, rkV from Ctx) satisfies Cons, Rk, Good3 by `decide`.
v(42) = X + ω, X = v(21) = ψ_ω(ψ_{ψ_{ψ_ω(0)}(0)}(0)); W = bumpW 43 = ψ_X(0); ω < W
is dangerous.  Only bump child 44, its only child 45 = (10,2,0) has row 1 = 2 ≠ 4:
no ReturnWitness; SupportWitness needs Support(increment 42 = ω, v(45) = X): false.
`deep_witness_here : WfHUACDeep.DeepWitness M σ 46 43 42` (a = 21; U-step 42 adds ω,
dominated through the index ω of X) is also proved, so the new residual holds there.

## Run 2 result (exact Lean HUACDeepShape, deep_exist2.py on deepfam.pkl)
4,015,492 matrices, 42,820,878 ancestor upgrades, 12,651,549 danger frames:
ReturnWitness 3,885,285; DeepWitness 8,766,264 (i=1 8,086,464, i=2 644,249, i>=3 35,551);
of the deep ones 156 need StepDom (literal support false); zero-index 0;
NO WITNESS 0; structural mismatch (P1/upg/v of c vs a) 0.  (deep_exist2_deepfam.json)

## What remains (exact Lean)
`Ytosk.WfHUACDeep.HUACDeepShape` (see above).  Bridge `Ytosk.WfHUACDeep.hUAC_of_deep :
HUACDeepShape → HUAC`.  The lead should replace the hypothesis `hUS : HUACShapes.HUACShape`
(which is FALSE: `WfHUACShapeFalse.not_HUACShape`) by `hUD : WfHUACDeep.HUACDeepShape` and
`HUACShapes.hUAC_of hUS` by `WfHUACDeep.hUAC_of_deep hUD`.
Open content: existence (under Danger, lev W ≠ 0, no last-child return) of a surviving
first-level grandchild c under the last bump child that returns to a row-1 ancestor a of m,
plus StepDom (U-increments ω^{P(t)} of chain columns between m and a are comps-dominated by v(a)).
