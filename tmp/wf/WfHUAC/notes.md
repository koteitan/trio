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
  ∃ j c a, j ∈ children k ∧ col j = bump k ∧ bumpTerm k j ∈ summands P ∧
    c ∈ children j ∧ o c ∈ summands (Σ o(children j)) ∧ c < n ∧
    Up1 a m ∧ e1 c = e1 a ∧ e2 c = 0 ∧ StepDom σ a m
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
