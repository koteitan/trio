# WfHUAC2 notes (shrinking WfHUACDeep.HUACDeepShape)

## Result (Lean, Ytosk/lean/Ytosk/WfHUAC2Canon.lean, green)
Notation: n upgrades to ancestor k (k < n), m = P0 k = P1 n, j = LAST bump child of k,
c = FIRST child of j, chain of m: m, P1 m, P1 P1 m, ...

Proved, no residual:
- `canon_struct` (Std, N != SRO): children k = L ++ j :: R, col j = bump k,
  children j = c :: C  ->  c < n ∧ e2 c = 0 ∧ ∃ a, Up1 a m ∧ e1 a = e1 c.
  * j < n: the child d of k on the path to n is not a bump child (UAB); if n < j then
    d is an earlier sibling, SibDec gives col j <= col d, Z1C/Z2 force col d = bump k.
  * c < n: subtree of j is contiguous and does not contain n (UAB).
  * e1 c <= e1 k (Z1C at j); e1 c = e1 k is impossible: BumpLeaf makes j the last child
    of k, then n (after j, below k) is below j (sib_after_gt) - contradiction.
  * e1 k = e1 m + 1 (R1S, par1_row_eq_succ), so e1 c <= e1 m.
  * e2 c = 0: RowJ (row 2 nonzero needs e1 P0(c) <= e1 c; e1 j > e1 c).
  * every level <= e1 m is on the row-1 chain (`chain_level`, R1S unit steps + par1_exists).
- `bump_kid_e2`: every child of a bump child has row 2 = 0 (RowJ / BumpLeaf).
- `first_kid_survives`: o(c) ∈ summands (Σ o(children j)).  All children of j are
  counted with cnt = o (not bump: row 2 = 0; not an upgrade target: row 2 = 0), so
  Good3.dec makes the o list non-increasing and sumN_cons_dec keeps the head.
- Bridges: `deepShape_of_canon : HUACCanon → HUACDeepShape`,
  `deepShape_of_step : HUACStep → HUACDeepShape`, `hUAC_of_step : HUACStep → HUAC`.

New residual `Ytosk.WfHUAC2Canon.HUACStep` (only the value part StepDom is left):
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ →
   ∀ n k m, upg N n = some k → k < n → par N 0 k = some m →
    Danger (vOpt σ (par N 1 n)) (bumpW N σ k) →
    lev (bumpW N σ k) = z ∨
    ∃ L j R c C, children k = L ++ j :: R ∧ col j = bump k ∧ (∀ d ∈ R, col d ≠ bump k) ∧
      children j = c :: C ∧ ∀ a, Up1 a m → e1 a = e1 c → StepDom σ a m
(a is unique: row 1 strictly drops along the chain.)

Splice for the top (V3TopT2B.lean, H10 agent): replace the hypothesis
`hUD : WfHUACDeep.HUACDeepShape` by `hUS2 : WfHUAC2Canon.HUACStep` and
`WfHUACDeep.hUAC_of_deep hUD` by `WfHUAC2Canon.hUAC_of_step hUS2`
(or keep hUAC_of_deep and pass `WfHUAC2Canon.deepShape_of_step hUS2`).
Import `Ytosk.WfHUAC2Canon`.

## Measurements (ij2.py, canonical witness on every ancestor upgrade)
D = danger with lev W != 0, N = the rest.
(i) = every upgrade target t of a chain column strictly above a has no bump child,
(ii) = v(a) has a level-0 component >= 1 (only needed when a U-step exists).

| set | frames | D | D canonical | D with U-step | D: (i) fail | D: (ii) fail | D: StepDom fail |
|---|---:|---:|---:|---:|---:|---:|---:|
| graftBb2St | 148,761 | 15,280 | 15,280 | 96 | 0 | 0 | 0 |
| deepfam (4,015,492 mats) | 42,820,878 | 12,651,549 | 12,651,549 | 780,732 | 0 | 0 | 0 |
| ufam (fresh, 911,416 mats) | 11,969,382 | 1,960,940 | 1,960,940 | 1,960,940 | 0 | 0 | 0 |

ufam (ufam.py): seeds = the 482 bms-standard matrices of graftBb2St, graftA, graftBn2,
graftBb2G, graftBb2, graftB having a D frame with a U-step above a; + 14,475 bms-standard
one-column extensions; + expansions n=0..4 with all prefixes (len <= 140, below SRO).

N frames (no danger): structure also always canonical (no j >= n, no category failure),
but U-steps there break (i) (deepfam 680,296; ufam 39,747) and StepDom
(deepfam 146,837; ufam 38,083).  So StepDom really needs Danger: the residual cannot
drop the Danger hypothesis.  j a leaf happens only in N frames (lev W = 0 in all of them,
surv.py on graftBb2St/graftA).

## What is left
`HUACStep`: under Danger and lev W != 0, (a) the last bump child of k has a child and
(b) StepDom at the chain level of the first grandchild.  The data says more: the
upgrade targets above a have no bump child, so each U-increment is ω (`last_v_noBump`),
and v(a) has a level-0 component >= 1 (`stepDom_of_noBump` turns (i)+(ii) into StepDom).
Observed: in every N frame with a U-step some target t above a has a bump child.
Conjecture (NOT measured): then the increment ω^{P(t)} is not below W, which is why there is no danger.  A proof has to
compare P(t) (grandchildren under t's bump child) with P(k) (grandchildren under k's
last bump child); this is the remaining value content.
