# WfB2S notes (2026-10-31): B2Step is FALSE; replaced by B2StepAb (absorption case, last bump child with children)

## PRIORITY: B2Step is false (Lean, `Ytosk/lean/Ytosk/WfB2SFalse.lean`)
- 28 columns, standard (Std.exp trace from SRO, 116 steps, kernel checked), Bad2:
  (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,2,0)(3,2,0)(4,3,1)(5,3,1)(6,3,0)(4,3,1)(5,3,1)(6,2,0)(5,3,1)(5,3,0)(6,4,1)(7,4,1)(8,3,0)(8,2,0)
  n = 26 upgrades to k = 19 = (4,3,1), m = 15. children 19 = [20, 22, 23]; 20 and 22 are bump children; the LAST bump
  child 22 is a leaf. bumpW(19) = psi_{w+1}(1), lev != 0. So neither disjunct of B2Step holds.
- `not_B2NoUB : ¬ WfH7W2.B2NoUB` (unconditional), `not_B2StepCore` (Inv3V2 replaced by Cons/Rk/Good3, unconditional),
  `not_B2Step_of (hInvV2_all's 9 hypotheses) : ¬ WfH7W2.B2Step` (via cons_unique: every valuation has the same bumpW).
- Found as the prefix (take 28) of a graft3 matrix with a NOCANON frame at n = 26 (nocanon.py).
- HUACB2 holds there: the last bump child WITH children (20) has first child 21 = (6,2,0) at the level of m (a = m).
- Fix: `WfB2S.B2StepAb` takes j = last bump child with children (later bump children may be leaves; their bump term
  is 1, so j's term survives in P: `bp_dom_of_lastK`, `mem_sumN_last_le1`). fr5.py (this canonical choice): the
  NOCANON frames disappear, all other counts unchanged.

## Result (Lean, green; full build 1142 jobs; axioms propext, Classical.choice, Quot.sound)
- `Ytosk/lean/Ytosk/WfB2S.lean`
  - `dom_add_noabs`: no summand of A below psi_s(b) -> comps u A dominated by comps u (A + psi_s(b)) ++ [0].
  - `huacB2_noabs`: every upgrade n -> k (no Bad2, no StepDom): if no summand of v(P1 n) is < bumpW(k),
    the HUAC domination holds at n (v(n) = v(k) = v(P1 n) + bumpW(k) with nothing absorbed).
  - residual `B2StepAb` = `WfH7W2.B2Step` plus the premise "some summand r of v(m) has r < bumpW(k)" (absorption).
  - `b2StepAb_of_step : B2Step -> B2StepAb` (it is weaker), `huacB2_of_ab : B2StepAb -> WfH7W.HUACB2`.
  - Splice in V3TopT2B: `(hStep : WfB2S.B2StepAb)`, and `WfB2S.huacB2_of_ab hStep` in place of
    `WfH7W2.huacB2_of_step hStep` (lines 161 and 218), `import Ytosk.WfB2S`.

## Measurements (scripts here)
- fr.py / fr2.py / fr3.py: every position n with upg n = k < n (fr3: also without the bump-parent condition),
  canonical c (first child of the last bump child of k), level a on the row-1 chain of m = P0 k, index i of a,
  U-steps strictly above a, StepDom, absorption ab = (last v(m) < bumpW(k)), and at n = x-1 Bad2 / UpgAbsX.
- With P0 n a bump child (bp), all positions, no Bad2 (cbadext, graft2, graft3, b2grow1, graft_b2 ... see fr3a.log):
  - i is always 0 or 1.
  - ab = True  ->  U0 (StepDom vacuous) in every frame.
  - ab = False ->  exactly the frames i = 1 with m upgrading (U1); StepDom is false in many of them
    (graft2: 1232 of 2575). These are harmless for HUACB2 (huacB2_noabs).
  - at x-1 the i = 1, m-upgrading frames all have UpgAbsX (not Bad2): Bad2 forces ab (v(m) has a summand
    r < W that is not lhd W), which is why B2Step needed Bad2.
- Without the bump parent (fr3, hsf.pkl = the HUACStep counterexample): ab = True with i = 2, two U-steps and
  StepDom false occurs (n = 37, k = 33). The bump parent (given by Bad2) is needed.

## B2StepAb split (Lean `Ytosk/lean/Ytosk/WfB2S2.lean`, green)
- `B2LevS` (structural, no valuation): n + 2 = |M|, upg n = k < n, m = P0 k, P0 n = p a bump child of g = P0 p ->
  every child of a bump child of k has row 1 = 0, or the last bump child j of k WITH children has a first child c
  with e1 m <= e1 c + 1 (level of c on the chain of m is m or P1 m; R1S makes chain levels unit steps).
- `B2UpgV` (value): same frame under Bad2/Inv3V2, e1 c + 1 = e1 m, upg m = t -> bumpW(k) <= last v(t).
- `b2StepAb_of : B2LevS -> B2UpgV -> B2StepAb`: a chain column y above a with Up1 y m has e1 y = e1 m, so y = m;
  then v(m) = v(P1 m) + last v(t) has every summand >= last v(t) >= W (`summands_add_ge`, `last_form`), which
  contradicts the absorption premise. So StepDom holds vacuously.
- Splice: `(hStep : WfB2S.B2StepAb)` can be fed by `WfB2S.b2StepAb_of hLev hUpgV`; HUACB2 = `WfB2S.huacB2_of_ab`.

## Measurements of B2LevS / B2UpgV (fr6.py; every position n with bump parent, no Bad2; 0 exceptions)
- cbadext (i1 201, U 201), graft2 (i0 26548, i1 3004, U 2819), graft3 (i1 1436), graft_b2, graft_sib, b2grow1,
  b2grow2, wide, paired, huac_fresh, huac_consumers_t0/deep_t0, t2src_a_last/parent/real/delete_return,
  graftBb2St, graftB: fr6all.log.
- graft4.py: 260 seeds (200 with an i1 frame cut at n+2, 60 i0), one column +-1/delete/duplicate/append, bms-standard:
  17293 grafts. all positions: i0 21233, i1 24702 (U 5830, all bumpW(k) <= last v(t)); x-1 only: i1 2801 (U 891).
  0 exceptions (fr6g4.log).
- B2UpgV: bumpW(k) = last v(t) in most frames, bumpW(k) < last v(t) in the rest (fr4.py on graft2: 2015 eq, 804 lt);
  t is always an ancestor of m (t < m).
- Bad2 is not needed for either (measured at all positions). Without the bump parent, B2LevS fails (hsf.pkl,
  i = 2 at n = 37 of the HUACStep counterexample).
- graft5.py (second generation; 200 seeds from graft4 with an i1 frame where m upgrades, cut at n+2): 12214
  bms-standard grafts; all positions: i1 18755, all with m upgrading, all bumpW(k) <= last v(t); 0 exceptions
  (fr6g5.log).
