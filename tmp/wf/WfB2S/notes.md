# WfB2S notes (2026-10-31): B2Step narrowed to the absorption case

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
