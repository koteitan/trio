# WfQnA: the q != r engine with the bad closure, assembled (2026-11-01, round 12)

All Lean green (leanman build, no sorry, no new axiom; `#print axioms t1_main_vlocSX` = propext, choice, Quot.sound).
Files Ytosk/lean/Ytosk/WfQnA1..18.lean.

## Lean
- WfQnA1 `deps_lhd_otUD`: the engine `WfQnH7.deps_lhd_otU` with `hVSN`, `hHard` asked only at o calls of the
  closure and the absorption `hAbs` only at non-seed v calls of the closure, in the WEAK form of `AbsWN`
  (`¬ q < bumpW N σ i`, `v_bump_lhdW`).  The strong form (BumpAbs on the closure) is FALSE: 3 failures on graftQ1,
  185 on graftQ2 (meas.py `ABS.cl`; example graftQ1 50 columns, i = 28, W != A, q not ◁ W).
- WfQnA2: structural hypotheses of the engine for the t = 1 frame, all proved: `hnx_t1` (v(x) ∉ D), `notXB`
  (o(x) ∉ closure), `depX_of_xb`, `hDvNilB`, `sameAt_t1`, `CL_eq_t1`, `hCLnilB`, `hOcB`, `hVcB`, `hupgKB`.
- WfQnA3: `seed_lhd_val` (V < A, A[ζ] ◁ A, window absorption ⇒ sf(V + A[ζ]) ◁ A), `seed_bad_t1` (hSeed at a bad leaf
  via leaf_E3, v_bad_M, fsD_seed at the diagonal point A = ψ_μ(b_r)), `hOTD_of_hole`, `engine_t1B` (the instance).
- WfQnA4/5: `t1_rootX` (t1_rootB with hE3 from the engine via e3_root), `t1_rootX2` (seeds = bad leaves).
- WfQnA6/7: `good3_N_gen` (Good3 of M[n] for any valuation that lowers D), `good3_N_t1B` (true valuation).
- WfQnA8: `t1_chainB` (induction on n with the TRUE valuation of M[n]: cons_of_rk of rk_N_t1; (E1) off the
  closure, engine on it, Good3, root), with `ResT1B` (engine residuals per level) and `StepT1B` (carried property).
- WfQnA9..12: the layers t1_main / t1_main2 / t1_main_struct / t1_main_dropG2 for the B-world
  (`t1_mainB`, `t1_main2B`, `t1_main_structB`, `t1_main_dropG2B`); OLocal off the closure from TPLB
  (`olocal_t1B`), holes from `hole0`, `hndN` from `hndN_of_hnd'`.
- WfQnA13 `t1_main_vlocSX`: the top (= t1_main_vlocSG2 with TPLoS → TPLoSX + TPLoSXIn, AbsDS → AbsDSX,
  VLocal off the closure by `vlocal_t1_atXB`, (W) by `hW_of_TP1_0`).
- WfQnA14 `bump_naB`: BumpNA at a non-nested bad call with the comparison only off the closure.
- WfQnA15 `resT1B_of`: the seed part of ResT1B from hVlt / hnest / hRwin / hna.
- WfQnA16 `t1_main_vlocSX2`: seeds reduced.
- WfQnA17 `db_lt_r`: if every bad call is before r, the whole closure is before r (vpar never fires in the
  closure, vupg goes to i+1).  `hrB_of`, `hnest_of`.
- WfQnA18 `t1_main_vlocSX3`: final form.

## Residuals of t1_main_vlocSX3 (beyond the old t1_main_vlocSG2 inputs, with AbsDS/TPLoS replaced by AbsDSX/TPLoSX)
- `hin`  : TPLoSXIn at every level m (closure claim).
- `hBr`  : every bad call is before r.                    (meas `B.ltr`)
- `hKr`  : bump grandchildren in D of a bad call are >= r.  (meas `B.kr`: the last one is r itself)
- `hVlt` : V = v(P1 i) < A at bad calls.                  (meas `B.Vlt`)
- `hRwin`: window absorption: q ∈ summands V, A[ζ] <= q < A ⇒ q ◁ A.  (meas `ABS.leaf`)
- `hRest` = `ResT1Bv`: in the closure, for the true σ of M[n]: `hVSN` (meas `VSN`), `hHard` (meas `HARD`),
  `hAbsW` (weak absorption, meas `ABSW.cl`).
- `hPsB` = `StepT1B`: the carried property Pn for the true valuation (design: Pn is the invariant; its step is
  the ExpStep of the invariant, to be restated for the true valuation).

## Measurements (meas.py = WfQnH meas.py + ABS/ABSW/VSN/HARD/R.inDB/B.ltr/B.kr; n = 2, 3)
- graftQ1 (4540 frames): B 397, B.Vlt 397/397, NEST 0, TZ.fail 794 all in DB, ABS.cl 3 FAIL / 608,
  ABS.leaf 397/397, VSN 659 ok (3503 same), HARD 989 ok (pre 1879), LZ.cl 5510/5510, E3 5510/5510.
- graftQ2 (29364 frames): B 18496, B.Vlt all, NEST 0, TZ 36992 all in DB, ABS.cl 185 FAIL / 29677,
  ABS.leaf 18496/18496, VSN 32435 ok, HARD 61108 ok (pre 110290), LZ.cl/E3 301980 all.
- graftA2 (53563 frames), graftA (7395): no bad call (B = 0).
- sample graftQ1 150: B.ltr 15/15, B.kr 15/15, R.outDB 15/15.
- GRAFT ROUND graftQ3 (graftQ3.py: 1500 bad-frame seeds of graftQ2, WfQnE/graft.py ops; 215650 grafts, all
  frames): B 154128 bad calls; B.Vlt 154128/154128 (hVlt), B.ltr 154128 (hBr), B.kr 154128 (hKr: last bump
  grandchild = r), NEST 0, R.inDB 0 (hrB), TZ.fail 308256 all in DB (TPLoSXIn), ABS.leaf 154128/154128 (hRwin),
  VSN 271617 ok / 0 fail, HARD 614155 ok / 0 fail (antecedent 1066808 pre-cases), ABSW.cl: 0 cases (the weak
  absorption antecedent never fires in the closure), LZ.cl / E3 2766927 all ok, ABS.cl (strong, unused) 2259 FAIL.
- re-runs graftQ1/graftQ2 with the new counters (m2_*.json): same, ABSW 0 cases, B.ltr/B.kr/R.outDB all.
- Not run (stopped at the time budget): graftA3, graftB, expP, ext1 (earlier rounds: no bad call in these).
- WfQnA19: `win_of_fail`/`witness_bad`: a TPLoSX witness at a failing comparison is in BadSet (given e1, e2 != 0
  and hVlt); the remaining half of TPLoSXIn is the climb of the closure from m = P0 i to c.
