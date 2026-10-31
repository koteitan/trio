# WfQnH: the q != r engine with the bad closure (2026-11-01, round 11)

All Lean green (leanman build 1225+ jobs), no sorry, no axiom.  Files Ytosk/lean/Ytosk/WfQnH1..8.lean.

## Lean
- WfQnH1 `hu0` PROVED (residual of WfQnL8 gone): in P = M[n-1] the column r+1 is a row-0 child of the bad root r
  (L >= 2: inside the bad part, child_succ; L = 1: first copy column, row 0 = e0(r) + d0, d0 > 0), so
  upg P r = some g -> g < r (upg_lt_of_child).  `hndN_of_hnd'` = hndN_of_hnd without hu0.
- WfQnH2 `vlocal_t1_at_locB` / `vlocal_t1_atXB`: VLocal at every v call of D off DepXB M (BadSet ..), with the
  low-part comparison hTPLζ asked only at o calls off the closure (it is read only at the last bump grandchild k;
  (true,k) in DepXB -> (false,i) in DepXB by vbump).
- WfQnH3 (task 1): `olocal_ofB` (olocal_of with hL only off the closure), `hole0` (holes from t1_hole0, no VLocal),
  `hW_of_TP1_0`, `hLoB`, `TPLB` (comparison at ζ off the closure), `TPLoSXIn` (closure claim),
  `tplB_of_tpLoSX : TPLoSX ∧ TPLoSXIn -> TPLB`, `olocal_t1B` = the hO of WfQnL3.t1_pathB.
- WfQnH4: `hF_of_pathB` (t1_pathB conclusion = hF of E1_M), `v_bad_M` (in M: v(i) = A when V < A),
  `leaf_E3` (task 2, leaves): at a non-nested bad call, σ.v i = sf(V + A[ζ]) and fsD(ρ.v i, ζ) <= σ.v i < ρ.v i.
- WfQnH5 (task 4): `t1_E1B` (E1 off the closure from OLocal/VLocal off the closure), `t1_rootB`: root of M[n]
  drops for every solution σ, given (E3) at the root (`hE3`).
- WfQnH6: `e3_of_lhd`: Lhd z + isOT at the root -> hE3.
- WfQnH7: `deps_lhd_otU` = V3DepOT.deps_lhd_ot with the unchanged calls given by a set U (σ = ρ only on U);
  needed because the glue values on D \ closure are not ◁ the old values (LZ.glue below).
- WfQnH8: seeds SB B = bad leaves, `depS_iff : DepS M (SB B) = DepXB M B`, `hoff_of_E1` and `hOTn_of_E1`
  (two hypotheses of deps_lhd_otU from E1 with U b i := ¬ DepX M x b i), `e3_root` (engine conclusion -> hE3).

## Measurements (meas.py, t = 1 q != r frames, ζ = gamS(n-2), n = 2, 3; logs meas.log, m_*.json)
B = Lean BadSet at ζ, DB = DepXB closure.
- graftQ1 (4540 frames): B 397; TZ.fail 794 all in DB (TPLoS failure at ζ at c => (true,c) ∈ DB); NEST 0;
  LEAF eqform/ltA/geAz 397/397; E3 ge/lt 5510/5510; E3.single 4836/4836; root in DB 397, single.
- graftQ2 (29364 frames): B 18496; TZ.fail 36992 all in DB; NEST 0; LEAF 18496 ok; E3 301980/301980 both;
  single 268750/268750.
- graftE, graftD, graftF, graftG, graftM36, graftM36x, graftA1: no bad call (B = 0), no TPL failure at ζ outside.
- Sample graftQ1 300 with the new counters: B.Vlt 34/34 (V < A at every bad call: hVlt of leaf_E3),
  LZ.cl 534/534 (true value ◁ old value at EVERY closure call), LZ.leaf 34/34 (sf(V + A[ζ]) ◁ A),
  LZ.glue 68 ok / 102 FAIL (glue fsD(old,ζ) is not ◁ old: seeds must be the bad leaves only).
- graftQ2 sample 3000 (m_graftQ2_LZ3000.json): B 1858, B.Vlt 1858/1858, LZ.cl 30319/30319, LZ.leaf 1858/1858,
  LZ.glue 3716 ok / 5574 FAIL, TZ 3716 all in DB, NEST 0, E3 30319/30319.
- graftA2, graftA, graftB, ext1, expP, graftA3: not run (stopped at the time budget; run.sh continues the list).

## Structural fact used by the plan (proved informally, to be done in Lean)
The inputs of a closure call are in the closure or outside D:
- o call via ochild: ¬ DepX false i (OShape), other counted children not in D (OShape);
- o call via ov: no counted children (OShape first case);
- v calls: P₁ i ∉ D (dv_shape hpd), so vpar never fires inside D; vbump: K, L-grandchildren ∉ D (BumpNA);
- leaves: the bump grandchild k is in D; if k ∉ DB (non-nested, NEST measured 0) it carries the glue value.
This is exactly what the structural hypotheses hOc / hVc of deps_lhd_otU ask with U = off D, except at the leaves
(seeds, handled by hSeed with leaf_E3 + LZ.leaf).

## Residuals (new, measured)
- TPLoSXIn (closure claim, WfQnH3): 0 failures (TZ, 37786 failures of the comparison, all in the closure).
- hVlt (V < A at bad calls): 0 failures (B.Vlt, sample).
- non-nested bad calls (hnest of leaf_E3): NEST 0 on all data with bad calls.
- Lhd z (sf(V + A[ζ])) A at leaves (hSeed of the engine): 0 failures (sample).
- (E3) in the ◁ form at all closure calls: 0 failures (sample) -> deps_lhd_otU's structural hypotheses
  (hDvNil, hCLnil, hOc, hVc, hupgK, hAbs, hVSN, hHard, hOTout, FrameClosed/FrameOT/VSmallF) for this instance.

## Next
1. Instantiate deps_lhd_otU (WfQnH8): prove hOc/hVc/hDvNil/hCLnil from OShape, dv_shape, BumpNA, SameAt
   (sameAt_lt), with bnd = x, U = off D; hSeed from leaf_E3 + an Lhd lemma for sf(V + A[ζ]) ◁ A
   (q ◁ A for the summands of V: the hAbs-type fact).
2. Assemble t1_main_vlocSX: t1_rootB with hO := olocal_t1B (TPLB via tplB_of_tpLoSX), hV := vlocal_t1_atXB,
   hE3 := e3_root (engine), plus existence of σ (Cons/Rk of N) and Good3/Pn of N.
3. Run meas.py on the remaining sets (graftA2, graftA, graftB, ext1, expP, graftA3) and attack TPLoSXIn / hVlt /
   NEST by grafting (graftQ-style from WfQnE/graft.py).
