# WfReM: re-measure the top hypotheses around the 36-column counterexample (2026-10-31)

## PRIORITY: HDropU is false (Lean, Ytosk/lean/Ytosk/WfReM1.lean, green)
N = M[3] of the 36-column WfSrcC3Cex.M (37 columns, standard, Std.exp 3 of the 93-step trace):
(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)
(6,2,1)(7,2,1)(8,2,0)(6,2,1)(7,2,1)(8,1,0)(9,2,1)(10,2,1)(11,2,0)(9,2,1)(10,2,1)(11,1,0)(12,2,0)(12,0,0)
(13,1,1)(14,1,1)(10,2,0)(11,3,1)(12,3,1)(13,1,0)(14,2,0)(15,3,0)
- x = 36 = (15,3,0), P0 x = 35 = x-1 = (14,2,0), e1 x = 3. upg(35) = none, so not Bad2 (first conjunct).
- HDropU asks BumpAbsC N 36 rho. It fails at i = 32 = (11,3,1): summand s of v(31) with
  s >= W_{N.take 36}(32) = psi_{psi(1)}(Omega_{psi(1)+1}), s < W_N(32) = psi_{psi(1)}(Omega_{psi(1)+2}), s not lhd W_N(32).
  Guard XParNB (col 35 = (14,2,0) != bump 34 = (14,1,1)).
- N.take 36 = M[2] (valuation WfSrcC3Cex.sigma).
- This is the second disjunct of Bad2 (P0 x = x-1, e1 x != 0, BumpAbsC fails) without the upgrade conjunct.
- Lean: bumpAbsC_core_false (Cons only, axioms propext/Quot.sound), not_HDropU_of_inv (exists Inv3V2 on N),
  not_HDropU_of (the 9 hypotheses of hInvV2_all, which include HDropU, are inconsistent).
- Python (ctx36.py): on every prefix of M, M[2], M[3] all Inv3V2 fields (inv_fields minus the old global
  AbsD/AbsU/AbsUW/TPLo/TPLoW/AbsDW, + probe_inv2/frame7/trigs0/leafg, PH3cG, FC3, SInv structure) hold;
  the only failures are BumpAbsC on M (Bad2, allowed) and on M[3] (not Bad2: the refutation).

## (2) StepCtxT2 fields on M (ctx36.py, ctx36.json)
- M: Std, != SRO, Inv3V2 fields all true on M and on every prefix M.take j; Res3AW's drop fields (HardArg,
  VSmallNew, BumpWeakSrc, WeakCS, BumpAbsC) true on every non-Bad2 prefix; T2CBad false (P0 x = r).
- DropResHB on M: HardArg, VSmallNew, WeakCS, BumpWeakSrc (old, stronger than B form) true; ua (UpgAbsXW0) true.
  BumpAbsC fails on M, but M is Bad2 so only BumpAbsCB is needed. (CntX second disjunct: see below.)
So the core refutations of WfSrcC3Cex are refutations of the full residuals, as far as Python measures.

## (1) graft family graftM36.pkl (graft.py)
- graft.py: seeds = M36, its frame F35, and every t=2 prefix with a column c != r, v(c) = v(r) of samples of
  graftBb2St / b2grow1 / b2grow2 (4000 each). Gen 1: child (e0 c + 1, a, b) of c (a <= e1 c + 2) as first or last
  child; for M36/F35 also every column c and graft4 mutations. Gen 2: the same on 1500 gen-1 matrices.
  bms -s = 1 and < SRO. 24690 matrices (gen1 7255, gen2 new 17435).

## PRIORITY 2: T2SeedClV2R (hClR) is false in its qn field (Lean, Ytosk/lean/Ytosk/WfReM2.lean, green)
N (46 columns, 236-step trace, qn46_trace.json):
(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)(6,2,1)
(7,2,1)(8,2,0)(6,2,1)(7,2,1)(8,1,0)(9,2,1)(10,2,1)(11,2,0)(9,2,1)(7,2,0)(8,3,1)(9,3,1)(10,2,0)(11,0,0)(10,1,0)
(11,2,1)(12,2,1)(13,2,0)(11,2,1)(12,2,1)(13,1,0)(14,2,1)(15,2,1)(16,2,0)(14,2,1)(12,2,0)(13,3,1)(14,3,1)(15,2,0)(14,3,1)
- Bad2, t = 2, x = 45, r = 41, q = 42, CL r = [42], Lc = [] (qn branch, not T2CBad).
- X1 = psi_{t1}(0), t1 = psi_{psi(1)+1}(0). Path level u = v(30) = psi(1) (30 -> 34 -> 41), u <= v(r).
  g = psi_{psi_{psi(1)+psi(1)}(0)}(0) in comps u qnS, g not < X1: third conjunct of T2SeedQNBaseR fails.
- Lean: qnBase_core_false (Std ∧ Cons, axioms propext), not_T2SeedClV2R_of_ctx (∃ rk, StepCtxT2 N rho rk).
- Python (chk_one.py): all Inv3V2 fields on N and every prefix hold (VSmallF in the Lean form, vsmallf.py; the
  inv_fields VSmallF is the old stronger form), drop fields hold, not T2CBad.
- qnpath.py: 163 of the graftM36 matrices fail this clause (smallest 46 columns); 0 on the earlier sets.

## Notes on the probes
- tools/probe_hframe measures TPLoW / AbsDW at the old lower bound gamS mu b 1 k (false on grafts). The Lean
  TakeFrameV2 / Inv3V2 use the seed forms TPLoWs / AbsDWs; hframe_s.py patches the seed to o_{M.take x}(r).
  The 2 TPLoW / 1 AbsDW failures of probe_hframe on graftM36 hold in the seed form.
- tools/probe_inv3_prefix.inv_fields VSmallF is the old form; use vsmallf.py (Lean form).

## PRIORITY 3: the `ua` field of HDropU is false too (Lean, Ytosk/lean/Ytosk/WfReM3.lean, green)
N (35 columns, 487-step trace, ua35.txt), not Bad2:
(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)(6,2,1)
(7,2,1)(8,2,0)(6,2,1)(7,2,1)(4,2,0)(5,3,1)(6,3,1)(7,2,0)(6,3,0)(7,4,1)(8,4,1)(9,2,0)(7,2,0)(5,3,0)(6,4,1)(7,4,1)
(8,2,0)(7,4,0)(8,5,1)
- i = x-1 = 33 = (7,4,0) upgrades to k = 30 = P0 i. V = v(29) = r0 + 1, r0 = psi_{psi(1)}(psi_{psi_{psi(2)}(0)}(0)),
  v(k) = psi_{r0}(0) = V + v(k). r0 not lhd v(k) (c = psi_{psi(1)+1}(0), u = 0), and the component
  psi_{psi_{psi(2)}(0)}(0) of V+1 is not < psi_{V+1}(0). Both disjuncts of ua fail.
- Lean: ua_core_false (Std, Cons; axioms propext), not_HDropU_of_inv, not_HDropU_of.
- hdropB.py: exact Lean ua and BumpWeakShapeSrcB. On graftM36: ua 23 failures / 12597 cases; wsB 0 cases.
  The codex UpgAbsXW0 (with NBParX, stronger) fails 1958 times there.
- remeasure.py bug fixed: importing residual_extension_t2 replaces residual_extension_local.run (A.run = run);
  the 'local' probe now keeps the original as run_local. rm_graftM36.jsonl's 'local' counts are the t2 run;
  use rm2_graftM36.jsonl.
