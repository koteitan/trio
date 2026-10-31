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

## PRIORITY 0: the invariant field AbsDN is false; HFrameV2 is false; Inv3V2 fails on a standard matrix
(Lean, Ytosk/lean/Ytosk/WfReM4.lean, green; axioms propext / Classical.choice / Quot.sound)
N (38 columns, 150-step trace, adn38.txt), an expansion prefix in graftM36x:
(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)(6,2,1)
(7,2,1)(8,2,0)(6,2,1)(7,2,1)(8,1,0)(9,2,1)(10,2,1)(11,2,0)(9,2,1)(10,2,1)(11,1,0)(12,0,0)(13,1,1)(14,1,1)(10,2,0)
(11,3,1)(12,3,1)(13,1,0)(14,0,0)(15,1,1)(16,1,1)(17,1,0)
- i = 31 = (11,3,1): W = bumpW(31) = psi_{psi(1)}(psi_{psi(1)}(psi_{psi(1)}(psi(Omega_{Omega_1})))) (OHole, cof omega,
  not a node). q0 = psi_{psi(1)}(psi_{psi(1)}(psi_{psi(1)}(psi(Omega_{psi(2)})))) in summands v(30) = v(P1 31),
  q0 < W, not q0 < W[1].
- not_absDN, no_inv3V2 (no valuation has Inv3V2), not_HFrameV2 (premises Std/Cons/Rk/Good3 proved),
  not_hInvV2_all_hyps (hInvV2_all's 9 hypotheses inconsistent).
- graftM36x: 2 AbsDN failures (38 and 72 columns, the second is a copy). Earlier sets: 0.
- 38 = the prefix (14,0,0)(15,1,1)(16,1,1)(17,1,0) after the 34-column frame of the 36-column M: a t = 0 step.

## graftM36x (expand_fam.py): M[2], M[3] of 1594 graftM36 matrices, prefixes past the bad root: 18227.

## Counts (rm2_graftM36.jsonl = graftM36 24690 with fixed harness; rm_graftM36.jsonl for t2/vraesc/qndom/canon/b2s/
## sib/plow/term/vanc; rm_graftM36x.jsonl = graftM36x 18227), failures / cases
- HDropU: ab 2 (graftM36) + 2 (x); ua 23/12597 and 75/6504; wsB 0/0 and 0/349; HardArg 0/109081, VSmallNew 0/141085,
  WeakCS 0/4475. FALSE (WfReM1, WfReM3).
- HFrameV2: AbsDN 0 / 2 (x) FALSE (WfReM4); seed TPLoWs 0/64, 2/17343 (x, 37 columns
  ...(12,1,0)(12,0,0)(13,1,1)(14,1,1)(15,0,0)(10,2,0)(11,3,1)(12,3,1)(13,1,0)(14,2,0), Python only); AbsDWs 0/39, 1/7585 (same).
- HLeafV2 (TP1LeafG, TP1WLeafG): 0 antecedents.
- HBumpExt: 0/68990241 (graftM36).
- hClR (T2SeedClV2R): SeedCl.qn.path 255/121945 and 3 (x) FALSE (WfReM2). Smaller witness (28 columns, Python premises
  hold incl. exact ua/wsB): (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)
  (4,2,1)(5,1,0)(6,2,1)(7,2,1)(8,2,0)(6,2,0)(7,3,1)(8,3,1)(9,2,0)(10,3,1)(4,2,0)(5,3,1)(6,3,1)(7,2,0)(6,3,1).
  Other SeedCl fields: 0.
- hPRE / hDomQ seeds (SeedPR.qn.*, Seed.qr/qn/sv/C.*): 0 (SeedPR.qn.iter 21780, Seed.qr.dom 32644, Seed.qn.dom2 7262).
- hVU T2VAncUse (usefld): vdomf 0/120673, edge 0/49192; x: 0/32495, 0/19828. (T2VAncStep is a diagnostic: 3592 fails.)
- hCan (canon.py): 0/3137, 0/1870.  hVCp T2VRACopyEsc: 0/130, 0/30.  hAG KAG: KA 0/100960, KG 0/27591.
- T2QNDomBad2 (qndom.py): weak simple frames 316 and 101, dom true in all.
- B2LevS / B2UpgV (fr6 all): S.FAIL 0 (i0 76526, zero 181218); i1 frames 0, so B2UpgV has no antecedent.
- H7WSib (probe_sib): 0 frames / 4 frames (x), 0 fail.  TermHi (WfTerm/probe_v): 0 frames.
- PLowRes (WfPLow/probe_o): frames a.B2 1935 / 270, b.B2 42 / 202; no failure tag.
- T2CBadOut: T2CBad sources 2; not measured further (its conclusion is Inv3V2 of M[n], which WfReM4 shows can fail).
