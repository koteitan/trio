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
