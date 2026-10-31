# WfInvC: the qn path clause of hClR (T2SeedClV2R), 2026-10-31

## Problem
WfScout.T2SeedQNBaseR, third conjunct: at every path level u <= V = v(r) (PathLvAll), every g in
comps u t1 ++ comps u s' is below X1 = B + Omega_{t1}  (s' = qnS = v_N(q)). The s' half is false (WfReM2).

## Consumers of the clause (V3TopT2B)
1. t2SeedClV2_of_B -> t2SeedQNCl_of_base -> T2SeedQNCl (used by T2BelowRV2 / hBX). T2SeedQNCl only asks k >= 1:
   comps u t_k < B + Omega_{t_k} (or <= a comp of B or V).  qn_closed_tqN needs the s' comps below X_k for k >= 1 only;
   s' < t_k for k >= 1 (lt_shf), so g < B + Omega_{s'} suffices.
2. hQNG -> t2VRAQNDom0_of (Lc = [], B = 0): needs g <= Omega_{s'} (or <= comp of V).  g < Omega_{s'} suffices.
3. t2SeedQNDom_of1, t2SeedQNOT_of_base: do not use the path clause.

## New form (WfInvC1.T2SeedQNBaseRW)
  forall u path level, u <= V:
    (forall g in comps u t1, g < B + Omega_{t1})      [unchanged t1 half]
    (forall g in comps u s', g < B + Omega_{s'})      [was: < B + Omega_{t1}; t1 <= s' so weaker]
Lean (green): WfInvC1 qn_closed_tqN_W, t2SeedQNCl_of_W, t2VRAQNDom0_of_W, base_W_of_base;
WfInvC2 T2SeedClV2W, t2SeedClV2BW_of_W, bridges, t2SeedClV2W_of_R (old -> new), trio_terminates_main_V2_W
(the top with hClW for hClR; the other hypotheses unchanged).

## Measurements (qnpw.py; exact comps, paths_all = PathLvAll)
- new families (fam.log): qn sources 15620; S.lt (old) fails 536; S.OS (new) 0/207140; t1.lt 0/174280;
  consumers T2SeedQNCl k=1..4 0/2535860, T2VRAQNDom0 0/203245.
- all handoff sets incl. std_b, expPt2, ext2n2 (sets_part1.log + sets.log): qn sources 811159;
  S.lt fails 9976; S.OS 0/5838025; t1.lt 0/5650156; QNCl 0/52.3M; Dom0 0/14.7M.
- S.BV (g <= comp of B or V alone) fails often: the V-disjunct of T2SeedQNCl is not what holds.
- grafting attack (graftw.py): 168 seeds (old-clause failures of graftM36/graft4/graft2/lift1/graftM36x + 2 witnesses);
  mutations: child with row 1 up to e1 c + 3 under any column (first/last child), larger sibling (row 1 + 1, + 2) before i,
  lift of a subtree by row 1 + 1..4 (row-1 values >= 4), duplicate a subtree; gen 2 on 600 gen-1 matrices; bms -s = 1.
  graftw1 9306, graftw2 34209 (all qn sources): old S.lt fails 85176; new S.OS 0/1156461; t1.lt 0/364902;
  QNCl 0/13.0M; Dom0 0/1.16M (graftw_meas.log).
- Caveat: the probes check Std and the qn shape only, not the StepCtxT2 premises (Inv3V2 is itself false, WfReM4).
- The new s' half is not proved: it is a bound of the components of v_N(q) at the path levels of r. Next step:
  derive it from the standard form of the ancestors' terms along the path (a VSmallRAll-type fact), or keep it as the
  residual T2SeedClV2W.
