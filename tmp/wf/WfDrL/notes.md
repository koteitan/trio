# WfDrL: the drop lemma redesign finished (2026-10-31)

## (1) Measurements (tmp/wf/WfDrE/pv2.py, uaw2.py, seedc.py; tmp/wf/WfDrL/probe_dp0.py)
PV2 = PV with WCS2 (WfDrE1). UAw2 = hX1 of drop_all_hardW2 (strong absorption or WCSP2(V+1) at x-1).
SeedC2 = WfDrE2.SeedC2 (seed lhd o(r), or weak seed with SeedOK mu and gamma_1 lhd o(r)).

| data | PV fails | PV2 fails | UAw fails | UAw2 fails | SeedC2 weak seeds / fails |
|---|---|---|---|---|---|
| 15 families (members, WfDrE pv2_fam + WfDrL uaw2_fam) | 0 | 0 | 0 | 0 | - |
| 34 small handoff sets (WfDrE pv2_small 26 sets + WfDrL pv2_small2 8 sets; uaw2_small) | 0 | 0 | see uaw2_small.jsonl | see uaw2_small.jsonl | - |
| graftD (37749) | 19 | 0 | - | - | 903 / 0 |
| graftE (54990, new) | 901 | 0 | 786 | 0 | 4488 / 0 (old SeedC fails 4333) |
| big sets, 100k sample each | pv2_big.jsonl | | | uaw2_big.jsonl | |

graftE (tmp/wf/WfDrE/graftE.py, graftE.pkl): seeds = the 19 PV failures + the 60 smallest qr-SeedC failures of graftD,
their prefixes ending at the last 3 columns (209 bases); gen1 = WfReM graft.gen_all (children of every column, one-column
mutations, append) + row-1 lifts b in {4,5,6} + a larger sibling of x-1 (WfInvD graftD.extra) + M[2], M[3] prefixes;
gen2 = the same on 300 random gen1 matrices. Kept bms -s = 1 and < SRO. 19343 + 35644 new = 54990.

## (2) Rewiring the consumers (Lean, green)
- WfDrL1: `PVnc` = PV without the component condition; `PV.toNC`, `PV2.toNC`, `PVnc.le`, `PV2.le`,
  `hdrop_nc_of_pv2`, `hdrop_nc_of_pv`, `hdrop_pv2_of_pv`. NC copies of dep_strict0, o_r_strict0 (with o_strict_frame,
  v_strict_bump, new_rewrite_same_v, arg0_take), good3_take (cl_take_vals), frameMapT1_take(G) (rewrite_take,
  frame_take_rw). These read only `lhdE or (weak and CntX)` and isOT, so PV and PV2 both feed them.
- WfDrL2: the t = 0 weak engine with PV2/WCS2: PO.zero_of_ne2, PO.zero_of_strong2, s1_core_weak2 (self_small_weakA2),
  po_lhd_or_weak2 (returns WCS2), lhd_t0_of2, lhd_or_weak_t02, t0_S1W2.
- WfDrL4: 67 live consumers with PV2 (all of the live chain except the producers), e.g. qr_final3G2, qr_final4SG2,
  t0_otdG2, t0_coreG2, root_drop_any2, root_drop_X2, inv3V2_takeD2, T2UpgAbs.qnu_take_of_drop_full2,
  vsmallRAll_take2, frameMap_N_t02, t1_main_dropG2, t1_main_vlocSG2, dep_strict0X2, t2SVc0'_of_drop2.
- Generator: gen.py / bulk.py (extract.py copies a declaration with its active section variables; renames the
  copied names; PV -> PV2). Exact live list: pvdeps.lean (Lean, getUsedConstants from trio_terminates_main_V2_cur).
- Coverage of all 111 live constants whose type mentions PV/WCSP/WeakCS: coverage.txt.
  67 WfDrL4, 5 WfDrL2 (+ NC copies in WfDrL1), 22 the drop lemma itself (replaced by WfDrE1.drop_all_hardW2),
  6 producer wrappers that call the old drop lemma (t1_drop_of_fields, g0_drop_rel, qr_dropSeed, StepCtxB.hdrop,
  hdrop_of_U, t2_drop_ctx: their output converts by PV.toPV2), 6 structure fields (DropResB, DropResHB, Res3W,
  T0DropF), and 4 internal readers not copied: T2AbsNWeak.weak_of_drop_failure (reads WCSP of the hypothesis
  BumpAbsCB, not PV: needs BumpAbsCB with WCSP2), t0_vsmallF_atC (reads WCS via T0DropF.po; WCS2 gives exactly the
  needed g <= psi(v'(r))), seedOT_qr (PV.le only), WfH7W.qnDom_simpleB2.

## (3) The index-0 obligation of hok_of_seedC2 (Lean, green, WfDrL3)
Measured (probe_dp0.py): in q = r frames, columns in D with lift count d = 0 have only mu as a diagonal point
(graftD sample 3000: 95 weak + 407 lhd cases, 0 exceptions); with d > 0 the root's 0 and p(1) occur (so d = 0 matters).
Proof: `DiagAt.unique` - DiagAt follows a fixed path (last summand, argument, subscript) and stops at the first
psi_a(b); if b has no diagonal point itself (not_diag_br for b_r = b + Om_{mu+1}) the point is unique.
`qr_diag0` (existing) gives DiagAt mu b_r mu t at d = 0, so `qr_diag_only_mu`; `hok_col_of_seedC2`: every index
m + d of a column with lift count d.

## Next
- The q = r chain still takes `hS : forall a' <= mu, SeedOK a' b_r mu seed` (V3QRLocV, V3QRLocOA, V3QRFinal2): false
  for weak seeds at a' = 0. Replace it by `hok0 : forall t k, isOT t -> HoleT mu b_r mu t ->
  (k = 0 -> forall a', DiagAt a' b_r mu t -> a' = mu) -> ...` (= hok_of_seedC2) and supply the condition at each use
  (hok at m + dOf, hokzeta inside omega_fsD_hole_Q on subterms of the diagonal path: DiagAt.rest_inv / arg_inv / last').
- The top level: produce hdrop from drop_all_hardW2 (hypotheses hBump = bump frames with PV2, WeakCS2, hX1 = UAw2)
  and feed the PV2 copies.
