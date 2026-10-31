# WfSdP: seed producers (2026-11-01)

## (2) SeedC2 from the PV2 drop conclusion (WfSdP1, green)
Measured (seedp.py, seedp_graft.jsonl): in every weak seed case of t = 1, q = r (graftD 903, graftE 4488):
w' = V + 1 (V = v(P1 r)), r = x - 1, P0 r != P1 r, and WCS2(v(r), w') holds (0 failures).
`WCS2 (v P0 r) w'` (the PV2 form) also holds but is about the wrong subscript; comps of V are not always dominated by
comps of v(r) (domV fails 3 times on graftE; there g <= Om_{w'}).
Lean:
- `seedC2_weak_of_wcs2`: AllGeT Om_{mu+1} b, isOT Om_{w'}, w' < mu, WCS2 mu w'  ->  SeedOK mu b_r mu Om_{w'} and
  psi_mu(b + Om_{w'}) lhd psi_mu(b_r)  (comps_a is empty since w' < mu; dom from WCS2; lhd by lhd_weak_childA from
  psi_mu(b) lhd psi_mu(b_r) = lhd_psi (lhd_prefix)).
- `qr_seedC2_of`: copy of qr_seedC_of2 with conclusion SeedC2 and hUAs in the form strong or WCS2 (v r) (V + 1).
- `UAwR M ρ x` := for i = x - 1, upg i = k, v(k) = V + W, W != 0: strong or WCS2 (v(i)) (V + 1).
- `qr_final4SGW2`: qr_final4SGW without hseedC (takes UAwR and NoBad3 or r + 2 = len).
Measurement of UAwR (uawr.py, exact hX1 enumeration of uaw2.py with WCS2(v(i), V+1)):
| data | cases | weak | UAwR fails |
|---|---:|---:|---:|
| graftD | 16502 | 11020 | 0 |
| graftE | 24110 | 16951 | 0 |
| graftA | 3307 | 937 | 0 |
| graftB | 80228 | 756 | 0 |
| ext2 | 248916 | 0 | 0 |
| expP | 105898 | 33 | 0 |
families / all handoff sets / graftF,G,H,Q: uawr_fam.jsonl, uawr_sets.jsonl (see below).
Remaining: UAwR is a residual (not derived from UAw2: WCSP2 is relative to v(P0 i), UAwR to v(i)).

## (3) bump frame of drop_all_hardW2 with BumpAbsCB2 (WfSdP2, green)
`g_levelB2`, `bump_relB2`, `bump_dropB2`: copies of V3BumpDropB with PV2 / WCSP2 / WeakCS2 / BumpAbsCB2 and
`BumpWeakSrcB2 = BumpWeakShapeSrcB and WeakCS2`. `drop_all_hardW2B`: drop_all_hardW2 with hBump := bump_dropB2.
(BumpWeakSrcB does not give BumpWeakSrcB2 without one <= v'(i); not needed: the hypothesis is taken in the new form.)

## (1) the producers of the carried property and the shared interface (WfSdP3-6, green)
Live producers (expdeps.lean: constants under trio_terminates_main_V2_cur whose type mentions ExpStepT1/HoleData):
18 producers (expStep_vrleS, frameClosedOmN_t1S, expStep_frameClosed_t1S, expStep_frameOT(_t1), G.frameQROmN_t1S,
G.expStep_ph3c_t1S, G.expStep_fc3_t1S, expStep_rootP_t1, expStep_bumpDec_t1, mu_lt_viS, vsf_frameS, expStep_vsmallF2S,
expStep_frameMapT1, expStep_closure/core/vsmallF_pass/core_vsmallF_pass_inv3V2). Readers of HoleData.S among them:
frameClosedOmN_t1S, G.frameQROmN_t1S (only SeedOK v(r)), vsf_frameS (hole_dom: needs fsD(t, gamma_k) lhd t at the
diagonal points, i.e. SeedOK at every diagonal point). The producers named in the task (V3ExpT1A AbsD/AbsUW/AbsDN at
271/369/466, V3ExpT1L, V3PT1, V3ExpT1SL) are NOT live under the current top.
Finding: ExpStepT1W/HoleDataW (WfSdH1) is too weak for vsf_frameS: HokQ gives only the descent fsD(t, gamma_k) < t,
hole_dom needs the domination (Lhd). New interface (WfSdP3):
- OkD mu br vr seed := forall a' <= vr, DiagAt a' br mu t, isOT t, (k = 0 -> SeedOK a' br mu seed) ->
  isOT (fsD t gamma_k) and fsD t gamma_k lhd t.  okD_of_S (old hS), okD_of_S1 (SeedOK at gamma_1 everywhere),
  okD_of_seedC2W (SeedC2: strong -> old hS, weak -> gamma_1 via seedOK1_of_lhd).
- ExpStepT1D: witness HoleDataW and OkD, index-0 condition "SeedOK a' at every diagonal point a' <= vr of the D value"
  (q = r: only point is v(r), qr_only_mu_col + SeedOK v(r); q != r: old hS).
- expStepT1_of_D: ExpStepT1D P -> ExpStepT1 P. This is how the q != r chain (V3ChainT1.t1_chain, old HoleData, no
  index-0 witness) shares the producers: every D producer is an old producer.
- hokQ_of_okD, hole_domD.
WfSdP4: the 18 live producers copied over ExpStepT1D (suffix D); WfSdP5: qr_chainD .. qr_final4SGD, qr_final4SGD2
(no hseedC); WfSdP6: qr_t1_D = the q = r branch of V3T1Bad.badOutT1 with PV2 drop, SeedC2 from UAwR, D producers
(base hP1 still a hypothesis, as in badOutT1).

## UAwRA (WfSdP7): one hypothesis for the seed and the base
UAwRA = UAwR at every level u (the VrDomQ form: g in comps u (V+1) -> g <= Om_{V+1} or dominated in comps u v(x-1)).
It gives UAwR (WCSA.toWCS2) and the base FrameMapT1 and VrDomQ (frameMapT1_takeG3, replacing SmallSelf(V+1)).
qr_t1_D2: the q = r branch with only T1Core at M.take x as the base hypothesis.
Measurement (uawra.py, exact enumeration as uaw2.py):
- graftD, graftE, graftF/F_a/F_b, graftG, graftQ1, graftQ2, graftH and the 15 family pkls: 24 sets, 61694 weak cases, 0 fail
  (uawra_graft.jsonl).
- graft attack graftR (graftR.py: 40 smallest seeds with domV false, gen1+gen2, 31558 matrices): 4717 weak cases
  (2626 with domV false), 0 fail (uawra_graftR.jsonl).
- 50 handoff sets (18,509,666 matrices incl. std_b): 25769 weak cases, 0 fail (uawra_sets.jsonl).
Not derived in Lean: PV2/UAw2 give WCS2 relative to v(P0(x-1)); UAwRA is relative to v(x-1) = sf(V + last v(k)),
where sf may absorb summands of V (domV false), so the bound g <= Om_{V+1} is needed there.
