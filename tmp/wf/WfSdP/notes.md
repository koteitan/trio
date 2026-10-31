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
