# WfInvD: repairing HDropU (2026-10-31)

## Consumers (Lean)
ua field (DropResHB.ua = strong ∨ (WCSP ∧ comps z (V+1) < ψ_{V+1}(0))):
- every drop lemma (pv_of_hardB / drop_all_hardB, drop_allB, V3DropMain:516/724, V3DropR, V3DropWeak0): reads
  strong ∨ WCSP (+ NBParX in the old ones); the comps conjunct is discarded (`obtain ⟨hwc, -⟩`).
- comps conjunct is read only at t = 1: qr_dropSeed → qr_seedC_of (SeedC: o'(r) ◁ o(r) ∨ (w' < v(r) ∧ SmallSelf w')),
  and frameMapT1_takeG (VrDomQ, case P0 x = r = x−1).
- NBParX (from ¬Bad2 in hDropV2W_of_U): old_target_of_failure / strong_or_old_target (t = 2), UpgAbsXW.toX_xm1 (t = 0).
ab conjunct (BumpAbsC on ¬Bad2 ∨ e1 x = 0):
- t = 1 engines (t1_drop_of_fields, qr_dropSeed, t1_main_final, V3Inv2 qr/qn): only through bump_drop → drop conclusion;
  bump_dropB with BumpAbsCB gives the same conclusion.
- t = 2: Res3W.ab → t2_absWN_take (AbsWN M (M.take x)); V3MainV2:145/220 absWN_of_absC.
- t = 0: t0AbsW_of_U → absWN_take_t0 (AbsWN M (M.take x)).

## Measurements (invd.py; fam2.jsonl = the 15 new families, 133298 matrices; sets_part1.jsonl = the 34 smallest
## handoff sets, 462122 matrices; graftD.jsonl = new grafts, 37749 matrices)
| | families | sets (34) | graftD |
|---|---:|---:|---:|
| ua cases | 73219 | 275718 | 16502 |
| ua comps conjunct fails (t0/t1/t2) | 370 total, 39 at t1 L=1 | 0 | 1628/2946/897 |
| UAw (strong ∨ WCSP) fails | 0 | 0 | 17 (all: x−1 upgrades to P0(x−1)) |
| BumpAbsC fails outside Bad2 (t0/t1/t2) | 2/8/9 | 0 | 21/71/100 |
| BumpAbsC fails without BadAbsShape M (M.take x) | 0 | 0 | 2 (both Bad2, t2) |
| B2X (P0 x = x−1, e1 x ≠ 0, ¬BumpAbsC, not Bad2) | 9 | 0 | 106 |
| qr SeedC (t1, P0 x = P1 x) fails, not Bad2 | 9 / 7167 | 0 / 73292 | 741 / 3576 |
| VrDomQ fails | (not run) | (not run) | 0 / 3576 |
| drop conclusion PV fails | 0 | 0 | 17 (¬Bad2) + 2 (Bad2) |
The 16 largest handoff sets (ext1x … std_b) were not run this round (hours at 4 processes); HDropU itself had
been measured there with no exception, and every form below is implied by HDropU, so only SeedC/UAw/PV are new there.

## Witnesses (all bms -s = 1)
- qr SeedC false, 21 columns: (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(4,1,1)(5,1,1)(6,1,0)(4,1,1)(5,1,1)
  (6,0,0)(2,1,0)(3,2,1)(4,2,1)(5,1,0)(6,1,0)(6,1,0)(4,2,0)(5,3,0): r = x−1 = 19 upgrades to 14, o'(r) = ψ_{V+1}(0),
  not ◁ o(r); SmallSelf(V+1) false (component ψ_{ψ_{ψ(ψ(1))}(0)}(0)). VrDomQ holds.
- PV (drop conclusion) false outside Bad2, 37 columns: …(13,1,0)(14,1,0)(12,3,0)(12,0,0) (prefix = M36 frame up to
  (13,1,0)): i = x−1 = 35 = (12,3,0) upgrades to its row-0 parent 31; v'(35) = V+1 with V = v(30) ∋ ψ_{ψ(2)}(0);
  not ◁ v(35), WCSP false (WCS (v(31)) fails). So UAw is false, and no hypothesis form of the current drop lemma holds.
- PV false on Bad2, 40 columns: …(13,1,0)(14,2,1)(12,3,0)(11,3,1)(12,3,1)(13,1,0)(14,2,1), i = 35 < x−1 (upgrades to
  36): WeakCS (field ws of DropResHB) false.
  (Inv3V2 of these matrices was not checked in Python this round.)

## Lean (green): WfInvD1, WfInvD2
- drop_all_hardW / pv_of_hardW: the drop lemma with hX1 = strong ∨ WCSP.
- UAg (comps only at e2 x = 0), DropResHBg, HDropUg, hDropUg_of_U, UAg.seed/.toW0/.nbx, hdrop_of_Ug, rootBad_of_T2g.
- BumpAbsCX (BumpAbsC ∨ WfAbsW.BadAbsShape M (M.take x)), absWNx_of_absCX (t = 2), absWNx_take_t0 (t = 0),
  HDropUx (BumpAbsCX at t0 and t2 ¬Bad2), hDropUx_of_U, hdrop_of_Ux.
- UAw, DropResHBw, HDropUw (unconditional BumpAbsCX), hdrop_of_Uw.
Status vs data: HDropUg false (t2 ab, families); HDropUx survives families/sets, but its ua (UAg) fails at t1 (families,
39) and UAg/UAw fail on graftD (17); HDropUw fails on graftD (2 BadAbsShape, Bad2; 17 UAw).
