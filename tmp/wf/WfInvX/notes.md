# WfInvX: audit of the invariant layer (2026-10-31)

## Checker
`audit.py`: one checker for every field of `Inv3V2` (V3Inv2.lean, 25 fields) and of `SInv` / `SInvX` / `RowJ` /
`UAT` / `UAB` (structural, 13 fields). Lean form per field (see the docstring of audit.py):
- structural: own literal port of Eval.lean `par` / `upg` / `children` / `topped` / `bump`; compared with the Python
  evaluator on every matrix (`internal.struct_mismatch` = 0 on all runs).
- `cons`: o(i) = sf(psi(v i, sumN(children.map cnt), 0)), v(i) = vRhs (Val.lean), recomputed from the evaluator values.
- `rank`: exists rk with Rk N rk iff the Rk constraint graph is acyclic (finite DFS); compared with the evaluator
  (`internal.rank_vs_eval` = 0).
- `fc` (FrameClosed): FrameDom decided by tools/fdom_exact.frame_dom (not the old sufficient test closedZ).
- `ph` (PH3cG): cutsNSG / cutsHG ported from V3PDef; `tp1` / `tp1w` (TP1C / TP1WC): counted children only
  (tools/probe_inv3_prefix.inv_fields TP1 checks all children: stronger).
- `tplow` / `adw`: TPLoWs / AbsDWs at the seed (WfReM/hframe_s), worst k = max 1 d (gamS_mono, fsD_mono_eta).
- `ads`, `auwl`, `auw0`, `tplon`, `adn`: tools/probe_frame7; `aus`, `tplos`, `vra`: tools/probe_inv2; `trigs`:
  tools/probe_trigs0. The probes' `M < SRO` filter is disabled.
- Sanity: hand-made non-standard matrices make R0P, R1S, SibDec, Z1C, Z2, R12, good, ph, tp1, fc3, trigs fail.
- Re-run of graftM36x reproduces WfReM: adn 2, TPLoWs 2, AbsDWs 1.

## Family run (fam_run.py, fam.jsonl, summary_fam.json)
Set = every prefix (length >= 2) of every member M of the 15 new family pkls and of M[2], M[3]
(tools/trio.expand), deduplicated: 4,691,563 standard matrices (381,230 maximal ones, up to 324 columns).

Failing fields (cases failed / matrices failed / smallest standard witness length; bms -s = 1):
- adn (AbsDN): 474 / 474 / 27 columns  [known: WfReM4 had 38 columns]
- ads (AbsDS): 6 / 6 / 26 columns      [NEW, Lean: WfInvX1]
- tplos (TPLoS): 12 / 6 / 26 columns   [NEW, Lean: WfInvX1, same matrix]
- tplow (TPLoWs): 90 / 45 / 35 columns [known, Python only]
- adw (AbsDWs): 46 / 45 / 35 columns   [known, Python only]
Every other field: 0 failures (cases in summary_fam.json).

## WfInvX1.lean (green): AbsDS and TPLoS are false
N = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(4,1,1)(5,1,1)(6,0,0)(7,1,1)(8,1,1)(9,0,0)(10,1,1)(11,1,1)(11,1,0)
(12,1,0)(13,0,0)(10,0,0)(2,1,0)(3,2,1)(4,2,1)(5,0,0)(6,1,1)(7,1,1)(8,1,0), 26 columns, Std (269-step trace).
x = 25, r = P_1 x = 22, P_0 x = 24 != r (t = 1, q != r). o(r) = psi(Omega_{Omega_1}); seed = o_{N.take 25}(r) = psi(Omega_{psi(2)}).
- AbsDS at i = 20: W = bumpW(20) = psi(Omega_{Omega_1}), a summand q0 of v(19) has q0 < W, not q0 < W[seed].
- TPLoS at c = 4: a = psi(Omega_{Omega_1}), psi_{a[seed]}(0) < Omega_{s+1}.
Theorems: not_absDS, not_tpLoS, no_inv3V2 (by ads), no_inv3V2' (by tplos), main, not_HFrameV2.
Axioms: propext, Classical.choice, Quot.sound.

## Consumers of the failing fields (live chain only)
- adn: qr_final4_seedG (V3QRFinal4, hADN -> hADs0) via qr_final4SG / qr_final4S / qr_final_inv3V2; only at the last-column
  q = r frame, D v-call i with dOf i = 0, index = seed (WfInvA1 AbsDN0 isolates this).
- ads: hADζ_of_absDS (V3SeedFields) in t1_main_vlocSG (V3VLocT1:1806) via t1_main_vlocS / qn_final_inv3V2; used for every
  m, including m = 0 where ζ = gamS 0 = seed. The NEW counterexample fails exactly at ζ = seed, so the m = 0 use is false.
- tplos: hTPLζ_of_tplos (V3VLocT1:1812, same m-loop, m = 0 = seed) and hLo_of_TPLS (V3SeedFields:184, at 1847).
- tplow: qr_lkeep (V3QRLocV, section variable hTPL, at k = m + dOf c >= 1) and qr_oloc (V3QRLocOA:208).
- adw: qr_vloc (V3QRLocV:431, at k = m + dOf i when it is >= 1).
All other uses are transport (TakeFrameV2 fields, V3TakeInv2, V3ExpT1Inv2, V3ExpT2Inv2, V3T0Bad, V3ExpInv2).

## Old sets run (sets.jsonl, summary_sets.json): all 52 pkls of tmp/ytosk-handoff/sets, 18,509,666 matrices
- tplow (TPLoWs) 8 cases / 4 matrices, adw (AbsDWs) 4 / 4, all in std_b; smallest standard witness 13 columns:
  (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(4,0,0)(2,1,0)(3,2,1)(4,2,1)(5,0,0)(6,1,0)
  (TPLoWs at c = 4, AbsDWs at i = 9). Much smaller than the 35/37-column family witnesses. Python only.
- Structural failures BumpLeaf 6, UAB 5, UAT 4, Z1C 1, rank 5 (eval cycle 5), all in cbadext / t0ext: every failing
  matrix is >= SRO (SRO itself or above it), so outside Std \ {SRO}; no structural field fails below SRO.
- Every other field: 0 failures.

## Combined (summary.json): 23,201,229 matrices. False fields of Inv3V2 below SRO:
adn (27 col), ads (26, Lean WfInvX1), tplos (26, Lean WfInvX1), tplow (13), adw (13). Everything else holds on all.

## (4) Descent (descent.py, descent.json)
Every family member and every prefix (1,418,779 matrices), n = 1, 2, 3: 4,256,337 pairs, all with
Ev(M[n]).value() < Ev(M).value() (tools/ytosk_eval.Ev, tools/trio.expand); no evaluation failure.
