# WfInvA: the AbsDN family of Inv3V2 (2026-10-31)

Lean: Ytosk/lean/Ytosk/WfInvA1.lean (green, commit 728b11a7).
Scripts: probe_adn.py (exact Lean forms; FRDIR = where frame matrices go), graft_adn.py, show37.py, exp37.py,
deps_adn.lean (live users of each field from trio_terminates_main_V2_cur, `leanman check`).

## Live consumers (deps_adn.lean, getUsedConstants closure of the top)
- AbsDN: users Inv3V2.adn, TakeFrameV2.adn, base_adn, qr_final4_seedG / qr_final4SG / qr_final4S.
  Inv3V2.adn is read only by badOutT1 and expT1Out_V2, which pass it to qr_final4SG(S) -> qr_final4_seedG.
  qr_final4_seedG uses it at ONE place: hADs0 (q = r frame, i < x, DepX false i, e2 i != 0, dOf i = 0,
  bump case, DiagAt mu b_r mu W, W != A), at index seed = o_{M.take x}(r) via fsD_mono_eta from index 1.
  TakeFrameV2.adn: only packaging (inv3V2_take, inv3V2_takeD, t0_final_inv3V2D/G, hExp_t2_inv3V2, inv3V2_of_core).
  Dead: absDN_at, t0_absDN, T0AbsDNRes, AbsDNAt, QV2 (V3T0Col / V3ExpT1A transport is not on the live path).
- AbsDWs / AbsDWAt: Inv3V2.adwAt (badOutT1, expT1Out_V2) -> qr_final4SG -> qr_final3G -> qr_vloc
  (VLocZ absorption at index gamS mu b_r seed (m + d_i), all m, m + d_i >= 1).
- TPLoWs / TPLoWAt: Inv3V2.tplowAt -> qr_lkeep / qr_oloc / qr_vloc ((L)(ii) low part stays empty).
- TPLoN: qr_final4_seedG (hLs0).

## Measurements (probe_adn.py, all 49 handoff sets + 15 new family pkls, 18.6M matrices < SRO, 3.3M q=r frames)
- AbsDN: 2 / 2003590 (graftM36x only; the 38-column N, i = 31).  Restricted to the frame (AbsDN.fr, index 1): 0 / 445832.
- AbsDN0 (candidate, index seed, d_i = 0): 0 / 203672.  Same without NotNode (AbsDN0x): 0 / 203672.
- TPLoN: 0 / 824576.
- AbsDWs: 6 / 550230 (std_b 4, graftM36x 1, g36_2 1).  TPLoWs: 12 / 2028832 (std_b 8, graftM36x 2, g36_2 2).
  Smallest witness (std_b, 13 columns, standard, not Bad2, all HDropU fields hold in remeasure.py):
  M13 = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(4,0,0)(2,1,0)(3,2,1)(4,2,1)(5,0,0)(6,1,0)
  frame r = 11, o(r) = A = psi(Omega_1) (mu = 0, b = 0), seed = 1, d = 2 at columns 4, 8, 9.
  AbsDWs at i = 9: W = bumpW 9 = A, q = v(8) = psi(psi(psi(1))), eta = gamS 2 = psi(psi(1)), W[eta] = psi(psi(psi(1))) = q.
  TPLoWs at c = 4, 8: o(c) = psi_s(Omega_A), s = psi(psi(psi(1))), a = A, a[eta] = s, so Omega_{a[eta]} < Omega_{s+1}.
- Grafts (graft_adn.py; inserted children / larger siblings, row-1 lifts +2/+3, mutations, new last columns, M[2], M[3]
  prefixes; seeds = frames with AbsDN0 cases, plus all prefixes of the 38-column N and the 37-column M37):
  graftA1 59793 (163 seeds): AbsDN0 0 / 36907.  graftA2 77059 (461 seeds): AbsDN0 0 / 52063.
  graftA3 258623 (second generation, 1512 seeds from graftA1 frames; not committed, 105 MB): AbsDN0 0 / 488692.
  Global AbsDN: 17 failures in each (smallest 37 columns, i = 30, a graft of N); AbsDWs 24, TPLoWs 48 (all from the
  N / M37 seeds; the same mechanism as M13).
  Total for AbsDN0: 0 / 781334 cases.

## Recommendation
Replace the field `adn : AbsDN M ρ` of Inv3V2 / TakeFrameV2 by `adn0 : AbsDN0 M ρ rk` (WfInvA1). It is exactly the
consumer's use; AbsDN -> AbsDN0 (absDN0_of_absDN), so base_adn gives the base case. qr_final_inv3V2A shows the q = r engine
runs with it. Transport users (TakeFrameV2.adn in inv3V2_take etc.) change mechanically (HFrameV2 produces the field).
This does not repair Inv3V2: AbsDWs and TPLoWs are false on M13 (13 columns, std_b) and the engine qr_vloc / qr_lkeep
is false there (above).

## Why AbsDWs / TPLoWs cannot be weakened: the consumer itself is false at M13
N = M13[2] = M13.take 12 ++ [(6,0,0)]. Evaluator: v_N(9) = psi(psi(psi(1))) + psi(psi(psi(1))) = q + A[gamS 2],
while the q = r engine (qr_vloc, VLocZ with Zf 9 = gamS mu b_r seed (0 + d_9)) needs v_N(9) = fsD(v_M(9), Zf 9) = A[gamS 2]
(q absorbed). m = 0 is the n = 2 instance (A[gamS 2] is the observed new term), so the failing index k = d_i = 2 is used.
In both failures W = A (resp. a = A) at d >= 1: the term at the hole is the node itself, and a value q of the good part with
A[eta] <= q < A sits under it. No field-level weakening helps; the engine must allow non-absorbed summands
(v_N(i) = summands of vOpt(P1 i) not below W' ++ W') and a nonempty low part when a = A, d >= 1.
