# WfSdH: the drop/seed rewiring of the q = r chain (2026-11-01)

## Problem
The q = r chain (fsD form: qr_oloc, qr_vloc, qr_final, qr_final2, qr_final3G2, qr_final4_seedG2, qr_final4SG2)
took `hS : forall a' <= mu, SeedOK a' b_r mu seed`. For a weak seed `Omega_{w'}` (weak branch of WfDrE2.SeedC2) this
is false at `a' = 0` (279 cases on graftD, WfDrE notes). The old seed condition with `SmallSelf` is false on graftD.
`hS` also sits inside `HoleData` (field `S`), which `qr_chain` hands to the carried property `ExpStepT1`.

## Lean (all green; leanman build Ytosk.WfSdH1..4)
- WfSdH1
  - `HokQ mu br vr seed` := forall t k, isOT t -> HoleT mu br vr t -> (k = 0 -> every diagonal point of t is vr) ->
    fsD t gamma_k standard and < t.  `hokQ_of_S` (old hS), `hokQ_of_seedC2` (weak branch, = hok_of_seedC2).
  - `HoleDataW`: HoleData with `S` replaced by `Sr : SeedOK vr br mu seed` and `ok : HokQ`. `HoleData.toW`.
  - `ExpStepT1AtW / ExpStepT1W`: ExpStepT1 over HoleDataW; the index witness also gives, at index 0, that vr is a
    diagonal point of every D value (so a producer can discharge the index-0 condition of `ok`).
  - `omega_fsD_hole_QW`: omega_fsD_hole_Q with the descent asked only on terms t whose diagonal points are diagonal
    points of Y (used at Y itself and at the low part lo of the argument: DiagAt.append + DiagAt.arg).
  - `qr_chainW`, `qr_mainW` (copies; qr_mainW takes `hdiag0 : dOf i = 0 -> DiagAt mu br mu (valB rho bb i)`).
  - `qr_diag_col` (qr_diag0 through dOf: depL_of_depX, dOf_v/dOf_o), `qr_only_mu_col` (+ diag_only_mu).
- WfSdH2: `qr_olocW`, `qr_vlocW` (section hyp hS -> hSr, hok0). Index-0 condition supplied at:
  the v/o column values (qr_only_mu_col), last v(i+1) in the upgrade frame (DiagAt.last_g of qr_diag_col),
  the bump frame: o(k) (qr_diag_col), G = sum K + o(k) (DiagAt.append), P + omega^G (diag_omega, append), and inside
  omega_fsD_hole_QW on subterms (via "diagonal points of t are those of Y" + DiagAt.unique_br).
- WfSdH3: `qr_finalW`, `qr_final2W` (hSr, hok0, ExpStepT1W), `qr_final3GW`, `qr_final4_seedGW`, `qr_final4SGW`
  (PV2 drop conclusion, hseedC : SeedC2 mu (qrB) seed; strong branch -> old hS -> hokQ_of_S, weak -> hokQ_of_seedC2).
- WfSdH4: `BumpAbsCB2` (BumpAbsCB with WCSP2), `BumpAbsCB.toB2`, `BumpAbsC.toB2`,
  `T2AbsNWeak.weak_of_drop_failure2`, `T2AbsNWeak.absorption_of_weak_branch2`.

## Measurement of BumpAbsCB2 (abcb2.py: exact Lean guard of BumpAbsCB, copied from WfInvD/invd.py)
See abcb2_graft.jsonl (graftE, graftD), abcb2_fam.jsonl (15 families), abcb2_small.jsonl (34 small sets).
| data | matrices | guarded cases | absorption fails | old weak branch (WCSP) holds | WCSP2 holds | failures |
|---|---:|---:|---:|---:|---:|---:|
| graftE | 54990 | 1282078 | 492 | 492 | 492 | 0 |
| graftD | 37749 | 765146 | 555 | 555 | 555 | 0 |
| 15 families | 133298 | - | 899 | 899 | 899 | 0 |
| 34 small sets | 533077 | - | 36 | 36 | 36 | 0 |
No absorption failure at i = x. So BumpAbsCB itself has no counterexample here; BumpAbsCB2 is weaker and also holds.
The PV failures of graftE (WfDrE) are at upgrade columns (ua / UAw), not at the bump absorption.

## Remaining
- Producers of `ExpStepT1W` for the live carried property: the ExpStepT1 producers read `hHD.S` only at `vr`
  (-> `Sr`) and through `hok_of_holeT ... hHD.S` on W / last v (V3ExpT1A 271/369/466; V3ExpT1, V3ExpT1L, V3ExpT1V,
  V3ExpT1SL, V3PT1, V3PT1G) -> `hHD.ok` with the index-0 condition from the witness (DiagAt vr at D values, then
  append/omega/last as in qr_vlocW). The q != r chain (V3ChainT1) would pass `HoleData.toW` but has no index-0
  witness; a shared interface needs the witness to be optional (e.g. `ok` unconditional when S holds).
- A producer of `SeedC2` from the PV2 drop conclusion (qr_seedC_of2 gives the old SmallSelf form).
- bump_dropB with BumpAbsCB2 (the bump frame hBump.1 of drop_all_hardW2).
