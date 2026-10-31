/-
**WfSdP6: the `t = 1`, `q = r` branch of `badOutT1` with the new seed producers (2026-11-01).**

`qr_t1_D`: the `q = r` branch of `V3T1Bad.badOutT1` (`hfin`) with
- the drop conclusion `PO ∧ PV2` (from `drop_all_hardW2B`, WfSdP2) in place of `PV`,
- the seed condition `SeedC2` produced from it and `UAwR` (`qr_seedC2_of`, WfSdP1) in place of the `SmallSelf` form,
- the carried property `T1Core ∧ (FrameMapT1 ∧ VrDomQ)` produced over `ExpStepT1D` (WfSdP4) and the chain
  `qr_final4SGD2` (WfSdP5).
The base `hP1` (the carried property at `M.take x`) stays a hypothesis.
-/
import Ytosk.WfSdP5
import Ytosk.V3T1Bad

namespace Ytosk

open T

theorem qr_t1_D {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V2 M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hL0 : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r))
    (hr : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    (hPR : PassRootRes M r L ρ)
    (hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rk) i ∧ PV2 M ρ (drop1 M (r + L) rk) i)
    (hUAR : UAwR M ρ (r + L)) (hr2 : r + 2 = M.length)
    (hbase : T1Core r ρ (M.take (r + L)) (drop1 M (r + L) rk) ∧
      (FrameMapT1 M ρ r L (M.take (r + L)) (drop1 M (r + L) rk) ∧
        VrDomQ M ρ r L (M.take (r + L)) (drop1 M (r + L) rk))) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
      Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) rkN ∧
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
      (T1Core r ρ (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
        (FrameMapT1 M ρ r L (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
          VrDomQ M ρ r L (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN)) ∧
      isOT (root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN) = true ∧
      root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN < root M ρ := by
  have hstep : ExpStepT1D (fun N σ => T1Core r ρ N σ ∧ (FrameMapT1 M ρ r L N σ ∧ VrDomQ M ρ r L N σ)) M r L
      (entry M 0 (r + L) - entry M 0 r) ρ :=
    expStepD_and (expStep_core_vsmallF_pass_inv3V2D S I hlen hL0 hd0e hr hx2 hPR)
      (expStep_frameMapT1D S I.cons I.good I.rank hlen hL0 hd0e hr hx2)
  exact qr_final4SGD2 hlen hL0 hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
    hr hx2 hq I.cons I.good I.rank I.kd I.td hdrop hUAR (Or.inr hr2)
    I.tp1w (I.tplowAt hlen hr) I.auwl I.auw0 (I.adwAt hlen hr) I.tp1 I.trigs I.tplon I.adn I.rootS I.rootP
    _ hbase hstep

end Ytosk
