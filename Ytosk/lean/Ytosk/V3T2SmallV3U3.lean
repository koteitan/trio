/-
**hN with the level-`u` copy condition `VDomU` (2026-11-06, generated from V3T2SmallV3U2 by a text copy).**

`CopyVDomK` (`VDomF` at every level `≤ f(a)`) is false on graftE (tmp/claude/measure_hn86.py, 9 frames).
`hN_of4` = `hN_of3` with `T2VRAK VDomU` (the components of `V′` at the frame's level `u ≤ V`, with the shifted
state as an alternative, V3T2VRAK3) in place of `T2CopyK CopyVDomK`.
-/
import Ytosk.V3T2SmallV3U2
import Ytosk.V3T2VRAK3

namespace Ytosk.V3Main
open T Classical WfExQ1 WfT2X WfAbsW G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- `t2_small_of_framesV3U4` with `KVRA3` (the level-`u` form `VDomU` in place of `CopyVDomK`). -/
theorem t2_small_of_framesV3U4 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtx3 M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hB : T2BelowAtV3U M ρ)
    (hVS : T2SeedFrames QVSF M) (hFC : T2SeedFrames QFC M)
    (hFD : T2CopyK FDshAt M)
    (hSeed : T2VRASeed M) (hPre : T2VRAPre M ρ) (hCopy : T2VRACopyEsc2 M)
    (hVD : T2VRAK (fun V V' a Lv _ u => VDomU V V' a Lv u) M) (hAG : T2VRAK KAG2 M) :
    ∀ n, 2 ≤ n → ∀ σ rkN, Cons (expand M n) σ → Rk (expand M n) rkN →
    Good3 (expand M n) σ → PH3cG (expand M n) σ →
      VSmallF (expand M n) σ ∧ FrameClosed (expand M n) σ ∧ VSmallRAll (expand M n) σ := by
  have hl : 2 ≤ M.length := by
    obtain ⟨r, hr⟩ := parLast_of C.S.e00 C.S.r01 C.S.r12 hz
    rw [h2] at hr
    have := par_lt M 2 _ r hr
    omega
  have I := coreW C.S C.I
  have D := C.drop hl
  have I1 := C.pre (M.length - 1) (by omega) (by omega)
  have hag : ∀ τ, Cons (M.take (M.length - 1)) τ →
      Agree (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) τ :=
    fun τ hτ => agree_of_cons I1.cons hτ I1.rank
  have hVSN := vsmallF_expand_t2VV3U hB C.std C.ne I D hz h2
    (fun τ hτ => ⟨good3_congr I1.good (hag τ hτ), vsmallF_of_clField hτ (good3_congr I1.good (hag τ hτ))
      (clField_congr (Q := QVSF) (clField_of_vsmallF I1.cons I1.good I1.vs) (hag τ hτ))⟩) hVS
  have hFCN := frameClosed_expand_t2KV3U hB C.std C.ne I D hz h2
    (fun τ hτ => clField_congr (Q := QFC) I1.fc (hag τ hτ)) hFC hFD
  have hVRA := vsmallRAll_expand_t2V3U2 qVRAshK_KVRA3 hB C.std C.ne I D hz h2 C.I.vra
    (fun τ hτ => vsmallRAll_congr (hag τ hτ) I1.vra) hSeed hPre hCopy
    (t2VRAK_KVRA3_of hVD hAG)
  intro n hn σ _ hCN _ hGN _
  exact ⟨hVSN n (by omega) σ hCN hGN, hFCN n (by omega) σ hCN, hVRA n (by omega) σ hCN⟩

namespace SeedPF
open Classical G

/-- **The input hN** with `KVRA3` (`VDomU`, `KAG2`) and `T2VRACopyEsc2`. -/
theorem hN_of4 (hBXU : T2AtV3 T2BelowAtV3U) (hVF : T2AtV3 (fun M ρ => SeedVFResV3 M ρ))
    (hFD : T2AtV3 (fun M _ => T2CopyK FDshAt M)) (hSeed : T2AtV3 (fun M _ => T2VRASeed M))
    (hPre : T2AtV3 (fun M ρ => T2VRAPre M ρ)) (hCopy : T2AtV3 (fun M _ => T2VRACopyEsc2 M))
    (hVD : T2AtV3 (fun M _ => T2VRAK (fun V V' a Lv _ u => VDomU V V' a Lv u) M)) (hAG : T2AtV3 (fun M _ => T2VRAK KAG2 M)) :
    T2SmallV3 := by
  intro M ρ rk C hz h2
  have hS := seed_frames_VFV3 C hz h2 (hVF M ρ rk C hz h2)
  have hVS : T2SeedFrames QVSF M :=
    fun r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl => (hS r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl).1
  have hFC : T2SeedFrames QFC M :=
    fun r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl => (hS r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl).2.2
  exact t2_small_of_framesV3U4 C hz h2 (hBXU M ρ rk C hz h2) hVS hFC (hFD M ρ rk C hz h2)
    (hSeed M ρ rk C hz h2) (hPre M ρ rk C hz h2) (hCopy M ρ rk C hz h2) (hVD M ρ rk C hz h2) (hAG M ρ rk C hz h2)

#print axioms hN_of4

end SeedPF

end Ytosk.V3Main
