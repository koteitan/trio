/-
**The input hN with the weaker copy-frame condition `KAG2` (2026-11-06).**

`KAG` (`T2VRAK KAG`, a residual of `hN_of`) is false on the standard forms of the graft sets (2643 failures,
tmp/claude/measure_t2vrak86.py); `KAG2` (V3T2VRAK2) adds the alternative "below a moving component of `a − V`" and
has no failure there (tmp/claude/measure_kag2.py).  `t2_small_of_framesV3U2` and `hN_of2` are `t2_small_of_framesV3U`
and `hN_of` with `KAG2` in place of `KAG`.
-/
import Ytosk.V3SeedVFAll
import Ytosk.V3T2VRAK2

namespace Ytosk.V3Main
open T WfExQ1 WfExQ2

/-- `t2_small_of_framesV3U` with the copy-frame condition `KAG2`. -/
theorem t2_small_of_framesV3U2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (C : StepCtx3 M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hB : T2BelowAtV3U M ρ)
    (hVS : T2SeedFrames QVSF M) (hFC : T2SeedFrames QFC M)
    (hFD : T2CopyK FDshAt M)
    (hSeed : T2VRASeed M) (hPre : T2VRAPre M ρ) (hCopy : T2VRACopyEsc M)
    (hVD : T2CopyK CopyVDomK M) (hAG : T2VRAK KAG2 M) :
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
  have hVRA := vsmallRAll_expand_t2V3U qVRAshK_KVRA2 hB C.std C.ne I D hz h2 C.I.vra
    (fun τ hτ => vsmallRAll_congr (hag τ hτ) I1.vra) hSeed hPre hCopy
    (t2VRAK_KVRA2_of hVD hAG)
  intro n hn σ _ hCN _ hGN _
  exact ⟨hVSN n (by omega) σ hCN hGN, hFCN n (by omega) σ hCN, hVRA n (by omega) σ hCN⟩

namespace SeedPF
open Classical G

/-- **The input hN** with `KAG2`: from `hBXU`, the VSmallF/FrameClosed seed residuals and the copy/VRA residuals. -/
theorem hN_of2 (hBXU : T2AtV3 T2BelowAtV3U) (hVF : T2AtV3 (fun M ρ => SeedVFResV3 M ρ))
    (hFD : T2AtV3 (fun M _ => T2CopyK FDshAt M)) (hSeed : T2AtV3 (fun M _ => T2VRASeed M))
    (hPre : T2AtV3 (fun M ρ => T2VRAPre M ρ)) (hCopy : T2AtV3 (fun M _ => T2VRACopyEsc M))
    (hVD : T2AtV3 (fun M _ => T2CopyK CopyVDomK M)) (hAG : T2AtV3 (fun M _ => T2VRAK KAG2 M)) :
    T2SmallV3 := by
  intro M ρ rk C hz h2
  have hS := seed_frames_VFV3 C hz h2 (hVF M ρ rk C hz h2)
  have hVS : T2SeedFrames QVSF M :=
    fun r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl => (hS r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl).1
  have hFC : T2SeedFrames QFC M :=
    fun r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl => (hS r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl).2.2
  exact t2_small_of_framesV3U2 C hz h2 (hBXU M ρ rk C hz h2) hVS hFC (hFD M ρ rk C hz h2)
    (hSeed M ρ rk C hz h2) (hPre M ρ rk C hz h2) (hCopy M ρ rk C hz h2) (hVD M ρ rk C hz h2) (hAG M ρ rk C hz h2)

#print axioms hN_of2

end SeedPF

end Ytosk.V3Main
