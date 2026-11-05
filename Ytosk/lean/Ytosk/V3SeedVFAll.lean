/-
**V3SeedVFAll (2026-11-05): the VSmallF/FrameClosed seed frames and the input hN on the V3 context.**

The per-configuration producers of V3SeedVF (generated from V3T2SeedFr/V3T2SeedFr2 by tmp/claude/make_seedvf.py)
are joined as in `seed_frames_PFV3` (V3SeedPFAll): source data from `StepCtx3`, prefix data from `C.pre`,
the C configuration split by `upg M (x − 1)` (C1: the residual `CRel` and `T2SeedCDom`; C2: the seed frames).
`hN_of` derives the entry input `hN : T2SmallV3` from `hBXU` and the remaining named copy/VRA residuals.
-/
import Ytosk.V3SeedVF
import Ytosk.V3SeedPFAll
import Ytosk.V3T2LocalV3U

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The VSmallF/FrameClosed seed property. -/
abbrev QVF (a : T) (Lv : List T) (cv : T) : Prop := QVSF a Lv cv ∧ QFCo a Lv cv

theorem seedFr_and {Q₁ Q₂ : T → List T → T → Prop} {M : Mat} {r L i : Nat}
    (h₁ : SeedFr Q₁ M r L i) (h₂ : SeedFr Q₂ M r L i) : SeedFr (fun a Lv cv => Q₁ a Lv cv ∧ Q₂ a Lv cv) M r L i :=
  fun n hn hlow σ hσ hG Lc c R hcl =>
    ⟨h₁ n hn hlow σ hσ hG Lc c R hcl, h₂ n hn hlow σ hσ hG Lc c R hcl⟩

/-- **The residuals of the VSmallF/FrameClosed seed frames**: those of the PH/FC3 seed frames, the two domination
fields, and the C2 seed frames. -/
structure SeedVFResV3 (M : Mat) (ρ : Valn) : Prop where
  pf : SeedPFResV3 M ρ
  qnDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDom M ρ r L q Lc
  cDom : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = none → T2SeedCDom M ρ r L q
  C2 : ∀ r L q k, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
    (¬ ∃ Lc, CL M r = Lc ++ [q]) → upg M (r + L - 1) = some k → ∀ i, (i = r ∨ i = q) → SeedFr QVF M r L i

/-- **VSmallF and FrameClosed at the seed frames of every `M[n]`** (`t = 2`) on the V3 context. -/
theorem seed_frames_VFV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (Ctx : StepCtx3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hRes : SeedVFResV3 M ρ) : T2SeedFrames QVF M := by
  have hM := Ctx.std
  have hS := Ctx.ne
  have I : Inv3W M ρ rk := coreW Ctx.S Ctx.I
  refine t2_seed_frames_of (Q := QVF) hM hS I ?_ ?_ ?_ ?_
  · intro r L hlen hr hq hXu Lc hLc
    have J := Ctx.pre (r + L) (by have := par_lt M 2 _ r hr; omega) (by omega)
    have h := seed_frames_qr3V3 hM hS I Ctx hz h2 hlen hr hq hXu hLc (hRes.pf.qr r L hlen hr hq hXu Lc hLc)
      J.cons ⟨rk, J.rank⟩
    exact seedFr_and h.1 h.2.2
  · intro r L hlen hr hq hux
    have J := Ctx.pre (r + L) (by have := par_lt M 2 _ r hr; omega) (by omega)
    have hFix := t2SeedSVFix_holdsV3 hM hS I Ctx hlen hr hq hux
    have h := seed_frames_sv3V3 hM hS I Ctx hz h2 hlen hr hq hux (hRes.pf.sv r L hlen hr hq hux) hFix
      J.cons J.rank J.vs J.fo J.fc
    exact seedFr_and h.1 h.2.2
  · intro r L q hlen hr hq hqr Lc hLc i hi
    have J := Ctx.pre (r + L) (by have := par_lt M 2 _ r hr; omega) (by omega)
    have h := seed_frames_qn3V3 hM hS I Ctx hz h2 hlen hr hq hqr hLc (hRes.pf.qn r L q hlen hr hq hqr Lc hLc)
      (hRes.qnDom r L q hlen hr hq hqr Lc hLc) J.cons ⟨rk, J.rank⟩ i hi
    exact seedFr_and h.1 h.2.2
  · intro r L q hlen hr hq hqr hncl i hi
    cases hu : upg M (r + L - 1) with
    | none =>
      have J := Ctx.pre (r + L) (by have := par_lt M 2 _ r hr; omega) (by omega)
      obtain ⟨hCR, hBig⟩ := hRes.pf.C1 r L q hlen hr hq hqr hncl hu
      have hFix := t2SeedCFix_ofV3 hM hS I Ctx hlen hr hq hqr hncl hCR hBig
      have h := seed_frames_C3V3 hM hS I Ctx hz h2 hlen hr hq hqr hncl hCR hFix
        (hRes.cDom r L q hlen hr hq hqr hncl hu) J.cons J.rank J.vs J.fo J.fc i hi
      exact seedFr_and h.1 h.2.2
    | some k => exact hRes.C2 r L q k hlen hr hq hqr hncl hu i hi

/-- **The input hN** from `hBXU`, the VSmallF/FrameClosed seed residuals and the copy/VRA residuals. -/
theorem hN_of (hBXU : T2AtV3 T2BelowAtV3U) (hVF : T2AtV3 (fun M ρ => SeedVFResV3 M ρ))
    (hFD : T2AtV3 (fun M _ => T2CopyK FDshAt M)) (hSeed : T2AtV3 (fun M _ => T2VRASeed M))
    (hPre : T2AtV3 (fun M ρ => T2VRAPre M ρ)) (hCopy : T2AtV3 (fun M _ => T2VRACopyEsc M))
    (hVD : T2AtV3 (fun M _ => T2CopyK CopyVDomK M)) (hAG : T2AtV3 (fun M _ => T2VRAK KAG M)) :
    T2SmallV3 := by
  intro M ρ rk C hz h2
  have hS := seed_frames_VFV3 C hz h2 (hVF M ρ rk C hz h2)
  have hVS : T2SeedFrames QVSF M :=
    fun r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl => (hS r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl).1
  have hFC : T2SeedFrames QFC M :=
    fun r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl => (hS r L hlen hr n hn hlow σ hσ hG i hi Lc c R hcl).2.2
  exact t2_small_of_framesV3U C hz h2 (hBXU M ρ rk C hz h2) hVS hFC (hFD M ρ rk C hz h2)
    (hSeed M ρ rk C hz h2) (hPre M ρ rk C hz h2) (hCopy M ρ rk C hz h2) (hVD M ρ rk C hz h2) (hAG M ρ rk C hz h2)

end Ytosk.V3Main.SeedPF
