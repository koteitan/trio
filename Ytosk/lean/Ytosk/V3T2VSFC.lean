/-
**最上位の t = 2 の残り `T2VSFCV2`（M[n] の VSmallF・FrameClosed）を埋める（2026-10-16、t2）。**

`vsmallF_expand_t2V`（V3T2VSF）と `frameClosed_expand_t2`（V3T2FC）から。M.take x の欄は文脈 StepCtxV2 の
接頭辞の Inv3V2 から、評価の一致（`agree_of_cons`）で任意の Cons の評価へ移す。
残りは名前つきの `FDsh`（FrameDom の σ 不変性、項だけの主張）と、種の列の枠 `T2SeedVSFV2`・`T2SeedFCV2`。
-/
import Ytosk.V3T2FC
import Ytosk.V3ExpT2V2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **t2-vs (seed)**: the `VSmallF` frames at the seed columns of `M[n]`. -/
def T2SeedVSFV2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedFrames QVSF M

/-- **t2-fc (seed)**: the `FrameClosed` frames at the seed columns of `M[n]`. -/
def T2SeedFCV2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedFrames QFC M

/-- The fields of `M.take x` for every consistent valuation, from the context. -/
theorem take_fields_ctx {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtxV2 M ρ rk)
    (hl : 2 ≤ M.length) {τ : Valn} (hτ : Cons (M.take (M.length - 1)) τ) :
    Good3 (M.take (M.length - 1)) τ ∧ VSmallF (M.take (M.length - 1)) τ ∧
      FrameClosed (M.take (M.length - 1)) τ := by
  obtain ⟨I1, _⟩ := C.pre (M.length - 1) (by omega) (by omega)
  have hA := agree_of_cons I1.cons hτ I1.rank
  have hG := good3_congr I1.good hA
  refine ⟨hG, ?_, clField_congr (frameClosed_iff.mp I1.fc) hA⟩
  exact vsmallF_of_clField hτ hG (clField_congr (clField_of_vsmallF I1.cons I1.good I1.vs) hA)

/-- **T2VSFCV2 from the named residuals.** -/
theorem t2VSFCV2_of (hB : T2BelowXResV2) (hFD : FDsh) (hSV : T2SeedVSFV2) (hSF : T2SeedFCV2) : T2VSFCV2 := by
  intro M ρ rk C hz h2 n hn σ rkN hCN _ hGN _
  obtain ⟨hX, _⟩ := sInvXJ_std C.std C.ne
  have hl2 : 2 ≤ M.length := by
    obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
    rw [h2] at hr
    have := par_lt M 2 _ r hr; omega
  have IW := Inv3W.ofV2 C.S C.I
  have RW : Res3W M ρ rk := ⟨C.R.drop⟩
  refine ⟨vsmallF_expand_t2V (hB M ρ rk C) C.std C.ne IW RW hz h2
      (fun τ hτ => ⟨(take_fields_ctx C hl2 hτ).1, (take_fields_ctx C hl2 hτ).2.1⟩)
      (hSV M ρ rk C hz h2) n (by omega) σ hCN hGN,
    frameClosed_expand_t2 hFD (hB M ρ rk C) C.std C.ne IW RW hz h2 (fun τ hτ => (take_fields_ctx C hl2 hτ).2.2)
      (hSF M ρ rk C hz h2) n (by omega) σ hCN⟩

end Ytosk
