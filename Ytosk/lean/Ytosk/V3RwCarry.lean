/-
**RwClosed を最上位の帰納法で運ぶ: 展開での保存（2026-10-17、lead）。**

最上位の帰納法（`hInvV2_all`）は `Inv3V2 ∧ RwClosed` を運び、文脈 `StepCtxV2` は `rw : RwClosed M ρ` を持つ。
展開 M[n] で RwClosed が出ること（`TRwOut t`）を、型ごとの保存の補題から示す。
- t = 2: `rwClosed_expand_t2SV`（V3RwClCopy）。残りは T2X1Cl・T2CopyK CopyLowK・T2VAncStep（どれも 11 集合で例外 0）。
-/
import Ytosk.V3RwClCopy
import Ytosk.V3RwClDrop
import Ytosk.V3ExpT2V2

namespace Ytosk

open T

/-- **`RwClosed` moves between agreeing valuations.** -/
theorem rwClosed_of_agree {M : Mat} {σ τ : Valn} (h : Agree M σ τ) (hσ : RwClosed M σ) : RwClosed M τ := by
  intro i hi Lc c R hCL s y ho ht hlt hnp
  have hcM : c < M.length := (mem_children (cl_mem_children (show c ∈ CL M i by rw [hCL]; simp))).2
  have hL : Lc.map τ.o = Lc.map σ.o := by
    apply List.map_congr_left
    intro d hd
    have hdM : d < M.length := (mem_children (cl_mem_children (show d ∈ CL M i by rw [hCL]; simp [hd]))).2
    exact (h d hdM).1.symm
  have hv : τ.v i = σ.v i := (h i hi).2.symm
  have ho' : σ.o c = psi s y z := by rw [(h c hcM).1]; exact ho
  rw [hL, hv] at ht hlt hnp ⊢
  exact hσ i hi Lc c R hCL s y ho' ht hlt hnp

/-- **`RwClosed` of the last drop for every valuation**, in the step context. -/
theorem rw_take_ctx {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtxV2 M ρ rk) (hl : 2 ≤ M.length)
    {τ : Valn} (hτ : Cons (M.take (M.length - 1)) τ) : RwClosed (M.take (M.length - 1)) τ := by
  have S := C.S
  have I := C.I
  have hx : M.length - 1 + 1 = M.length := by omega
  have hcnt := counted_take_last (M := M) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (M.length - 1)) rk := rk_take (by omega) I.rank hcnt
  have hC1 := cons_of_rk hRk1
  have hdr := C.R.drop
  have hdrop := drop_all hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.vs hdr.vst
    I.fc I.fo hdr.argT
    (bump_drop hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 I.kd I.td hdr.ab hdr.ws) hdr.ua
  have h1 := rwClosed_take hx S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good hC1 hRk1 hdrop C.rw
  exact rwClosed_of_agree (agree_of_cons hC1 hτ hRk1) h1

/-- **`TRwOut 2`** from `rwClosed_expand_t2SV`: the residuals are `T2X1Cl`, `T2CopyK CopyLowK` and
`T2VAncStep` of the matrices of the induction (the seed residual is t2's `T2SeedPResV2`). -/
theorem tRwOut2_of (hB : T2BelowXResV2) (hP : T2SeedPResV2)
    (hX1 : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → G.T2X1Cl M ρ)
    (hLow : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2CopyK CopyLowK M)
    (hVS : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2VAncStep M) : TRwOut 2 := by
  intro M ρ rk C hz hs n hn ρN rkN IN
  have hl : 2 ≤ M.length := by
    have := (sInvXJ_std C.std C.ne).1
    obtain ⟨r, hr⟩ := parLast_of this.e00 this.r01 this.r12 hz
    rw [hs] at hr
    have := par_lt M 2 _ r hr; omega
  exact rwClosed_expand_t2SV (hB M ρ rk C) C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz hs C.rw
    (fun τ hτ => rw_take_ctx C hl hτ) (hX1 M ρ rk C hz hs) (hP M ρ rk C hz hs) (hLow M ρ rk C hz hs)
    (hVS M ρ rk C hz hs) n (by omega) ρN IN.cons

end Ytosk
