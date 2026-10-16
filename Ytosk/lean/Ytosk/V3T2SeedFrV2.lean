/-
**種の列の枠の残り T2SeedVSFV2・T2SeedFCV2・T2FOSeedV2 を埋める（2026-10-17、t2）。**

4 つの場合（qr・sv・qn・C、`G.t2_seed_frames_of`）の枠の補題（V3T2SeedFr・V3T2SeedFr2）を組み立てる。
使う残りは既存の種の残り `T2SeedPResV2`（closure の PH3cG・FC3 と同じ束）と、添字 s′ の成分の残り
`T2SeedDomV2`（qn の `T2SeedQNDom`・C の `T2SeedCDom`）だけ。M.take x の VSmallF・FrameOT・FrameClosed は
StepCtxV2 の接頭辞から（`take_fields_ctx`）。
-/
import Ytosk.V3T2SeedFr2
import Ytosk.V3T2VSFC

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **t2-seed-dom**: the components of `s′ = v_N(q)` at the seed frames (qn and C). -/
def T2SeedDomV2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    (∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDom M ρ r L q Lc) ∧
    (∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → G.T2SeedCDom M ρ r L q)

/-- `FrameOT` of `M.take x` for every consistent valuation, from the context. -/
theorem take_fo_ctx {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (C : StepCtxV2 M ρ rk)
    (hl : 2 ≤ M.length) {τ : Valn} (hτ : Cons (M.take (M.length - 1)) τ) :
    FrameOT (M.take (M.length - 1)) τ := by
  obtain ⟨I1, _⟩ := C.pre (M.length - 1) (by omega) (by omega)
  exact clField_congr (frameOT_iff.mp I1.fo) (agree_of_cons I1.cons hτ I1.rank)

open Classical in
/-- **The seed frames of every `M[n]`** for `QVSF`, `QFO` and `QFCo`. -/
theorem t2SeedFrames3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hRes : G.T2SeedPRes M ρ)
    (hQND : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      ∀ Lc, CL M r = Lc ++ [q] → T2SeedQNDom M ρ r L q Lc)
    (hCD : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → G.T2SeedCDom M ρ r L q)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → VSmallF (M.take (M.length - 1)) τ ∧
      FrameOT (M.take (M.length - 1)) τ ∧ FrameClosed (M.take (M.length - 1)) τ) :
    T2SeedFrames QVSF M ∧ T2SeedFrames QFO M ∧ T2SeedFrames QFCo M := by
  have hlen1 : 1 ≤ M.length := by
    rcases hM0 : M with _ | _
    · rw [hM0] at hz; exact absurd rfl hz
    · simp
  have hRk1 : Rk (M.take (M.length - 1)) rk :=
    rk_take (by omega) I.rank (counted_take_last (M := M) hlen1 I.r0p I.z2 I.sd I.z1 I.uat)
  have hC1 := cons_of_rk hRk1
  set τ0 := rhsIt (M.take (M.length - 1)) (rkBound (M.take (M.length - 1)) rk) with hτ0
  have hT0 := hT τ0 hC1
  have hx : ∀ r L, r + L + 1 = M.length → M.length - 1 = r + L := fun r L h => by omega
  -- the four cases, all three properties at once
  have hQR : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
      (∀ i, upg M i ≠ some (r + L)) → ∀ Lc, CL M r = Lc ++ [r + L] →
      G.SeedFr QVSF M r L r ∧ G.SeedFr QFO M r L r ∧ G.SeedFr QFCo M r L r := by
    intro r L hlen hr hq hXu Lc hLc
    have hC1' := hC1; have hRk1' := hRk1
    rw [hx r L hlen] at hC1' hRk1'
    exact seed_frames_qr3 hM hS I R hz h2 hlen hr hq hXu hLc (hRes.qr r L hlen hr hq hXu Lc hLc) hC1' ⟨rk, hRk1'⟩
  have hSV : ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some r →
      upg M (r + L - 1) = some (r + L) →
      G.SeedFr QVSF M r L r ∧ G.SeedFr QFO M r L r ∧ G.SeedFr QFCo M r L r := by
    intro r L hlen hr hq hux
    have hC1' := hC1; have hRk1' := hRk1; have hT0' := hT0
    rw [hx r L hlen] at hC1' hRk1' hT0'
    exact G.seed_frames_sv3 hM hS I R hz h2 hlen hr hq hux (hRes.sv r L hlen hr hq hux)
      (G.t2SeedSVFix_holds hM hS I R hlen hr hq hux) hC1' hRk1' hT0'.1 hT0'.2.1 hT0'.2.2
  have hQN : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      ∀ Lc, CL M r = Lc ++ [q] → ∀ i, (i = r ∨ i = q) →
      G.SeedFr QVSF M r L i ∧ G.SeedFr QFO M r L i ∧ G.SeedFr QFCo M r L i := by
    intro r L q hlen hr hq hqr Lc hLc i hi
    have hC1' := hC1; have hRk1' := hRk1
    rw [hx r L hlen] at hC1' hRk1'
    exact seed_frames_qn3 hM hS I R hz h2 hlen hr hq hqr hLc (hRes.qn r L q hlen hr hq hqr Lc hLc)
      (hQND r L q hlen hr hq hqr Lc hLc) hC1' ⟨rk, hRk1'⟩ i hi
  have hC : ∀ r L q, r + L + 1 = M.length → par M 2 (r + L) = some r → par M 0 (r + L) = some q → q ≠ r →
      (¬ ∃ Lc, CL M r = Lc ++ [q]) → ∀ i, (i = r ∨ i = q) →
      G.SeedFr QVSF M r L i ∧ G.SeedFr QFO M r L i ∧ G.SeedFr QFCo M r L i := by
    intro r L q hlen hr hq hqr hncl i hi
    have hC1' := hC1; have hRk1' := hRk1; have hT0' := hT0
    rw [hx r L hlen] at hC1' hRk1' hT0'
    obtain ⟨hCR, hBig⟩ := hRes.C r L q hlen hr hq hqr hncl
    exact G.seed_frames_C3 hM hS I R hz h2 hlen hr hq hqr hncl hCR
      (G.t2SeedCFix_of hM hS I R hlen hr hq hqr hncl hCR hBig) (hCD r L q hlen hr hq hqr hncl)
      hC1' hRk1' hT0'.1 hT0'.2.1 hT0'.2.2 i hi
  refine ⟨G.t2_seed_frames_of hM hS I (fun r L h1 h2 h3 h4 Lc h5 => (hQR r L h1 h2 h3 h4 Lc h5).1)
      (fun r L h1 h2 h3 h4 => (hSV r L h1 h2 h3 h4).1)
      (fun r L q h1 h2 h3 h4 Lc h5 i hi => (hQN r L q h1 h2 h3 h4 Lc h5 i hi).1)
      (fun r L q h1 h2 h3 h4 h5 i hi => (hC r L q h1 h2 h3 h4 h5 i hi).1),
    G.t2_seed_frames_of hM hS I (fun r L h1 h2 h3 h4 Lc h5 => (hQR r L h1 h2 h3 h4 Lc h5).2.1)
      (fun r L h1 h2 h3 h4 => (hSV r L h1 h2 h3 h4).2.1)
      (fun r L q h1 h2 h3 h4 Lc h5 i hi => (hQN r L q h1 h2 h3 h4 Lc h5 i hi).2.1)
      (fun r L q h1 h2 h3 h4 h5 i hi => (hC r L q h1 h2 h3 h4 h5 i hi).2.1),
    G.t2_seed_frames_of hM hS I (fun r L h1 h2 h3 h4 Lc h5 => (hQR r L h1 h2 h3 h4 Lc h5).2.2)
      (fun r L h1 h2 h3 h4 => (hSV r L h1 h2 h3 h4).2.2)
      (fun r L q h1 h2 h3 h4 Lc h5 i hi => (hQN r L q h1 h2 h3 h4 Lc h5 i hi).2.2)
      (fun r L q h1 h2 h3 h4 h5 i hi => (hC r L q h1 h2 h3 h4 h5 i hi).2.2)⟩

/-- **The seed-frame residuals of the top level** from `T2SeedPResV2` and `T2SeedDomV2`. -/
theorem t2SeedFrV2_of (hPR : T2SeedPResV2) (hD : T2SeedDomV2) :
    T2SeedVSFV2 ∧ T2SeedFCV2 ∧ T2FOSeedV2 := by
  have main : ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 →
      T2SeedFrames QVSF M ∧ T2SeedFrames QFO M ∧ T2SeedFrames QFCo M := by
    intro M ρ rk C hz h2
    obtain ⟨hX, _⟩ := sInvXJ_std C.std C.ne
    have hl2 : 2 ≤ M.length := by
      obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
      rw [h2] at hr
      have := par_lt M 2 _ r hr; omega
    obtain ⟨hQND, hCD⟩ := hD M ρ rk C hz h2
    exact t2SeedFrames3 C.std C.ne (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2 (hPR M ρ rk C hz h2) hQND hCD
      (fun τ hτ => ⟨(take_fields_ctx C hl2 hτ).2.1, take_fo_ctx C hl2 hτ, (take_fields_ctx C hl2 hτ).2.2⟩)
  refine ⟨fun M ρ rk C hz h2 => (main M ρ rk C hz h2).1, fun M ρ rk C hz h2 => ?_,
    fun M ρ rk C hz h2 => (main M ρ rk C hz h2).2.1⟩
  intro r L hlen hr n hn hGlow σ hCN hGN i hi Lc c R hCL
  exact ((main M ρ rk C hz h2).2.2 r L hlen hr n hn hGlow σ hCN hGN i hi Lc c R hCL).2

/-- **T2VSFCV2 with the seed frames filled**: from `T2BelowXRes`, `FDsh`, `T2SeedPResV2` and `T2SeedDomV2`. -/
theorem t2VSFCV2_of2 (hB : T2BelowXRes) (hFD : FDsh) (hPR : T2SeedPResV2) (hD : T2SeedDomV2) : T2VSFCV2 :=
  t2VSFCV2_of hB hFD (t2SeedFrV2_of hPR hD).1 (t2SeedFrV2_of hPR hD).2.1

/-- **T2FOSeedV2** from `T2SeedPResV2` and `T2SeedDomV2`. -/
theorem t2FOSeedV2_of (hPR : T2SeedPResV2) (hD : T2SeedDomV2) : T2FOSeedV2 :=
  (t2SeedFrV2_of hPR hD).2.2

end Ytosk
