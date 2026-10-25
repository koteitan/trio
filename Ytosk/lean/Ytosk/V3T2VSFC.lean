/-
**最上位の t = 2 の残り `T2VSFCV2`（M[n] の VSmallF・FrameClosed）を埋める（2026-10-16、t2）。**

`vsmallF_expand_t2V`（V3T2VSF）と `frameClosed_expand_t2`（V3T2FC）から。M.take x の欄は文脈 StepCtxV2 の
接頭辞の Inv3V2 から、評価の一致（`agree_of_cons`）で任意の Cons の評価へ移す。
残りは写しの枠での FrameDom の σ 不変性 `T2FDCopyRes`（2026-10-19。項だけの `FDsh` は偽、`FDCut.not_FDsh`）と、種の列の枠 `T2SeedVSFV2`・`T2SeedFCV2`。
-/
import Ytosk.V3T2FC
import Ytosk.V3ExpT2V2
import Ytosk.V3RwClCopy

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **`FDsh` at one copy frame** `(a, Lv, cv)` (2026-10-19). The pure `FDsh` is false (`FDCut.not_FDsh`), so the
`σ`-invariance of `FrameDom` is asked only at the real copy frames of the expansion (`T2FDCopyRes`). -/
def FDshAt (V V' a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y, cv = psi s y z → V < s →
    lt (spArg a z (sumN Lv)) y = true → lt (psi a z z) (psi s y z) = true →
    FrameDom a (spArg a z (sumN Lv)) s (H s y) →
    FrameDom (shf V V' a) (sh V V' (spArg a z (sumN Lv))) (shf V V' s) (H (shf V V' s) (sh V V' y))

/-- **`QFCo` moves with `σ`** at one copy frame, given `FDshAt` at that frame (the frame-local form of `FDsh`). -/
theorem qFCo_shK (V V' a : T) (Lv : List T) (cv : T) (hV : isOT V = true)
    (hV' : isOT V' = true) (hVV : V < V') (ha : isOT a = true) (hVa : V ≤ a)
    (hs : ∀ t ∈ Lv ++ [cv], Single t) (hp : (Lv ++ [cv]).Pairwise (fun a b => b ≤ a))
    (hlev : V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t) (hK : FDshAt V V' a Lv cv) (hQ : QFCo a Lv cv) :
    QFCo (shf V V' a) (Lv.map (sh V V')) (sh V V' cv) := by
  have hLs : ∀ t ∈ Lv, Single t := fun t ht => hs t (List.mem_append_left _ ht)
  have hLp : Lv.Pairwise (fun a b => b ≤ a) := (List.pairwise_append.mp hp).1
  obtain ⟨hSot, hSsum⟩ := sumN_dec Lv hLs hLp
  have hlev' : V < a ∨ ∀ q ∈ summands (sumN Lv), lev q ≠ V := by
    rcases hlev with h | h
    · exact Or.inl h
    · right; rw [hSsum]; intro q hq; exact ne_of_gt (h q (List.mem_append_left _ hq))
  have hBot : isOT (spArg a z (sumN Lv)) = true := isOT_spArg a (sumN Lv) z rfl hSot
  have hB : spArg (shf V V' a) z (sumN (Lv.map (sh V V'))) = sh V V' (spArg a z (sumN Lv)) := by
    rw [← sh_sumN hV hV' hVV (fun t ht => (hLs t ht).1)]
    have hsp := sh_spArg hV hV' hVV ha hVa (b := z) rfl hSot hlev'
    rw [sh_z] at hsp
    exact hsp
  obtain ⟨hcvot, s, y, hcv⟩ := hs cv (by simp)
  subst hcv
  refine ⟨isOT_sh hV hV' hVV hcvot, ?_⟩
  intro s' y' hcv' ht'
  rw [hB] at ht' ⊢
  have hVV' : V ≤ V' := le_of_lt hVV
  have hsot : isOT s = true := isOT_sub hcvot
  have hyot : isOT y = true := isOT_arg hcvot
  by_cases hVs : V < s
  · rw [sh_psi_gt hVs, sh_z] at hcv'
    simp only [psi.injEq] at hcv'
    obtain ⟨rfl, rfl, -⟩ := hcv'
    -- the frame of `P` rewrites
    have h1 : lt (spArg a z (sumN Lv)) y = true :=
      (sh_lt_iff hV hV' hVV' hBot hyot).mp ht'.1
    have hfa : shf V V' a ≤ shf V V' s := le_of_trig ht'.2
    have has : a ≤ s := by
      rcases (le_iff _ _).mp hfa with h | h
      · exact le_of_lt ((shf_lt_iff hV hV' hVV' ha hsot hVa (le_of_lt hVs)).mp h)
      · rcases lt_trichotomy' a s with h' | h' | h'
        · exact le_of_lt h'
        · rw [h']
        · exact absurd h (ne_of_gt (shf_lt_shf hV hV' hVV' hsot ha (le_of_lt hVs) h'))
    have hyz : y ≠ z := fun h => by rw [h] at h1; exact T.not_lt_z _ h1
    have h2 : lt (psi a z z) (psi s y z) = true := by
      show psi a z z < psi s y z
      rcases (le_iff _ _).mp has with h | h
      · exact psi_lt_psi_z_iff.mpr (Or.inl h)
      · subst h
        exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_ne (z_le _) (Ne.symm hyz)⟩)
    exact hK s y rfl hVs h1 h2 (hQ.2 s y rfl ⟨h1, h2⟩)
  · rw [sh_psi_le hVs, sh_z] at hcv'
    simp only [psi.injEq] at hcv'
    obtain ⟨rfl, rfl, -⟩ := hcv'
    exfalso
    have hlt : s < shf V V' a :=
      lt_of_le_of_lt (le_of_not_gt hVs) (lt_of_lt_of_le hVV (le_shf hV hV' hVV' ha hVa))
    have := le_of_trig ht'.2
    exact lt_irrefl' _ (lt_of_lt_of_le hlt this)

/-- **FrameClosed of every `M[n]`** (`t = 2`, `n ≥ 1`) with `FDshAt` at the copy frames (`T2CopyK FDshAt M`) in
place of the false `FDsh`. -/
theorem frameClosed_expand_t2K {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk) (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → FrameClosed (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QFC M) (hK : T2CopyK FDshAt M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → FrameClosed (expand M n) σ := by
  have hl : 1 ≤ M.length := by
    rcases Nat.eq_zero_or_pos M.length with h | h
    · exfalso; apply hz; rw [h]
      have : M = [] := List.eq_nil_of_length_eq_zero h
      subst this; rfl
    · exact h
  have hSeed' : T2SeedFrames QFCo M := by
    intro r L hlen hr n hn hGm σ hCN hGN i hsc Lc c R hCL
    have hcN := (mem_children (cl_mem_children (show c ∈ CL _ i by rw [hCL]; simp))).2
    exact ⟨hGN.ot_o c hcN, hSeed r L hlen hr n hn hGm σ hCN hGN i hsc Lc c R hCL⟩
  have key := clField_expand_t2SK (K := FDshAt) (fun V V' a Lv cv hV hV' hVV ha hVa hs hp hlev hK hQ =>
      qFCo_shK V V' a Lv cv hV hV' hVV ha hVa hs hp hlev hK hQ) qFCo_low hB hM hS I R hz h2
    (clField_QFCo I.good I.fc) (fun τ hτ => clField_QFCo (good3_take_any I R hl hτ) (hT τ hτ)) hSeed' hK
  exact fun n hn σ hσ => frameClosed_of_QFCo (key n hn σ hσ)

/-- **Residual: `FDsh` at the copy frames of the `t = 2` expansions** (2026-10-19; replaces the false pure `FDsh`).
Measured (trio-codex): 2,281,140 moving rewriting copy frames of the 13 sets, new FrameDom true at all. -/
def T2FDCopyRes : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2CopyK FDshAt M

/-- **t2-vs (seed)**: the `VSmallF` frames at the seed columns of `M[n]`. -/
def T2SeedVSFV2 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedFrames QVSF M

/-- **t2-fc (seed)**: the `FrameClosed` frames at the seed columns of `M[n]`. -/
def T2SeedFCV2 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
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
theorem t2VSFCV2_of (hB : T2BelowXResV2) (hFC : T2FDCopyRes) (hSV : T2SeedVSFV2) (hSF : T2SeedFCV2) : T2VSFCV2 := by
  intro M ρ rk C hz h2 n hn σ rkN hCN _ hGN _
  obtain ⟨hX, _⟩ := sInvXJ_std C.std C.ne
  have hl2 : 2 ≤ M.length := by
    obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
    rw [h2] at hr
    have := par_lt M 2 _ r hr; omega
  have IW := Inv3W.ofV2 C.S C.I
  have RW : Res3W M ρ rk := C.toW
  refine ⟨vsmallF_expand_t2V (hB M ρ rk C) C.std C.ne IW RW hz h2
      (fun τ hτ => ⟨(take_fields_ctx C.toStepCtxV2 hl2 hτ).1, (take_fields_ctx C.toStepCtxV2 hl2 hτ).2.1⟩)
      (hSV M ρ rk C hz h2) n (by omega) σ hCN hGN,
    frameClosed_expand_t2K (hB M ρ rk C) C.std C.ne IW RW hz h2 (fun τ hτ => (take_fields_ctx C.toStepCtxV2 hl2 hτ).2.2)
      (hSF M ρ rk C hz h2) (hFC M ρ rk C hz h2) n (by omega) σ hCN⟩

end Ytosk
