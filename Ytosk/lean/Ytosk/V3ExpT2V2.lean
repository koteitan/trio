/-
**最上位の t = 2 の枠 `ExpT2V2`・`R2V2` を埋める（2026-10-16、t2）。**

- `r2V2_of`: `R2V2`（t = 2 の下降の残り Res3T2）は `T2BelowXRes` と x − 1 の強い吸収 `T2UpgAbsW`（drop の UpgAbsXW から外した部分）から（`hR2_t2_ofW`）。
- `expT2V2_of`: `ExpT2V2` は `hExp_t2_inv3V2`（V3ExpT2Inv2）から。残りは名前つきの
  `T2BelowXRes`・`T2FOSeedV2`・`T2SeedPResV2`・`T2VSFCV2`・`T2VRAV2` と、top の共通の残り
  `HFrameV2`・`HLeafV2`（M[n] は標準形なので、その枠の欄と葉の条件はこの 2 つから出る）。
-/
import Ytosk.V3GlobV2
import Ytosk.V3ExpT2Inv2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **t2-fo**: the FrameOT part of the seed frames (`T2Rest3.foSeed` with the new context). -/
def T2FOSeedV2 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedFrames QFO M

/-- **t2-seed**: the PH3cG・FC3 residuals of the seed frames (`T2SeedQRRes`・`QNRes`・`SVRes`・`CRes`・
`T2SeedCNext`). -/
def T2SeedPResV2 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    G.T2SeedPRes M ρ

/-- **`T2BelowXRes` in the step context**: the part before `x` only at the matrices of the induction. -/
def T2BelowXResV2 : Prop := ∀ M ρ rk, StepCtxT2 M ρ rk → T2BelowXResAt M ρ rk

theorem T2BelowXRes.toV2 (h : T2BelowXRes) : T2BelowXResV2 := fun M ρ rk _ => h M ρ rk

/-- **t2-vs**: `VSmallF` and `FrameClosed` of `M[n]` (`T2Rest3.vs`・`fc` with the new context). -/
def T2VSFCV2 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ n, 2 ≤ n → ∀ σ rkN, Cons (expand M n) σ → Rk (expand M n) rkN → Good3 (expand M n) σ →
      PH3cG (expand M n) σ → VSmallF (expand M n) σ ∧ FrameClosed (expand M n) σ

/-- **t2-vra**: `VSmallRAll` of `M[n]`. -/
def T2VRAV2 : Prop :=
  ∀ M ρ rk, StepCtxT2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ n, 2 ≤ n → ∀ σ rkN, Cons (expand M n) σ → Rk (expand M n) rkN → Good3 (expand M n) σ →
      PH3cG (expand M n) σ → VSmallRAll (expand M n) σ

/-- `M[n]` (`n ≥ 1`, `t = 2`) is not empty. -/
theorem expand_ne_nil_t2 {M : Mat} (hX : SInvX M) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) {n : Nat} (hn : 1 ≤ n) : expand M n ≠ [] := by
  obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  rw [h2] at hr
  have hrx : r < M.length - 1 := par_lt M 2 _ r hr
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  have h := expand_eq_gexp M n (by omega) hzT (by rw [h2]; rw [hL]; rw [hL] at hr; exact hr)
  rw [h2, hL] at h
  simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
    Nat.add_sub_cancel_left] at h
  have hne : TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n ≠ [] := by
    intro hE
    have hl := TRIO.gexp_length (M := M) (j0 := r) (Lb := L)
      (d0 := entry M 0 (r + L) - entry M 0 r) (d1 := entry M 1 (r + L) - entry M 1 r) (n := n) hlen
    rw [hE] at hl
    have : L ≤ n * L := Nat.le_mul_of_pos_left L (by omega)
    simp at hl; omega
  rw [h]; exact hne

/-- **R2V2 from `T2BelowXRes`.** -/
theorem r2V2_of (hB : T2BelowXResV2) (hU2 : T2UpgAbsW) : R2V2 := by
  intro M ρ rk C hz h2
  exact hR2_t2_ofW (hB M ρ rk C) hU2 C.std (Inv3W.ofV2 C.S C.I) ⟨C.R.drop⟩ hz h2

/-- **ExpT2V2 from the named residuals.** -/
theorem expT2V2_of (hB : T2BelowXResV2) (hU2 : T2UpgAbsW) (hFO : T2FOSeedV2) (hPR : T2SeedPResV2) (hVF : T2VSFCV2)
    (hVA : T2VRAV2) (hF : HFrameV2) (hL : HLeafV2) : ExpT2V2 := by
  intro M ρ rk C hz h2 n hn
  obtain ⟨hX, _⟩ := sInvXJ_std C.std C.ne
  have hl2 : 2 ≤ M.length := by
    obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
    rw [h2] at hr
    have := par_lt M 2 _ r hr; omega
  obtain ⟨I1, _⟩ := C.pre (M.length - 1) (by omega) (by omega)
  have hE := expand_ne_nil_t2 hX hz h2 (n := n) (by omega)
  have hStd : Std (expand M n) := Std.exp n C.std
  obtain ⟨ρN, rkN, IN, _⟩ := hExp_t2_inv3V2 (hB M ρ rk C) hU2 C.std C.ne C.I C.R.drop I1 hz h2
    (hFO M ρ rk C hz h2) (hPR M ρ rk C hz h2)
    (fun m hm σ rkN hCN hRN hGN hPN => by
      have hEm := expand_ne_nil_t2 hX hz h2 (n := m) (by omega)
      have hSm : Std (expand M m) := Std.exp m C.std
      obtain ⟨hvs, hfc⟩ := hVF M ρ rk C hz h2 m hm σ rkN hCN hRN hGN hPN
      obtain ⟨hl1, hl2⟩ := hL _ σ rkN hSm (ne_SRO_of_rk hRN) hEm hCN hRN hGN
      exact ⟨hvs, hfc, hVA M ρ rk C hz h2 m hm σ rkN hCN hRN hGN hPN,
        hF _ σ rkN hSm (ne_SRO_of_rk hRN) hEm hCN hRN hGN, hl1, hl2⟩) n hn
  exact ⟨ρN, rkN, IN⟩

end Ytosk
