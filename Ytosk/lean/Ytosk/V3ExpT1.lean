/-
**3 行・t = 1: 最上位の仮定 hExp の t = 1 の部分（n ≥ 2）の組み立て。**

t = 1 の鎖（q ≠ r は `t1_main_final`、q = r は `qr_final4`）は、運ぶ性質 Pn を指定すると
M[n] の評価 ρN と順位 rkN で Cons・Rk・Good3・Pn を出す。ここでは Pn として
- 証明済みで運べるもの: FrameOT（`expStep_frameOT_t1`）・RootP（`expStep_rootP_t1`）・
  BumpDec（`expStep_bumpDec_t1`）・FrameClosed（`expStep_frameClosed_t1`、残りは FrameClosedOmN）、
- 残りの値の欄の束 `QV`（VSmallF と 11 項目）
を使う。M.take x（鎖の始点）での値は、落とす補題（`valInv_drop1`・`rootP_drop1`）と、1 列落としの残り
（`hLast_of` の hRest と同じ形）から。
-/
import Ytosk.V3IndV
import Ytosk.V3TrigQR

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The value fields of `Inv3V` not yet carried by a proven step** (`t = 1`). -/
def QV (N : Mat) (σ : Valn) : Prop :=
  VSmallF N σ ∧ AbsD N σ ∧ AbsU N σ ∧ TP1C N σ ∧ TPLo N σ ∧ TP1WC N σ ∧ TPLoW N σ ∧ AbsUW N σ ∧
    AbsDW N σ ∧ TrigOmC N σ ∧ TPLoN N σ ∧ AbsDN N σ

/-- **The property carried along the `t = 1` chain.** -/
def PT1 (N : Mat) (σ : Valn) : Prop :=
  FrameOT N σ ∧ RootP N σ ∧ BumpDec N σ ∧ FrameClosed N σ ∧ QV N σ

/-- The 11 value fields of `M.take x` with the drop valuation that the drop lemma does not give
(the residual of `hLast_of`, without `rootP` and `Res3A`). -/
def RestT (M : Mat) (rk : Bool → Nat → Nat) : Prop :=
  let x := M.length - 1
  let σ := drop1 M x rk
  AbsD (M.take x) σ ∧ AbsU (M.take x) σ ∧ TP1C (M.take x) σ ∧ TPLo (M.take x) σ ∧
    TP1WC (M.take x) σ ∧ TPLoW (M.take x) σ ∧ AbsUW (M.take x) σ ∧ AbsDW (M.take x) σ ∧
    TrigOmC (M.take x) σ ∧ TPLoN (M.take x) σ ∧ AbsDN (M.take x) σ

/-- **`Inv3V` from the chain's output.** -/
theorem inv3V_of_PT1 {N : Mat} {σ : Valn} {rk : Bool → Nat → Nat} (hC : Cons N σ) (hR : Rk N rk)
    (hG : Good3 N σ) (hP : PT1 N σ) : Inv3V N σ rk :=
  let ⟨fo, rp, ⟨kd, td⟩, fc, vs, ad, au, tp1, tplo, tp1w, tplow, auw, adw, trig, tplon, adn⟩ := hP
  ⟨hC, hG, hR, vs, fc, fo, kd, td, ad, au, tp1, tplo, tp1w, tplow, auw, adw, trig, tplon, adn,
    rootS_of_good hC hG, rp⟩

/-- **`t = 1`, `n ≥ 2`, in the `gexp` form**: the valuation of `M[n]` with `Inv3V`, from the chains.
Residuals: the base `RestT` at `M.take x`, the step `hQs` of the uncarried value fields `QV`, and the
`FrameClosed` residual `FrameClosedOmN` of every glued valuation. -/
theorem inv3V_N_t1 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 1 (r + L) = some r)
    (hx2 : entry M 2 (r + L) = 0)
    (hRT : RestT M rk)
    (hQs : ExpStepT1 QV M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hOm : ∀ (ρP : Valn) (Z : Nat → T), FrameClosedOmN M r L ρ (glueZ M (r + L) ρ (shiftV ρP L) Z)) :
    ∀ n, 2 ≤ n → ∃ ρN rkN,
      Inv3V (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN rkN ∧
      isOT (root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN) = true ∧
      root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN < root M ρ := by
  intro n hn
  have hL0 : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; have := par_lt M 1 _ r hr; omega
    · exact h
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) hr
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
    have := anc0_e0_lt hA (by omega); omega
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hdr := R.drop
  have hsd := R.seed
  rw [show M.length - 1 = r + L by omega] at hdr hsd
  have hVI : ValInv M ρ := ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩
  have V1 := valInv_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank hVI hdr
  have hx0 : entry M 0 (r + L) ≠ 0 := by
    have := anc0_interval hA (r + L) (by omega) (Nat.le_refl _); omega
  have hRP1 := rootP_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r01 I.r12 I.e00 hx0 I.cons I.rank hVI hdr
    I.rootP
  have hRT' := hRT
  simp only [RestT] at hRT'
  rw [show M.length - 1 = r + L by omega] at hRT'
  obtain ⟨ad, au, tp1, tplo, tp1w, tplow, auw, adw, trig, tplon, adn⟩ := hRT'
  have hP1 : PT1 (M.take (r + L)) (drop1 M (r + L) rk) :=
    ⟨V1.fo, hRP1, ⟨V1.kd, V1.td⟩, V1.fc, V1.vs, ad, au, tp1, tplo, tp1w, tplow, auw, adw, trig, tplon, adn⟩
  have hPs : ExpStepT1 PT1 M r L (entry M 0 (r + L) - entry M 0 r) ρ :=
    expStep_and (expStep_frameOT_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.fo)
      (expStep_and (expStep_rootP_t1 hlen hL0 hd0e I.z2 I.uat I.r12 I.be I.r01 I.e00 hr hx2 I.rootP)
        (expStep_and (expStep_bumpDec_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.good
            ⟨I.kd, I.td⟩)
          (expStep_and (expStep_frameClosed_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq
              I.cons I.good I.fc hOm) hQs)))
  by_cases hqr : q = r
  · subst hqr
    obtain ⟨ρN, rkN, hCN, hRN, hGN, hPN, hot, hlt⟩ :=
      qr_final4 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2 hq
        I.cons I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua I.ad I.tp1w
        I.tplow I.auw I.adw I.tp1 I.trig I.tplon I.adn I.rootS I.rootP (hsd q hr hq) PT1 hP1 hPs n hn
    exact ⟨ρN, rkN, inv3V_of_PT1 hCN hRN hGN hPN, hot, hlt⟩
  · obtain ⟨s0, y0, h0⟩ := o_psi_form I.cons (show r < M.length by omega)
    obtain ⟨ρN, rkN, hCN, hRN, hGN, hPN, hot, hlt⟩ :=
      t1_main_final hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2
        (fun h' => hqr (Option.some.inj (hq.symm.trans h'))) I.cons I.good I.rank I.vs I.fc I.fo
        I.tp1 I.tplo I.ad I.au hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua rfl h0 I.rootS I.rootP
        V1.g PT1 hP1 hPs n hn
    exact ⟨ρN, rkN, inv3V_of_PT1 hCN hRN hGN hPN, hot, hlt⟩

/-- **The `t = 1` part of `hExp`** (`trio_terminates_main_T2`). Residuals (each stated for the `t = 1`
matrices only):
- `hRT`: the 11 value fields of `M.take x` with the drop valuation (also the residual of `hLast_of`);
- `hQs`: the uncarried value fields `QV` pass from `M[n − 1]` to the glued valuation of `M[n]`;
- `hOm`: `FrameClosedOmN` of the glued valuations (the residual of `frameClosed_N_t1`);
- `hRes`: `Res3A` of `M[n]` (the drop residual `DropRes` of `M[n] → M[n].take` and the seed). -/
theorem hExp_t1
    (hRT : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → RestT M rk)
    (hQs : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      ExpStepT1 QV M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hOm : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      ∀ (ρP : Valn) (Z : Nat → T), FrameClosedOmN M r L ρ (glueZ M (r + L) ρ (shiftV ρP L) Z))
    (hRes : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → ∀ n, 2 ≤ n →
      ∀ σ rkN, Inv3 (expand M n) σ rkN → Res3A (expand M n) σ rkN) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 →
      ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ Res3A (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hz h1t n hn hNS _
  obtain ⟨r, hr⟩ := parLast_of I.e00 I.r01 I.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hlen2 : 2 ≤ M.length := by
    by_contra h
    have hx0 : M.length - 1 = 0 := by omega
    apply hz
    rw [hx0]
    have e0 := I.e00
    have e1 := I.r01 0 e0
    have e2 := I.r12 0 e1
    exact (col_zero_iff M 0).mpr ⟨e0, e1, e2⟩
  have hx2 : entry M 2 (M.length - 1) = 0 := by
    unfold TRIO.srow at h1t
    by_cases ha : 0 < TRIO.entry M 2 (M.length - 1)
    · rw [if_pos ha] at h1t; cases h1t
    · show TRIO.entry M 2 (M.length - 1) = 0; omega
  rw [h1t] at hr
  have hexp := expand_eq_gexp_t1 M n hlen2 hzT (by rw [h1t]; exact hr) h1t
  have hrx : r < M.length - 1 := par_lt M 1 _ r hr
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  rw [hL] at hexp hr hx2
  simp only [Nat.add_sub_cancel_left] at hexp
  have hlen : r + L + 1 = M.length := by omega
  obtain ⟨ρN, rkN, V, _, _⟩ :=
    inv3V_N_t1 I R hlen hr hx2 (hRT M ρ rk hM hS I R hz h1t)
      (hQs M ρ rk hM hS I R r L hlen hr hx2) (hOm M ρ rk hM hS I R r L hlen hr hx2) n hn
  rw [← hexp] at V
  exact ⟨ρN, rkN, V, hRes M ρ rk hM hS I R hz h1t n hn ρN rkN
    (Inv3.ofV (sInv_std (Std.exp n hM) hNS) V)⟩

end Ytosk
