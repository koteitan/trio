/-
**3 行・t = 1: 最上位の仮定 hExp の t = 1 の部分（n ≥ 2）の組み立て。**

t = 1 の鎖（q ≠ r は `t1_main_final`、q = r は `qr_final4`）は、運ぶ性質 Pn を指定すると
M[n] の評価 ρN と順位 rkN で Cons・Rk・Good3・Pn を出す。ここでは Pn として
- 証明済みで運べるもの: FrameOT（`expStep_frameOT_t1`）・RootP（`expStep_rootP_t1`）・
  BumpDec（`expStep_bumpDec_t1`）・FrameClosed（`expStep_frameClosed_t1`、残りは FrameClosedOmN）、
- 残りの値の欄の束 `QV`（VSmallF と 9 項目。AbsU は AbsD から（`absU_of_absD`）、TrigOmC は `expStep_trigOmC` で運ぶ）
を使う。M.take x（鎖の始点）での値は、落とす補題（`valInv_drop1`・`rootP_drop1`）と、1 列落としの残り
（`hLast_of` の hRest と同じ形）から。
-/
import Ytosk.V3IndV
import Ytosk.V3TrigQR
import Ytosk.V3GroupA

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## TrigOmC along the chain, `q = r` -/

/-- No diagonal point on `b ++ Ω_{m+1}`. -/
theorem not_diag_app_om {a br μ : T} (hbr : br ≠ z) (m : T) :
    ∀ b, DiagAt a br μ (app b (psi (succ m) z z)) → False
  | z, h => not_diag_om hbr h
  | psi c d e, h => by
    generalize hU : app (psi c d e) (psi (succ m) z z) = U at h
    cases h with
    | here _ _ _ =>
      have := (T.psi.inj hU).2.2; simp only [app] at this
      exact absurd (app_eq_z this).2 (by simp)
    | rest h' =>
      have := (T.psi.inj hU).2.2
      rw [← this] at h'
      exact not_diag_app_om hbr m e h'
    | arg _ _ _ =>
      have := (T.psi.inj hU).2.2
      exact absurd (app_eq_z this).2 (by simp)
    | sub _ _ _ =>
      have := (T.psi.inj hU).2.2
      exact absurd (app_eq_z this).2 (by simp)

/-- **The witnesses of the hole data are those of `o(r) = ψ_μ(b + Ω_{μ+1})`.** -/
theorem holeT_pin {μ b μ' br' vr' : T} (hcb' : cof br' = .big μ')
    (hH : HoleT μ' br' vr' (psi μ (app b (psi (succ μ) z z)) z)) :
    μ' = μ ∧ br' = app b (psi (succ μ) z z) ∧ ¬ lt vr' μ = true := by
  have hXz : app b (psi (succ μ) z z) ≠ z := fun h => absurd (app_eq_z h).2 (by simp)
  have hcX : cof (app b (psi (succ μ) z z)) = .big μ := cof_br
  have hbr' : br' ≠ z := by intro h; rw [h] at hcb'; simp [cof] at hcb'
  rcases hH with hc | ⟨a', ha', hD⟩
  · have := DiagAt.cof_omega (DiagAt.here (a := μ) hXz hcX (lt_irrefl' μ))
    rw [this] at hc; cases hc
  · generalize hU : psi μ (app b (psi (succ μ) z z)) z = U at hD
    cases hD with
    | here _ hc _ =>
      obtain ⟨h1, h2, _⟩ := T.psi.inj hU
      subst h1; subst h2
      rw [hcX] at hc
      exact ⟨(Cof.big.inj hc).symm, rfl, ha'⟩
    | rest _ => exact absurd (T.psi.inj hU).2.2.symm (by simp)
    | arg _ _ hD' =>
      rw [← (T.psi.inj hU).2.1] at hD'
      exact (not_diag_app_om hbr' μ b hD').elim
    | sub _ _ _ => exact absurd (T.psi.inj hU).2.1 (fun h => hXz h)

/-- **TrigOmC is carried** (`t = 1`, `q = r`): the residuals `hShape`, `hLeaf` of `trigOm_N_t1` are
`qr_hShape`, `qr_hLeaf` once the hole data is pinned (`holeT_pin`). -/
theorem expStep_trigOmC_qr {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r) :
    ExpStepT1 TrigOmC M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  obtain ⟨b, hro, hbe, _⟩ := qr_o_r hlen I.r0p I.sd h1 hx2 hq I.cons I.good I.rank
  have hox := o_last_t1 hlen I.cons I.good h1 (by have := par1_entry_lt h1; omega) hx2
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq
  have hrD : DepX M (r + L) true r := dep_anc_x I.uat I.z2 I.r12 I.be hlen hx2 hA
  intro n hn ρP Z hCP _ hTOP _ _ _ _ hle hlex hH
  obtain ⟨μ', br', vr', seed, k0, hHD, hZ, hPr⟩ := hH
  have hHr := hHD.hole true r hrD (by omega)
  simp only [valB, cond_true] at hHr
  rw [hro] at hHr
  obtain ⟨hμ', hbr', hvr'⟩ := holeT_pin hHD.cb hHr
  subst hμ' hbr'
  have hot : isOT (psi (ρ.v r) (app b (psi (succ (ρ.v r)) z z)) z) = true := by
    rw [← hro]; exact I.good.ot_o r (by omega)
  have hSr := hHD.S (ρ.v r) hvr' hot
  have hseedz : seed ≠ z := by obtain ⟨a, X, h⟩ := hHD.seedS; rw [h]; simp
  have hZz : ∀ c, Z c ≠ z := fun c => by
    obtain ⟨k, _, hk⟩ := hZ c; rw [hk]; exact gamS_ne_z_q hseedz k
  have hxnb := hxnb_t1 hlen hL hA hd0e I.z2 I.z1 h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn
  have hσx : (glueZ M (r + L) ρ (shiftV ρP L) Z).o (r + L) = ρP.o r := by
    rw [glueZ_o_ge ρ (shiftV ρP L) Z (Nat.le_refl _)]
    show ρP.o (r + L - L) = ρP.o r; rw [Nat.add_sub_cancel]
  exact trigOm_N_t1 hlen hL hA hd0e hn hpath hx2 hxnb (I.z2 r) hiu hiux hOS I.cons hCP I.trig hTOP
    (qr_hShape hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 h1 hq I.cons I.good I.kd I.td I.ad hro hox hOS hZz)
    (fun c hc hd => (hle c hc hd).1)
    (qr_hLeaf hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 h1 hq I.cons I.good I.kd I.td I.ad hro hox hOS rfl
      hSr hseedz hbe.symm ⟨k0, by rw [hσx]; exact hPr⟩)
    ⟨_, hox⟩

/-! ## TrigOmC along the chain, `q ≠ r` -/

theorem gamS_ne_z_gen {μ b seed : T} (hs : seed ≠ z) : ∀ k, gamS μ b seed k ≠ z
  | 0 => hs
  | k + 1 => by show psi μ _ z ≠ z; simp

/-- **TrigOmC is carried** (`t = 1`, `q ≠ r`). `hShape`: `Z c` is a chain term; from the second term on
it is `ψ_μ(b_r[γ])` with `b_r[γ] ≠ 0`, and the seed is `o(r)` in `M[n − 1]`, whose argument is not `0`
(`r` has a counted child, `first_child_counted_take`); so `Z c` is not a successor and `hole_om_shape`
applies. `hLeaf`: a `D` child with old value `Ω_{t+1}` is `x` (a `D` leaf below `x` would have a successor
`v`, against its hole, or a counted child, against the zero argument); at `x` the new value is at most
`Ω_{v(r)+1}`, so its subscript is at most `v(r) < v(q)` (F1), and there is no trigger. -/
theorem expStep_trigOmC_qn {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hqr : par M 0 (r + L) ≠ some r) :
    ExpStepT1 TrigOmC M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq
  have hox := o_last_t1 hlen I.cons I.good h1 (by have := par1_entry_lt h1; omega) hx2
  obtain ⟨hmemT, hcntT⟩ := first_child_counted_take hlen I.r0p I.z2 I.sd I.z1 I.uab h1 hqr
  have hcntM : Counted M r (r + 1) := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat r (r + 1) (by omega) hmemT hcntT
  have hmemM : r + 1 ∈ children M r := by
    rw [children_take, List.mem_filter] at hmemT; exact hmemT.1
  intro n hn ρP Z hCP _ hTOP _ _ _ _ hle hlex hH
  obtain ⟨μ', br', vr', seed, k0, hHD, hZ, hPr⟩ := hH
  -- the value of `r` in `M[n − 1]` has a nonzero argument
  have hPa : ∃ σ, ρP.o r = psi (sf (ρP.v r)) σ z ∧ σ ≠ z := by
    by_cases hn2 : n = 2
    · have hg : TRIO.gexp M r L d0 0 (n - 1) = M.take (r + L) := by
        rw [show n - 1 = 1 by omega]; exact gexp_one_eq hlen
      rw [hg] at hCP
      exact o_arg_ne_z hCP (by rw [List.length_take]; omega) hmemT hcntT
    · have hn' : 2 ≤ n - 1 := by omega
      have hS := sameAt_lt hlen hL hA hd0e hn' hpath hx2 (hxnb_t1 hlen hL hA hd0e I.z2 I.z1 h1 (n - 1) hn')
        (hiu_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn') (hiux_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn')
        r (by omega)
      have hlP := len_P (d0 := d0) (n := n) hlen
      exact o_arg_ne_z hCP (by rw [hlP]; have := Nat.mul_pos (show 0 < n - 1 by omega) hL; omega) (by rw [hS.ch]; exact hmemM)
        ((counted_iff_of_cnt (hS.cnt _ hmemM)).mpr hcntM)
  have hseedz : seed ≠ z := by obtain ⟨a, X, h⟩ := hHD.seedS; rw [h]; simp
  have hZs : ∀ c, Z c ≠ z ∧ isSucc (Z c) = false := by
    intro c
    obtain ⟨k, hk0, hk⟩ := hZ c
    rw [hk]
    cases k with
    | zero =>
      have : k0 = 0 := by omega
      subst this
      obtain ⟨σ, hσ, hσz⟩ := hPa
      show seed ≠ z ∧ isSucc seed = false
      rw [show seed = gamS μ' br' seed 0 from rfl, ← hPr, hσ]
      exact ⟨by simp, isSucc_psi_z' (Or.inr hσz)⟩
    | succ k =>
      refine ⟨gamS_ne_z_gen hseedz (k + 1), ?_⟩
      show isSucc (psi μ' (fs br' (gamS μ' br' seed k)) z) = false
      exact isSucc_psi_z' (Or.inr (fs_ne_z_big hHD.cb (gamS_ne_z_gen hseedz k)))
  have hxnb := hxnb_t1 hlen hL hA hd0e I.z2 I.z1 h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn
  have hσx : (glueZ M (r + L) ρ (shiftV ρP L) Z).o (r + L) = ρP.o r := by
    rw [glueZ_o_ge ρ (shiftV ρP L) Z (Nat.le_refl _)]
    show ρP.o (r + L - L) = ρP.o r; rw [Nat.add_sub_cancel]
  refine trigOm_N_t1 hlen hL hA hd0e hn hpath hx2 hxnb (I.z2 r) hiu hiux hOS I.cons hCP I.trig hTOP
    ?_ (fun c hc hd => (hle c hc hd).1) ?_ ⟨_, hox⟩
  · -- hShape
    intro c hc hd s0 y0 h0 hy0 s ν h
    have hHc := hHD.hole true c hd hc
    simp only [valB, cond_true] at hHc
    rw [h0] at hHc
    exact hole_om_shape hHc hy0 (hZs c).1 (hZs c).2 h
  · -- hLeaf
    intro i Lc c R hi hch hcnt hcx hd t hto s ν hnew ht1 ht2
    have hcm : c ∈ children M i := by rw [hch]; simp
    have hcM := (mem_children hcm).2
    rcases Nat.lt_or_ge c (r + L) with hc | hc
    · exfalso
      rcases hOS c hc hd with ⟨hvc, hnc⟩ | ⟨_, L', c', R', hch', hcb', hcu', hR', _⟩
      · have hHv := hHD.hole false c hvc hc
        simp only [valB, cond_false] at hHv
        have hoc := o_nocnt I.cons I.good hcM hnc
        rw [hto] at hoc
        have hs : succ t = ρ.v c := (T.psi.inj hoc).1
        have := holeT_not_succ hHv
        rw [← hs, isSucc_succ] at this; cases this
      · have hc'M := (mem_children (by rw [hch']; exact List.mem_append_right _ List.mem_cons_self :
          c' ∈ children M c)).2
        have hfr := o_frame I.cons I.good hcM hch' hcb' hcu' hR' hc'M
        obtain ⟨s3, y3, hc3⟩ := o_psi_form I.cons hc'M
        rw [hc3, spArg_single, hto] at hfr
        exact step_ne_z' _ _ _ _ _ (T.psi.inj hfr).2.1.symm
    · exfalso
      have hcx' : c = r + L := by omega
      subst hcx'
      have hix : par M 0 (r + L) = some i := (mem_children_iff.mp hcm).2
      have hiq : i = q := Option.some.inj (hix.symm.trans hq)
      have hri : r < i := by
        rcases Nat.eq_or_lt_of_le (par0_ge_of_anc hA (show r < r + L by omega) (Nat.le_refl _) hix) with h | h
        · exact absurd (h ▸ hix) hqr
        · exact h
      have hdi : DepX M (r + L) true i := dep_anc_x I.uat I.z2 I.r12 I.be hlen hx2 (anc0_of_par M 0 i _ hix)
      have hvi : ¬ DepX M (r + L) false i := by
        rcases hOS i hi hdi with ⟨_, hnc⟩ | ⟨hv, _⟩
        · rcases hnc _ hcm with h | h
          · exact absurd h hcnt.1
          · exact absurd h hcnt.2
        · exact hv
      have hF := hF1_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 I.cons I.good I.rank i hri hi hdi hvi
      -- the new value at `x` is at most `Ω_{v(r)+1}`
      have hle' : psi s (psi (succ ν) z z) z ≤ psi (succ (ρ.v r)) z z := by
        rw [← hnew, hσx, ← hox]; exact hlex.1
      have hsr : s ≤ ρ.v r := by
        rcases (le_iff _ _).mp hle' with h | h
        · rcases psi_lt_psi_z_iff.mp h with h' | ⟨_, h'⟩
          · exact lt_succ_iff.mp h'
          · exact absurd h' (T.not_lt_z _)
        · exact absurd (T.psi.inj h).2.1 (by simp)
      have his : ρ.v i ≤ s := by
        rcases psi_lt_psi_z_iff.mp ht2 with h | ⟨h, _⟩
        · exact le_of_lt h
        · rw [h]
      exact lt_irrefl' _ (lt_of_lt_of_le hF (le_trans his hsr))

/-- **TrigOmC is carried** (`t = 1`). -/
theorem expStep_trigOmC {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    ExpStepT1 TrigOmC M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  by_cases hqr : q = r
  · subst hqr; exact expStep_trigOmC_qr I hlen hL hd0e h1 hx2 hq
  · exact expStep_trigOmC_qn I hlen hL hd0e h1 hx2 (fun h => hqr (Option.some.inj (hq.symm.trans h)))

/-- **The value fields of `Inv3V` not yet carried by a proven step** (`t = 1`). -/
def QV (N : Mat) (σ : Valn) : Prop :=
  VSmallF N σ ∧ AbsD N σ ∧ TP1C N σ ∧ TPLo N σ ∧ TP1WC N σ ∧ TPLoW N σ ∧ AbsUW N σ ∧
    AbsDW N σ ∧ TPLoN N σ ∧ AbsDN N σ

/-- **The property carried along the `t = 1` chain.** -/
def PT1 (N : Mat) (σ : Valn) : Prop :=
  FrameOT N σ ∧ RootP N σ ∧ BumpDec N σ ∧ FrameClosed N σ ∧ TrigOmC N σ ∧ QV N σ

/-- The 11 value fields of `M.take x` with the drop valuation that the drop lemma does not give
(the residual of `hLast_of`, without `rootP` and `Res3A`). -/
def RestT (M : Mat) (rk : Bool → Nat → Nat) : Prop :=
  let x := M.length - 1
  let σ := drop1 M x rk
  AbsD (M.take x) σ ∧ TP1C (M.take x) σ ∧ TPLo (M.take x) σ ∧
    TP1WC (M.take x) σ ∧ TPLoW (M.take x) σ ∧ AbsUW (M.take x) σ ∧ AbsDW (M.take x) σ ∧
    TrigOmC (M.take x) σ ∧ TPLoN (M.take x) σ ∧ AbsDN (M.take x) σ

/-- **`Inv3V` from the chain's output.** -/
theorem inv3V_of_PT1 {N : Mat} {σ : Valn} {rk : Bool → Nat → Nat} (hC : Cons N σ) (hR : Rk N rk)
    (hG : Good3 N σ) (hP : PT1 N σ) : Inv3V N σ rk :=
  let ⟨fo, rp, ⟨kd, td⟩, fc, trig, vs, ad, tp1, tplo, tp1w, tplow, auw, adw, tplon, adn⟩ := hP
  ⟨hC, hG, hR, vs, fc, fo, kd, td, ad, absU_of_absD hC hG ad, tp1, tplo, tp1w, tplow, auw, adw, trig, tplon, adn,
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
  obtain ⟨ad, tp1, tplo, tp1w, tplow, auw, adw, trig, tplon, adn⟩ := hRT'
  have hP1 : PT1 (M.take (r + L)) (drop1 M (r + L) rk) :=
    ⟨V1.fo, hRP1, ⟨V1.kd, V1.td⟩, V1.fc, trig, V1.vs, ad, tp1, tplo, tp1w, tplow, auw, adw, tplon, adn⟩
  have hPs : ExpStepT1 PT1 M r L (entry M 0 (r + L) - entry M 0 r) ρ :=
    expStep_and (expStep_frameOT_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.fo)
      (expStep_and (expStep_rootP_t1 hlen hL0 hd0e I.z2 I.uat I.r12 I.be I.r01 I.e00 hr hx2 I.rootP)
        (expStep_and (expStep_bumpDec_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.good
            ⟨I.kd, I.td⟩)
          (expStep_and (expStep_frameClosed_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq
              I.cons I.good I.fc hOm) (expStep_and (expStep_trigOmC I hlen hL0 hd0e hr hx2) hQs))))
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
