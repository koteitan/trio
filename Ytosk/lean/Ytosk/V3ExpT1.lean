/-
**3 行・t = 1: 最上位の仮定 hExp の t = 1 の部分（n ≥ 2）の組み立て。**

t = 1 の鎖（q ≠ r は `t1_main_final`、q = r は `qr_final4`）は、運ぶ性質 Pn を指定すると
M[n] の評価 ρN と順位 rkN で Cons・Rk・Good3・Pn を出す。ここでは Pn = `PT1`:
- 残りの仮定なしで運ぶもの: FrameOT・RootP・BumpDec（t1-struct）、FrameClosed（`expStep_frameClosed_t1'`、
  `FrameClosedOmN` を鎖の穴の情報から `frameClosedOmN_t1`）、TrigOmC（`expStep_trigOmC`）、
  TP1C・TP1WC（`expStep_tpG`・`qr2_tpG`、fsD の合成 `fsD_comp`）。AbsU は AbsD から（`absU_of_absD`）。
- TPLoN・TPLo は残り `TPLoNRes`・`TPLoRes`（退化した添字 = q = r・n = 2 の種と、種の条件 `SeedCond`、
  groupA の tplo_fsD_gen の残り）つきで運ぶ（`expStep_tploN`・`expStep_tplo`）。
- 残りの値の欄の束 `QV`（VSmallF・AbsD・TPLoW・AbsUW・AbsDW・AbsDN）は仮定 `hQs`。
M.take x（鎖の始点）での値は、落とす補題（`valInv_drop1`・`rootP_drop1`）と、1 列落としの残り
（`hLast_of` の hRest と同じ形の `RestT`）から。M[n] の `Res3A` は仮定 `hRes`。
-/
import Ytosk.V3IndV
import Ytosk.V3TrigQR
import Ytosk.V3GroupA
import Ytosk.V3FsdComp

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
  obtain ⟨μ', br', vr', seed, k0, hHD, hZ, hPr, _⟩ := hH
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
  obtain ⟨μ', br', vr', seed, k0, hHD, hZ, hPr, _⟩ := hH
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

/-! ## 最後の加数の添字の不変条件（TPLo 系）の補題 -/

theorem ohole_last : ∀ {t : T}, OHole t → OHole (last t)
  | z, h => h
  | psi a b z, h => h
  | psi a b (psi c d e), h => by
    have h' : OHole (psi c d e) := h
    show OHole (last (psi c d e)); exact ohole_last h'

theorem last_app' : ∀ (P : T) {X : T}, X ≠ z → last (app P X) = last X
  | z, _, _ => rfl
  | psi a b P, X, hX => by
    simp only [app_psi]
    have hPX : app P X ≠ z := fun h => hX (app_eq_z h).2
    cases hc : app P X with
    | z => exact absurd hc hPX
    | psi d e f =>
      show last (psi d e f) = last X
      rw [← hc]; exact last_app' P hX

theorem last_ne_z'' : ∀ {t : T}, t ≠ z → last t ≠ z
  | z, h => absurd rfl h
  | psi a b z, _ => by simp [last]
  | psi a b (psi c d e), _ => by show last (psi c d e) ≠ z; exact last_ne_z'' (by simp)

theorem last_single' : ∀ {t : T}, t ≠ z → ∃ a b, last t = psi a b z
  | z, h => absurd rfl h
  | psi a b z, _ => ⟨a, b, rfl⟩
  | psi a b (psi c d e), _ => by show ∃ a b, last (psi c d e) = psi a b z; exact last_single' (by simp)

theorem fsD_init_last {t : T} (ht : t ≠ z) (ζ : T) : fsD t ζ = app (init t) (fsD (last t) ζ) := by
  conv => lhs; rw [← init_app_last t]
  exact fsD_app _ (last_ne_z'' ht) ζ

theorem le_of_app_le_app {P x y : T} (h : app P x ≤ app P y) : x ≤ y := by
  rcases lt_trichotomy' x y with h' | h' | h'
  · exact le_of_lt h'
  · rw [h']
  · exact absurd (lt_of_le_of_lt h (app_lt_app_left P h')) (lt_irrefl' _)

theorem allGe_of_split_snd {θ t : T} (h : (split t θ).2 = z) : AllGeT θ t := by
  intro q hq
  have ht := split_app θ t
  rw [h, app_z_right] at ht
  rw [← ht] at hq
  exact split_fst_ge θ t q hq

theorem split_snd_of_allGe {θ : T} : ∀ {t : T}, AllGeT θ t → (split t θ).2 = z
  | z, _ => rfl
  | psi a b c, h => by
    have hh : ¬ psi a b z < θ := h _ (by simp [summands])
    have hc : AllGeT θ c := fun q hq => h q (by simp [summands, hq])
    simp only [split]
    rw [if_neg (show ¬ lt (psi a b z) θ = true from hh)]
    exact split_snd_of_allGe hc

theorem allGe_app {θ P X : T} : AllGeT θ (app P X) ↔ AllGeT θ P ∧ AllGeT θ X := by
  unfold AllGeT
  rw [summands_app]
  constructor
  · intro h; exact ⟨fun q hq => h q (List.mem_append_left _ hq), fun q hq => h q (List.mem_append_right _ hq)⟩
  · rintro ⟨h1, h2⟩ q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact h1 q hq
    · exact h2 q hq

/-- **The last summand after `fsD`** when it is `Ω_a`: it comes from an old last summand `Ω_{a₀}` with a
hole in `a₀`, and `a = a₀⟨ζ⟩` (the index `ζ` is single with a nonzero argument). -/
theorem last_fsD_om {y0 ζ a : T} (hO : OHole y0) (hζz : ζ ≠ z) (hζ1 : ∃ μ X, ζ = psi μ X z ∧ X ≠ z)
    (hl : last (fsD y0 ζ) = psi a z z) :
    ∃ a0, last y0 = psi a0 z z ∧ a0 ≠ z ∧ isSucc a0 = false ∧ OHole a0 ∧ a = fsD a0 ζ ∧
      fsD y0 ζ = app (init y0) (psi a z z) := by
  have hy0z : y0 ≠ z := by intro h; subst h; exact hO
  have hl0 := ohole_last hO
  have hdec := fsD_init_last hy0z ζ
  have hlz : fsD (last y0) ζ ≠ z := fsD_ne_z_oh hl0 hζz
  rw [hdec, last_app' _ hlz] at hl
  obtain ⟨a0, b0, hl0e⟩ := last_single' hy0z
  rw [hl0e] at hl0 hl hdec
  unfold OHole at hl0
  by_cases hb : b0 = z
  · subst hb
    rw [if_pos rfl] at hl0
    obtain ⟨ha0, hl0⟩ := hl0
    by_cases has0 : isSucc a0 = true
    · exfalso
      rw [fsD_leaf has0 ha0] at hl
      obtain ⟨μ, X, hζe, hX⟩ := hζ1
      rw [hζe] at hl
      exact hX (T.psi.inj hl).2.1
    · have has0' : isSucc a0 = false := by simpa using has0
      have hOa0 : OHole a0 := by rcases hl0 with h | h; exact absurd h has0; exact h
      rw [fsD_sub ha0 has0'] at hl hdec
      have ha : fsD a0 ζ = a := (T.psi.inj hl).1
      refine ⟨a0, hl0e, ha0, has0', hOa0, ha.symm, ?_⟩
      rw [hdec, ha]
  · exfalso
    rw [if_neg hb] at hl0
    have hbs : isSucc b0 = false := by
      by_contra hc; rw [if_pos (by simpa using hc)] at hl0; exact hl0
    rw [if_neg (by rw [hbs]; simp)] at hl0
    rw [fsD_psi hb hbs] at hl
    have hfz : fsD b0 ζ ≠ z := by
      cases hcb : cof b0 with
      | big m => rw [fsD_eq_fs hcb]; exact fs_ne_z_big hcb hζz
      | zero => rw [hcb] at hl0; exact fsD_ne_z_oh hl0 hζz
      | succ => rw [hcb] at hl0; exact fsD_ne_z_oh hl0 hζz
      | omega => rw [hcb] at hl0; exact fsD_ne_z_oh hl0 hζz
    exact hfz (T.psi.inj hl).2.1

/-- **TPLoN at a new argument `y₀⟨ζ⟩`** from TPLoN at the old argument `y₀`, when the old last
subscript `a₀` is `ω`-cofinal and not a node (`fsD_comp` and monotonicity); the other old last
subscripts are the hypothesis `hRes`. -/
theorem tploN_fsD {y0 ζ θ : T} (hO : OHole y0) (hζz : ζ ≠ z) (hζs : isSucc ζ = false)
    (hζ1 : ∃ μ X, ζ = psi μ X z ∧ X ≠ z) (hle : fsD y0 ζ ≤ y0)
    (hM : AllGeT θ y0 → ∀ a0, last y0 = psi a0 z z → isSucc a0 = false → OHole a0 →
      cof a0 = .omega → NotNode a0 → ¬ psi (fsD a0 one) z z < θ)
    (hRes : ∀ a0, last y0 = psi a0 z z → isSucc a0 = false → OHole a0 →
      ¬ (cof a0 = .omega ∧ NotNode a0) → AllGeT θ y0 →
      isSucc (fsD a0 ζ) = false → OHole (fsD a0 ζ) → cof (fsD a0 ζ) = .omega → NotNode (fsD a0 ζ) →
      ¬ psi (fsD (fsD a0 ζ) one) z z < θ) :
    AllGeT θ (fsD y0 ζ) → ∀ a, last (fsD y0 ζ) = psi a z z → isSucc a = false → OHole a →
      cof a = .omega → NotNode a → ¬ psi (fsD a one) z z < θ := by
  intro hAll a hl has hOa hca hNa
  have hy0z : y0 ≠ z := by intro h; subst h; exact hO
  obtain ⟨a0, hl0e, _, has0, hOa0, ha, hdec⟩ := last_fsD_om hO hζz hζ1 hl
  -- the old argument has no low part either
  have hy0e : y0 = app (init y0) (psi a0 z z) := by rw [← hl0e]; exact (init_app_last y0).symm
  have hAll0 : AllGeT θ y0 := by
    rw [hdec] at hAll hle
    obtain ⟨hP, hA⟩ := allGe_app.mp hAll
    rw [hy0e]
    refine allGe_app.mpr ⟨hP, ?_⟩
    have hle' : psi a z z ≤ psi a0 z z := by
      apply le_of_app_le_app (P := init y0)
      conv => rhs; rw [← hy0e]
      exact hle
    intro q hq
    simp only [summands, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    intro hlt
    exact hA _ (by simp [summands]) (lt_of_le_of_lt hle' hlt)
  subst ha
  by_cases hcN : cof a0 = .omega ∧ NotNode a0
  · have h0 := hM hAll0 a0 hl0e has0 hOa0 hcN.1 hcN.2
    have hOζ := ohole_of_fsD hOa0 hζz hζs hOa
    rw [fsD_comp hOa0 hζz hζs]
    intro hlt
    apply h0
    refine lt_of_le_of_lt (le_psi_sub (fsD_mono_eta hOa0 ?_)) hlt
    exact one_le_of_ne_z (fsD_ne_z_oh hOζ (by simp [one]))
  · exact hRes a0 hl0e has0 hOa0 hcN hAll0 has hOa hca hNa

/-! ## 種の条件（groupA の tplo_fsD_gen・absorb_fsD_W の残り） -/

/-- **The seed condition** of the index `ζ` against the old index `η₀`, for the subterms of `s`. -/
def SeedCond (s ζ η0 θ : T) : Prop := ∀ u, SubS s u → u < ζ → u < η0 → u < fsD ζ θ

theorem seedCond_of_le {s ζ η0 θ : T} (h : η0 ≤ fsD ζ θ) : SeedCond s ζ η0 θ :=
  fun _ _ _ hu => lt_of_lt_of_le hu h

/-- The TPLo condition at one value `ψ_s(y)`. -/
def TPLoAt (s y : T) : Prop :=
  (split y (psi (succ s) z z)).2 = z →
    ∀ a, last y = psi a z z → isSucc a = false → OHole a →
    ¬ psi (fsD a (etaOm (holeLev y))) z z < psi (succ s) z z

/-- The old argument has no low part when the new one has none. -/
theorem allGe_back {y0 ζ a a0 θ : T} (hdec : fsD y0 ζ = app (init y0) (psi a z z))
    (hl0e : last y0 = psi a0 z z) (hle : fsD y0 ζ ≤ y0) (hAll : AllGeT θ (fsD y0 ζ)) : AllGeT θ y0 := by
  have hy0e : y0 = app (init y0) (psi a0 z z) := by rw [← hl0e]; exact (init_app_last y0).symm
  rw [hdec] at hAll hle
  obtain ⟨hP, hA⟩ := allGe_app.mp hAll
  rw [hy0e]
  refine allGe_app.mpr ⟨hP, ?_⟩
  have hle' : psi a z z ≤ psi a0 z z := by
    apply le_of_app_le_app (P := init y0)
    conv => rhs; rw [← hy0e]
    exact hle
  intro q hq
  simp only [summands, List.mem_cons, List.not_mem_nil, or_false] at hq
  subst hq
  intro hlt
  exact hA _ (by simp [summands]) (lt_of_le_of_lt hle' hlt)

/-- **The TPLo-type comparison at a new argument** from TPLo at the old one and the seed condition. -/
theorem tplo_new {s0 y0 ζ θ : T} (hO : OHole y0) (hζz : ζ ≠ z) (hζs : isSucc ζ = false)
    (hζ1 : ∃ μ X, ζ = psi μ X z ∧ X ≠ z) (hle : fsD y0 ζ ≤ y0) (hM : TPLoAt s0 y0)
    (hS : SeedCond s0 ζ (etaOm (holeLev y0)) θ) :
    (split (fsD y0 ζ) (psi (succ s0) z z)).2 = z → ∀ a, last (fsD y0 ζ) = psi a z z →
      ¬ psi (fsD a θ) z z < psi (succ s0) z z := by
  intro hsplit a hl
  have hAll := allGe_of_split_snd hsplit
  obtain ⟨a0, hl0e, _, has0, hOa0, ha, hdec⟩ := last_fsD_om hO hζz hζ1 hl
  have hAll0 := allGe_back hdec hl0e hle hAll
  have hM' := tpl_iff.mp (hM (split_snd_of_allGe hAll0) a0 hl0e has0 hOa0)
  have hN : s0 < a := by
    rw [hdec] at hAll
    exact tpl_iff.mp ((allGe_app.mp hAll).2 _ (by simp [summands]))
  rw [ha] at hN ⊢
  exact tpl_iff.mpr (tplo_fsD_gen hOa0 hζz hζs hM' hN hS)

/-- **TPLo at a new argument** (the index of the new hole is `etaOm (holeLev ζ)`). -/
theorem tploAt_new {s0 y0 ζ : T} (hO : OHole y0) (hζz : ζ ≠ z) (hζs : isSucc ζ = false)
    (hζ1 : ∃ μ X, ζ = psi μ X z ∧ X ≠ z) (hle : fsD y0 ζ ≤ y0) (hM : TPLoAt s0 y0)
    (hS : SeedCond s0 ζ (etaOm (holeLev y0)) (etaOm (holeLev ζ))) : TPLoAt s0 (fsD y0 ζ) := by
  intro hsplit a hl _ _
  rw [holeLev_fsD hO hζz hζs]
  exact tplo_new hO hζz hζs hζ1 hle hM hS hsplit a hl

/-- The TPLoN condition at one value `ψ_s(y)`. -/
def TPLoNAt (s y : T) : Prop :=
  (split y (psi (succ s) z z)).2 = z →
    ∀ a, last y = psi a z z → isSucc a = false → OHole a → cof a = .omega → NotNode a →
    ¬ psi (fsD a one) z z < psi (succ s) z z

/-- The hole information of `ExpStepT1` at level `n`. -/
def HoleInfo (M : Mat) (r L n : Nat) (ρ ρP : Valn) (Z : Nat → T) : Prop :=
  ∃ μ br vr seed k0, HoleData M (r + L) ρ μ br vr seed ∧
    (∀ i, ∃ k, k0 ≤ k ∧ Z i = gamS μ br seed k) ∧ ρP.o r = gamS μ br seed k0 ∧ k0 = n - 2 ∧
    μ = vr ∧ ρ.o r = psi vr br z

/-- The index is a single term `ψ_μ(X)` with `X ≠ 0` (every chain term except a degenerate seed). -/
def GoodIdx (ζ : T) : Prop := isSucc ζ = false ∧ ∃ μ X, ζ = psi μ X z ∧ X ≠ z

/-- **Residual: degenerate indices** (only the seed at `q = r`, `n = 2`): the field `F` at the new value. -/
def DegRes (F : T → T → Prop) (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ c, c < r + L → DepX M (r + L) true c → ∀ s0 y0, ρ.o c = psi s0 y0 z → y0 ≠ z →
    ¬ GoodIdx (Z c) → F s0 (fsD y0 (Z c))

/-- **Residual: the seed condition** at the `D` columns where `G s₀ y₀ ζ` holds (index `θ ζ` at the new
hole). -/
def SeedRes (G : T → T → T → Prop) (θf : T → T) (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ c, c < r + L → DepX M (r + L) true c → ∀ s0 y0, ρ.o c = psi s0 y0 z → y0 ≠ z →
    GoodIdx (Z c) → G s0 y0 (Z c) → SeedCond s0 (Z c) (etaOm (holeLev y0)) (θf (Z c))

/-- **Residual: a field `F` at the new value** at the `D` columns where `G s₀ y₀ ζ` holds. -/
def FieldRes (G : T → T → T → Prop) (F : T → T → Prop) (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ c, c < r + L → DepX M (r + L) true c → ∀ s0 y0, ρ.o c = psi s0 y0 z → y0 ≠ z →
    GoodIdx (Z c) → G s0 y0 (Z c) → F s0 (fsD y0 (Z c))

/-- The TPLo pattern at the new value `ψ_{s₀}(y₀⟨ζ⟩)`. -/
def TPLoPatN (s0 y0 ζ : T) : Prop :=
  (split (fsD y0 ζ) (psi (succ s0) z z)).2 = z ∧
    ∃ a, last (fsD y0 ζ) = psi a z z ∧ isSucc a = false ∧ OHole a

/-- The old last subscript is a node or `Ω`-cofinal. -/
def BadA0 (s0 y0 : T) : Prop :=
  ∃ a0, last y0 = psi a0 z z ∧ isSucc a0 = false ∧ OHole a0 ∧ ¬ (cof a0 = .omega ∧ NotNode a0)

/-- **The residual of the TPLoN carry** (`t = 1`): degenerate indices, and the columns whose old last
subscript is a node or `Ω`-cofinal (C′ 4 万行列で D の列の約 4%; the seed condition with `θ = 1` is false in
3 of them, so the instance itself is the residual). -/
def TPLoNRes (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  DegRes TPLoNAt M r L d0 ρ ∧ FieldRes (fun s0 y0 _ => BadA0 s0 y0) TPLoNAt M r L d0 ρ

/-- **The residual of the TPLo carry** (`t = 1`): degenerate indices, and the seed condition at the columns
with the TPLo pattern at the new value (C′ 4 万行列で 15413 件、例外 0). -/
def TPLoRes (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  DegRes TPLoAt M r L d0 ρ ∧ SeedRes TPLoPatN (fun ζ => etaOm (holeLev ζ)) M r L d0 ρ

theorem tploAt_of {M : Mat} {ρ : Valn} (h : TPLo M ρ) {c : Nat} (hc : c < M.length) {s y : T}
    (ho : ρ.o c = psi s y z) : TPLoAt s y :=
  fun hs a hl has hOa => h c hc s y ho hs a hl has hOa

/-- **TPLoN is carried** (`t = 1`). At a `D` column below `x` the new last subscript is `a₀⟨ζ⟩`; if `a₀`
is `ω`-cofinal and not a node, TPLoN of `M` persists (`tploN_fsD`). Residual `TPLoNRes`. -/
theorem expStep_tploN {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hRes : TPLoNRes M r L d0 ρ) :
    ExpStepT1 TPLoN M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq
  intro n hn ρP Z hCP _ hTPP hCN _ _ _ hle _ hH
  have hDeg := hRes.1 n hn ρP Z hH hCN
  have hSd := hRes.2 n hn ρP Z hH hCN
  obtain ⟨μ', br', vr', seed, k0, hHD, _, _, _, _, _⟩ := hH
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  intro c hc s y hσc hsplit a hl has hOa hca hNa
  rcases Nat.lt_or_ge c (r + L) with hc' | hc'
  · have hcM : c < M.length := by omega
    obtain ⟨s0, y0, h0⟩ := o_psi_form I.cons hcM
    by_cases hd : DepX M (r + L) true c
    · rw [hσ, glueZ_o_dep ρ (shiftV ρP L) Z hc' hd, h0] at hσc
      by_cases hy0 : y0 = z
      · exfalso
        subst hy0
        by_cases hs0 : isSucc s0 = true
        · -- a `D` leaf with old value `Ω_{t+1}` below `x`: impossible
          rcases hOS c hc' hd with ⟨hvc, hnc⟩ | ⟨_, L', c', R', hch', hcb', hcu', hR', _⟩
          · have hHv := hHD.hole false c hvc hc'
            simp only [valB, cond_false] at hHv
            have hoc := o_nocnt I.cons I.good hcM hnc
            rw [h0] at hoc
            have hs : s0 = ρ.v c := (T.psi.inj hoc).1
            have := holeT_not_succ hHv
            rw [← hs, hs0] at this; cases this
          · have hc'M := (mem_children (by rw [hch']; exact List.mem_append_right _ List.mem_cons_self :
              c' ∈ children M c)).2
            have hfr := o_frame I.cons I.good hcM hch' hcb' hcu' hR' hc'M
            obtain ⟨s3, y3, hc3⟩ := o_psi_form I.cons hc'M
            rw [hc3, spArg_single, h0] at hfr
            exact step_ne_z' _ _ _ _ _ (T.psi.inj hfr).2.1.symm
        · by_cases hs0z : s0 = z
          · subst hs0z; unfold fsD at hσc; simp at hσc
          · rw [fsD_sub hs0z (by simpa using hs0)] at hσc
            rw [← (T.psi.inj hσc).2.1] at hl
            simp [last] at hl
      · have hHc := hHD.hole true c hd hc'
        simp only [valB, cond_true] at hHc
        rw [h0] at hHc
        have hy0s := not_succ_arg_of_holeT hy0 hHc
        have hHy := holeT_arg hy0 hHc hHD.cb
        have hOy0 := ohole_of_holeT hHy
        rw [fsD_psi hy0 hy0s] at hσc
        obtain ⟨hss, hyy, _⟩ := T.psi.inj hσc
        subst hss hyy
        have hlec : psi s0 (fsD y0 (Z c)) z ≤ psi s0 y0 z := by
          have := (hle c hc' hd).1
          rw [h0, fsD_psi hy0 hy0s] at this; exact this
        have hyy0 : fsD y0 (Z c) ≤ y0 := by
          rcases (le_iff _ _).mp hlec with h' | h'
          · rcases psi_lt_psi_z_iff.mp h' with h'' | ⟨_, h''⟩
            · exact absurd h'' (lt_irrefl' _)
            · exact le_of_lt h''
          · rw [(T.psi.inj h').2.1]
        by_cases hgood : GoodIdx (Z c)
        · obtain ⟨hζs, μ, X, hζe, hX⟩ := hgood
          have hζz : Z c ≠ z := by rw [hζe]; simp
          by_cases hbad : BadA0 s0 y0
          · exact hSd c hc' hd s0 y0 h0 hy0 ⟨hζs, μ, X, hζe, hX⟩ hbad hsplit a hl has hOa hca hNa
          · refine tploN_fsD hOy0 hζz hζs ⟨μ, X, hζe, hX⟩ hyy0
              (fun hAll a0 hl0 has0 hOa0 hca0 hNa0 =>
                I.tplon c hcM s0 y0 h0 (split_snd_of_allGe hAll) a0 hl0 has0 hOa0 hca0 hNa0)
              (fun a0 hl0 has0 hOa0 hcN _ _ _ _ _ => absurd ⟨a0, hl0, has0, hOa0, hcN⟩ hbad)
              (allGe_of_split_snd hsplit) a hl has hOa hca hNa
        · exact hDeg c hc' hd s0 y0 h0 hy0 hgood hsplit a hl has hOa hca hNa
    · rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hc' hd] at hσc
      exact I.tplon c hcM s y hσc hsplit a hl has hOa hca hNa
  · -- a copy column
    obtain ⟨b, rfl⟩ : ∃ b, c = r + L + b := ⟨c - (r + L), by omega⟩
    have hσo : σ.o (r + L + b) = ρP.o (r + b) := by
      rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
      show ρP.o (r + L + b - L) = ρP.o (r + b); congr 1; omega
    rw [hσo] at hσc
    exact hTPP (r + b) (by rw [hlP]; rw [hlN] at hc; omega) s y hσc hsplit a hl has hOa hca hNa

/-- **TPLo is carried** (`t = 1`): at a `D` column below `x`, TPLo of `M` and the seed condition at the new
hole level (`tploAt_new`). Residual `TPLoRes`: degenerate indices and the seed condition. -/
theorem expStep_tplo {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hRes : TPLoRes M r L d0 ρ) :
    ExpStepT1 TPLo M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq
  intro n hn ρP Z hCP _ hTPP hCN _ _ _ hle _ hH
  have hDeg := hRes.1 n hn ρP Z hH hCN
  have hSd := hRes.2 n hn ρP Z hH hCN
  obtain ⟨μ', br', vr', seed, k0, hHD, _, _, _, _, _⟩ := hH
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  intro c hc s y hσc hsplit a hl has hOa
  rcases Nat.lt_or_ge c (r + L) with hc' | hc'
  · have hcM : c < M.length := by omega
    obtain ⟨s0, y0, h0⟩ := o_psi_form I.cons hcM
    by_cases hd : DepX M (r + L) true c
    · rw [hσ, glueZ_o_dep ρ (shiftV ρP L) Z hc' hd, h0] at hσc
      by_cases hy0 : y0 = z
      · exfalso
        subst hy0
        by_cases hs0 : isSucc s0 = true
        · -- a `D` leaf with old value `Ω_{t+1}` below `x`: impossible
          rcases hOS c hc' hd with ⟨hvc, hnc⟩ | ⟨_, L', c', R', hch', hcb', hcu', hR', _⟩
          · have hHv := hHD.hole false c hvc hc'
            simp only [valB, cond_false] at hHv
            have hoc := o_nocnt I.cons I.good hcM hnc
            rw [h0] at hoc
            have hs : s0 = ρ.v c := (T.psi.inj hoc).1
            have := holeT_not_succ hHv
            rw [← hs, hs0] at this; cases this
          · have hc'M := (mem_children (by rw [hch']; exact List.mem_append_right _ List.mem_cons_self :
              c' ∈ children M c)).2
            have hfr := o_frame I.cons I.good hcM hch' hcb' hcu' hR' hc'M
            obtain ⟨s3, y3, hc3⟩ := o_psi_form I.cons hc'M
            rw [hc3, spArg_single, h0] at hfr
            exact step_ne_z' _ _ _ _ _ (T.psi.inj hfr).2.1.symm
        · by_cases hs0z : s0 = z
          · subst hs0z; unfold fsD at hσc; simp at hσc
          · rw [fsD_sub hs0z (by simpa using hs0)] at hσc
            rw [← (T.psi.inj hσc).2.1] at hl
            simp [last] at hl
      · have hHc := hHD.hole true c hd hc'
        simp only [valB, cond_true] at hHc
        rw [h0] at hHc
        have hy0s := not_succ_arg_of_holeT hy0 hHc
        have hHy := holeT_arg hy0 hHc hHD.cb
        have hOy0 := ohole_of_holeT hHy
        rw [fsD_psi hy0 hy0s] at hσc
        obtain ⟨hss, hyy, _⟩ := T.psi.inj hσc
        subst hss hyy
        have hlec : psi s0 (fsD y0 (Z c)) z ≤ psi s0 y0 z := by
          have := (hle c hc' hd).1
          rw [h0, fsD_psi hy0 hy0s] at this; exact this
        have hyy0 : fsD y0 (Z c) ≤ y0 := by
          rcases (le_iff _ _).mp hlec with h' | h'
          · rcases psi_lt_psi_z_iff.mp h' with h'' | ⟨_, h''⟩
            · exact absurd h'' (lt_irrefl' _)
            · exact le_of_lt h''
          · rw [(T.psi.inj h').2.1]
        by_cases hgood : GoodIdx (Z c)
        · obtain ⟨hζs, μ, X, hζe, hX⟩ := hgood
          have hζz : Z c ≠ z := by rw [hζe]; simp
          exact tploAt_new hOy0 hζz hζs ⟨μ, X, hζe, hX⟩ hyy0 (tploAt_of I.tplo hcM h0)
            (hSd c hc' hd s0 y0 h0 hy0 ⟨hζs, μ, X, hζe, hX⟩ ⟨hsplit, a, hl, has, hOa⟩) hsplit a hl has hOa
        · exact hDeg c hc' hd s0 y0 h0 hy0 hgood hsplit a hl has hOa
    · rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hc' hd] at hσc
      exact I.tplo c hcM s y hσc hsplit a hl has hOa
  · -- a copy column
    obtain ⟨b, rfl⟩ : ∃ b, c = r + L + b := ⟨c - (r + L), by omega⟩
    have hσo : σ.o (r + L + b) = ρP.o (r + b) := by
      rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
      show ρP.o (r + L + b - L) = ρP.o (r + b); congr 1; omega
    rw [hσo] at hσc
    exact hTPP (r + b) (by rw [hlP]; rw [hlN] at hc; omega) s y hσc hsplit a hl has hOa

/-! ## TP1C along the chain -/

theorem ohole_app_inv : ∀ {P c : T}, c ≠ z → OHole (app P c) → OHole c
  | z, c, _, h => by simpa using h
  | psi a b P, c, hc, h => by
    simp only [app_psi] at h
    have hPc : app P c ≠ z := fun he => hc (app_eq_z he).2
    have h' : OHole (app P c) := by
      cases hX : app P c with
      | z => exact absurd hX hPc
      | psi => rw [hX] at h; exact h
    exact ohole_app_inv hc h'

/-- **The persistence invariants in one form**: at a rewriting frame with a hole in `y`, the head stays below
`fsD(y, η)` for the indices `η` allowed by `P y`. -/
def TPG (P : T → T → Prop) (M : Mat) (ρ : Valn) : Prop :=
  ∀ i L c R, children M i = L ++ c :: R → Counted M i c → ∀ s y, ρ.o c = psi s y z →
    lt (preState M ρ i L) y = true → lt (psi (ρ.v i) z z) (psi s y z) = true → OHole y →
    ∀ η, P y η → lt (preState M ρ i L) (fsD y η) = true

theorem tpG_iff_tp1C {M : Mat} {ρ : Valn} :
    TPG (fun y η => η = psi (holeLev y) one z) M ρ ↔ TP1C M ρ :=
  ⟨fun h i L c R hch hc s y ho h1 h2 hO => h i L c R hch hc s y ho h1 h2 hO _ rfl,
   fun h i L c R hch hc s y ho h1 h2 hO η hη => hη ▸ h i L c R hch hc s y ho h1 h2 hO⟩

theorem tpG_iff_tp1WC {M : Mat} {ρ : Valn} :
    TPG (fun y η => cof y = .omega ∧ η = one) M ρ ↔ TP1WC M ρ :=
  ⟨fun h i L c R hch hc s y ho h1 h2 hcy hO => h i L c R hch hc s y ho h1 h2 hO _ ⟨hcy, rfl⟩,
   fun h i L c R hch hc s y ho h1 h2 hO η ⟨hcy, hη⟩ => hη ▸ h i L c R hch hc s y ho h1 h2 hcy hO⟩

/-- **TPG is carried** (`t = 1`), from TP1C of `M`; the case `q = r` at `n = 2` is the hypothesis `hQR2` (proven in `qr2_tpG`; there the seed
`o_{M.take x}(r)` may be below `ψ_μ(1)`). At a `D` child below `x` the new argument is `y⟨ζ⟩`, and
`y⟨ζ⟩⟨θ⟩ = y⟨ζ⟨θ⟩⟩` (`fsD_comp`) with `ψ_μ(1) ≤ ζ⟨θ⟩` (`psi_one_le_fsD`; the hole of `y⟨ζ⟩` comes from `ζ`,
`ohole_of_fsD`), so TP1C of `M` persists (`persist_of_tp1`). At `x`: for `q ≠ r` no trigger (F1); for `q = r`
the new argument is `b + γ` and `fsD` keeps it above `b`. The copies are the frames of `M[n − 1]`. -/
theorem expStep_tpG {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    (P : T → T → Prop) (hPz : ∀ y η, P y η → η ≠ z) (hTGM : TPG P M ρ)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hQR2 : par M 0 (r + L) = some r → ExpStepT1At (TPG P) M r L d0 ρ 2) :
    ExpStepT1 (TPG P) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq
  have hox := o_last_t1 hlen I.cons I.good h1 (by have := par1_entry_lt h1; omega) hx2
  intro n hn ρP Z hCP hGP hTPP hCN hGN hoto hotv hle hlex hH
  by_cases hq2 : q = r ∧ n = 2
  · obtain ⟨hqr, rfl⟩ := hq2
    subst hqr
    exact hQR2 hq ρP Z hCP hGP hTPP hCN hGN hoto hotv hle hlex hH
  obtain ⟨μ', br', vr', seed, k0, hHD, hZ, hPr, hk0n, hμv, hro'⟩ := hH
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hxnb := hxnb_t1 hlen hL hA hd0e I.z2 I.z1 h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux
  have hσx : σ.o (r + L) = ρP.o r := by
    rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (Nat.le_refl _)]
    show ρP.o (r + L - L) = ρP.o r; rw [Nat.add_sub_cancel]
  -- `vr' = v(r)`
  have hvr' : vr' = ρ.v r := by
    obtain ⟨y1, hy1⟩ := o_psi_sub I.cons (show r < M.length by omega)
    rw [hro'] at hy1
    rw [(T.psi.inj hy1).1, sf_ot (I.good.ot_v r (by omega))]
  have hseedz : seed ≠ z := by obtain ⟨a, X, h⟩ := hHD.seedS; rw [h]; simp
  -- the chain terms used at the `D` columns
  have hZF : ∀ c, Z c ≠ z ∧ isSucc (Z c) = false ∧
      ∀ η, η ≠ z → OHole (Z c) → psi μ' one z ≤ fsD (Z c) η := by
    intro c
    obtain ⟨k, hk0, hk⟩ := hZ c
    rw [hk]
    cases k with
    | succ j =>
      have hX : fs br' (gamS μ' br' seed j) ≠ z := fs_ne_z_big hHD.cb (gamS_ne_z_gen hseedz j)
      exact ⟨gamS_ne_z_gen hseedz (j + 1), isSucc_psi_ne (Or.inr hX),
        fun η hη hO => psi_one_le_fsD hX hO hη⟩
    | zero =>
      -- `n = 2`, so `q ≠ r`, and the seed is `o(r)` in `M.take x`
      have hk00 : k0 = 0 := by omega
      have hn2 : n = 2 := by omega
      have hqr : q ≠ r := fun h => hq2 ⟨h, hn2⟩
      have hqr' : par M 0 (r + L) ≠ some r := fun h => hqr (Option.some.inj (hq.symm.trans h))
      subst hk00 hn2
      have hg : TRIO.gexp M r L d0 0 (2 - 1) = M.take (r + L) := gexp_one_eq hlen
      have hCP' : Cons (M.take (r + L)) ρP := hg ▸ hCP
      have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
      have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
      have hvP : ρP.v r = ρ.v r :=
        base_v_r hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hCP' hRk1 hA (by omega) hqr' hpath
      obtain ⟨hmemT, hcntT⟩ := first_child_counted_take hlen I.r0p I.z2 I.sd I.z1 I.uab h1 hqr'
      obtain ⟨σ0, hσ0, hσ0z⟩ := o_arg_ne_z hCP' (by rw [List.length_take]; omega) hmemT hcntT
      have hseed : seed = psi (sf (ρP.v r)) σ0 z := by rw [← hσ0, hPr]; rfl
      show seed ≠ z ∧ isSucc seed = false ∧ ∀ η, η ≠ z → OHole seed → psi μ' one z ≤ fsD seed η
      rw [hseed, hvP, sf_ot (I.good.ot_v r (by omega)), ← hvr', ← hμv]
      exact ⟨by simp, isSucc_psi_ne (Or.inr hσ0z), fun η hη hO => psi_one_le_fsD hσ0z hO hη⟩
  intro i Lc c R hch hcN s y hc ht1 ht2 hOy η hPη
  have hcmem : c ∈ children (TRIO.gexp M r L d0 0 n) i := by rw [hch]; simp
  have hcl := mem_children hcmem
  have hη : η ≠ z := hPz y η hPη
  rcases Nat.lt_or_ge i (r + L) with h | h
  · have hS := hSA i h
    rw [hS.ch] at hch hcmem
    have hcM : Counted M i c := (counted_iff_of_cnt (hS.cnt c hcmem)).mp hcN
    obtain ⟨hv, hpre⟩ := preState_lt hlen hL hA hd0e hn hpath hx2 hxnb (I.z2 r) hiu hiux (ρ := ρ) (ρP := ρP)
      (Z := Z) hOS h hch hcM
    rw [← hσ] at hv hpre
    rw [hpre] at ht1 ⊢
    rw [hv] at ht2
    have hcm := mem_children hcmem
    have hcx : c ≤ r + L := by have := (mem_children hcmem).2; omega
    by_cases hd : DepX M (r + L) true c
    · rcases Nat.lt_or_ge c (r + L) with hc' | hc'
      · -- a `D` child below `x`
        obtain ⟨s0, y0, h0⟩ := o_psi_form I.cons hcm.2
        have hσc : σ.o c = fsD (psi s0 y0 z) (Z c) := by
          rw [hσ, glueZ_o_dep ρ (shiftV ρP L) Z hc' hd, h0]
        obtain ⟨hζz, hζs, hζF⟩ := hZF c
        by_cases hy0 : y0 = z
        · exfalso
          subst hy0
          by_cases hs0 : isSucc s0 = true
          · -- a `D` leaf with old value `Ω_{t+1}` below `x`: impossible
            rcases hOS c hc' hd with ⟨hvc, hnc⟩ | ⟨_, L', c', R', hch', hcb', hcu', hR', _⟩
            · have hHv := hHD.hole false c hvc hc'
              simp only [valB, cond_false] at hHv
              have hoc := o_nocnt I.cons I.good hcm.2 hnc
              rw [h0] at hoc
              have hs : s0 = ρ.v c := (T.psi.inj hoc).1
              have := holeT_not_succ hHv
              rw [← hs, hs0] at this; cases this
            · have hc'M := (mem_children (by rw [hch']; exact List.mem_append_right _ List.mem_cons_self :
                c' ∈ children M c)).2
              have hfr := o_frame I.cons I.good hcm.2 hch' hcb' hcu' hR' hc'M
              obtain ⟨s3, y3, hc3⟩ := o_psi_form I.cons hc'M
              rw [hc3, spArg_single, h0] at hfr
              exact step_ne_z' _ _ _ _ _ (T.psi.inj hfr).2.1.symm
          · by_cases hs0z : s0 = z
            · subst hs0z
              rw [hσc] at hc; unfold fsD at hc; simp at hc
            · rw [hσc, fsD_sub hs0z (by simpa using hs0)] at hc
              rw [← (T.psi.inj hc).2.1] at ht1
              exact T.not_lt_z _ ht1
        · have hHc := hHD.hole true c hd hc'
          simp only [valB, cond_true] at hHc
          rw [h0] at hHc
          have hy0s := not_succ_arg_of_holeT hy0 hHc
          have hHy := holeT_arg hy0 hHc hHD.cb
          have hOy0 := ohole_of_holeT hHy
          have hlev := holeLev_holeT hHy
          rw [hσc, fsD_psi hy0 hy0s] at hc
          obtain ⟨hss, hyy, _⟩ := T.psi.inj hc
          subst hss hyy
          -- the trigger goes back to `M`
          have hlec : psi s0 (fsD y0 (Z c)) z ≤ psi s0 y0 z := by
            have := (hle c hc' hd).1
            rw [h0, fsD_psi hy0 hy0s] at this; exact this
          have hyy0 : fsD y0 (Z c) ≤ y0 := by
            rcases (le_iff _ _).mp hlec with h' | h'
            · rcases psi_lt_psi_z_iff.mp h' with h'' | ⟨_, h''⟩
              · exact absurd h'' (lt_irrefl' _)
              · exact le_of_lt h''
            · rw [(T.psi.inj h').2.1]
          have hTPM := I.tp1 i Lc c R hch hcM s0 y0 h0 (lt_of_lt_of_le ht1 hyy0)
            (lt_of_lt_of_le ht2 hlec) hOy0
          have hOζ := ohole_of_fsD hOy0 hζz hζs hOy
          rw [fsD_comp hOy0 hζz hζs]
          apply persist_of_tp1 hOy0 _ hTPM
          rw [hlev]; exact hζF _ hη hOζ
      · -- the frame of `x`
        have hcx' : c = r + L := by omega
        subst hcx'
        have hix : par M 0 (r + L) = some i := (mem_children_iff.mp hcmem).2
        have hiq : i = q := Option.some.inj (hix.symm.trans hq)
        subst hiq
        by_cases hqr : i = r
        · subst hqr
          -- `n ≥ 3`: the new value is `ψ_μ(b + γ)` with `γ` the previous chain term
          have hn3 : 3 ≤ n := by
            rcases Nat.lt_or_ge n 3 with h3 | h3
            · exact absurd ⟨rfl, by omega⟩ hq2
            · exact h3
          obtain ⟨b, hro, hbe, _⟩ := qr_o_r hlen I.r0p I.sd h1 hx2 hq I.cons I.good I.rank
          rw [hro] at hro'
          obtain ⟨_, hbr, _⟩ := T.psi.inj hro'
          obtain ⟨j, hj⟩ : ∃ j, k0 = j + 1 := ⟨k0 - 1, by omega⟩
          rw [hσx, hPr, hj] at hc
          change psi μ' (fs br' (gamS μ' br' seed j)) z = psi s y z at hc
          rw [← hbr, fs_br] at hc
          obtain ⟨_, hy, _⟩ := T.psi.inj hc
          subst hy
          have hγz : gamS μ' (app b (psi (succ (ρ.v i)) z z)) seed j ≠ z := gamS_ne_z_gen hseedz j
          have hOγ := ohole_app_inv hγz hOy
          -- the head is `b`
          have hR : R = [] := by
            rcases R with _ | ⟨d, R'⟩
            · rfl
            · exfalso
              have hdm : d ∈ children M i := by rw [hch]; simp
              have hsort := children_sorted M i
              rw [hch] at hsort
              have hcd := (List.pairwise_cons.mp (List.pairwise_append.mp hsort).2.1).1 d (by simp)
              have := (mem_children hdm).2; omega
          subst hR
          have hLc : (children M i).filter (fun d => decide (d < i + L)) = Lc := by
            rw [hch, List.filter_append]
            have h1' : Lc.filter (fun d => decide (d < i + L)) = Lc := by
              rw [List.filter_eq_self]
              intro d hd
              have hsort := children_sorted M i
              rw [hch] at hsort
              simpa using (List.pairwise_append.mp hsort).2.2 d hd (i + L) (by simp)
            rw [h1']; simp
          rw [← hLc, ← hbe]
          rw [fsD_app _ hγz]
          exact lt_app_of (fsD_ne_z_oh hOγ hη)
        · -- `q ≠ r`: no trigger (F1)
          exfalso
          have hqr' : par M 0 (r + L) ≠ some r := fun h' => hqr (Option.some.inj (hq.symm.trans h'))
          have hri : r < i := by
            rcases Nat.eq_or_lt_of_le (par0_ge_of_anc hA (show r < r + L by omega) (Nat.le_refl _) hix)
              with h' | h'
            · exact absurd h'.symm hqr
            · exact h'
          have hdi : DepX M (r + L) true i :=
            dep_anc_x I.uat I.z2 I.r12 I.be hlen hx2 (anc0_of_par M 0 i _ hix)
          have hvi : ¬ DepX M (r + L) false i := by
            rcases hOS i h hdi with ⟨_, hnc⟩ | ⟨hv', _⟩
            · rcases hnc _ hcmem with h' | h'
              · exact absurd h' hcM.1
              · exact absurd h' hcM.2
            · exact hv'
          have hF := hF1_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 I.cons I.good I.rank i hri h hdi hvi
          have hle' : psi s y z ≤ psi (succ (ρ.v r)) z z := by
            rw [← hc, hσx, ← hox]; exact hlex.1
          have hsr : s ≤ ρ.v r := by
            rcases (le_iff _ _).mp hle' with h' | h'
            · rcases psi_lt_psi_z_iff.mp h' with h'' | ⟨_, h''⟩
              · exact lt_succ_iff.mp h''
              · have hyz : y ≠ z := by intro hz'; rw [hz'] at ht1; exact T.not_lt_z _ ht1
                exact absurd h'' (T.not_lt_z _)
            · exfalso
              have hyz : y = z := (T.psi.inj h').2.1
              rw [hyz] at ht1; exact T.not_lt_z _ ht1
          have his : ρ.v i ≤ s := by
            rcases psi_lt_psi_z_iff.mp ht2 with h' | ⟨h', _⟩
            · exact le_of_lt h'
            · rw [h']
          exact lt_irrefl' _ (lt_of_lt_of_le hF (le_trans his hsr))
    · -- not in `D`: the frame of `M`
      have hc' : c < r + L := by
        rcases Nat.lt_or_ge c (r + L) with h' | h'
        · exact h'
        · exact absurd (show c = r + L by omega ▸ DepX.leaf) hd
      rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hc' hd] at hc
      exact hTGM i Lc c R hch hcM s y hc ht1 ht2 hOy η hPη
  · -- a copy column: the frame of `M[n − 1]`
    obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have ha : a < (n - 1) * L := by omega
    have hσo : ∀ b, σ.o (r + L + b) = ρP.o (r + b) := by
      intro b; rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
      show ρP.o (r + L + b - L) = ρP.o (r + b); congr 1; omega
    have hσv : σ.v (r + L + a) = ρP.v (r + a) := by
      rw [hσ, glueZ_v_ge ρ (shiftV ρP L) Z (by omega)]
      show ρP.v (r + L + a - L) = ρP.v (r + a); congr 1; omega
    rw [children_shift (d0 := d0) hlen hL hA hd0e hn ha] at hch
    obtain ⟨Lc', T', hsplit, hLc, hT⟩ := List.map_eq_append_iff.mp hch
    obtain ⟨c', R', hT', hc', hR⟩ := List.map_eq_cons_iff.mp hT
    subst hLc hc' hR
    rw [hT'] at hsplit
    have hc'm : c' ∈ children (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by rw [hsplit]; simp
    have hc'l := mem_children hc'm
    rw [hlP] at hc'l
    have hpre : preState (TRIO.gexp M r L d0 0 n) σ (r + L + a) (Lc'.map (· + L)) =
        preState (TRIO.gexp M r L d0 0 (n - 1)) ρP (r + a) Lc' := by
      unfold preState
      rw [hσv, List.map_map]
      congr 3
      apply List.map_congr_left
      intro d hd
      have hdm : d ∈ children (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by rw [hsplit]; simp [hd]
      exact cnt_copy hlen hL hA hd0e hn hpath (I.z2 r) ha hdm
    have hco : σ.o (c' + L) = ρP.o c' := by
      have := hσo (c' - r)
      rw [show r + L + (c' - r) = c' + L by omega, show r + (c' - r) = c' by omega] at this
      exact this
    rw [hpre] at ht1 ⊢
    rw [hσv] at ht2
    rw [hco] at hc
    have hcntP : Counted (TRIO.gexp M r L d0 0 (n - 1)) (r + a) c' := by
      refine (counted_iff_of_cnt1 (cnt_copy hlen hL hA hd0e hn hpath (I.z2 r) (ρ := ρ) (Z := Z) ha hc'm)
        hco ?_).mp hcN
      obtain ⟨s1, y1, he⟩ := o_psi_form hCP (i := c') (by rw [hlP]; omega)
      rw [he]; simp
    exact hTPP (r + a) Lc' c' R' hsplit hcntP s y hc ht1 ht2 hOy η hPη

/-- **TPG at `q = r`, `n = 2`** (the residual of `expStep_tpG`), for the two persistence invariants
(`hP`: an index allowed by `P` is nonzero; the `M`-side facts are TP1C, TP1WC, TrigOmC and TPG P of `M`).
At a `D` child below `x` with the seed `ζ = o_{M.take x}(r)` as index: the old argument `y₀` is either `b_r`
(then `b = 0` and TrigOmC makes the head `0`, or `b ≠ 0`, `seed ≥ ψ_μ(1)` and TP1C persists) or `ω`-cofinal
(TP1WC persists, or the seed is `1` and the hole disappears, `diag_fsD_one`). At `x`: the new argument
lies between `b` and `b + seed` (`SeedOK.lt_next`), so it is `b + δ` and `fsD` keeps it above `b`. -/
theorem qr2_tpG {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    (P : T → T → Prop) (hPz : ∀ y η, P y η → η ≠ z) (hTGM : TPG P M ρ)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r) :
    ExpStepT1At (TPG P) M r L d0 ρ 2 := by
  have hn : 2 ≤ 2 := le_refl 2
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq
  obtain ⟨b, hro, hbe, _⟩ := qr_o_r hlen I.r0p I.sd h1 hx2 hq I.cons I.good I.rank
  have hox := o_last_t1 hlen I.cons I.good h1 (by have := par1_entry_lt h1; omega) hx2
  have hbr0 : app b (psi (succ (ρ.v r)) z z) ≠ z := fun h => absurd (app_eq_z h).2 (by simp)
  have hcbr : cof (app b (psi (succ (ρ.v r)) z z)) = .big (ρ.v r) := cof_br
  intro ρP Z hCP _ hTPP _ _ _ _ hle hlex hH
  obtain ⟨μ', br', vr', seed, k0, hHD, hZ, hPr, hk0n, hμv, hro'⟩ := hH
  have hk00 : k0 = 0 := by omega
  subst hk00
  rw [hro] at hro'
  obtain ⟨hvr, hbr', _⟩ := T.psi.inj hro'
  subst hvr hμv hbr'
  -- now `μ' = vr' = v(r)` and `br' = b + Ω_{μ+1}`
  set μ := ρ.v r with hμ
  set br := app b (psi (succ μ) z z) with hbrdef
  have hot : isOT (psi μ br z) = true := by rw [← hro]; exact I.good.ot_o r (by omega)
  have hSr := hHD.S μ (lt_irrefl' μ) hot
  have hseedz : seed ≠ z := by obtain ⟨a, X, h⟩ := hHD.seedS; rw [h]; simp
  have hseedP : ρP.o r = seed := hPr
  -- the seed is `1`, or a non-successor
  have hseed1 : seed = one ∨ isSucc seed = false := by
    obtain ⟨a, X, h⟩ := hHD.seedS
    by_cases ha : a = z
    · by_cases hX : X = z
      · left; rw [h, ha, hX]; rfl
      · right; rw [h]; exact isSucc_psi_ne (Or.inr hX)
    · right; rw [h]; exact isSucc_psi_ne (Or.inl ha)
  -- `b ≠ 0` gives a big seed
  have hbig : b ≠ z → psi μ one z ≤ seed := by
    intro hbz
    have hr1x : r + 1 < r + L := by
      rcases Nat.lt_or_ge (r + 1) (r + L) with h | h
      · exact h
      · exfalso; apply hbz
        rw [hbe]; unfold preState
        have : (children M r).filter (fun d => decide (d < r + L)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro c hc
          have := (mem_children hc).1
          simp; omega
        rw [this]; rfl
    have hg : TRIO.gexp M r L d0 0 (2 - 1) = M.take (r + L) := gexp_one_eq hlen
    have hCP' : Cons (M.take (r + L)) ρP := hg ▸ hCP
    have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
    have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
    rw [← hseedP]
    exact qr_seed_big hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 I.cons I.good hCP' hRk1 hr1x
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := 2) hlen
  have hxnb := hxnb_t1 hlen hL hA hd0e I.z2 I.z1 h1 2 hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2 hxnb hiu hiux
  have hσx : σ.o (r + L) = ρP.o r := by
    rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (Nat.le_refl _)]
    show ρP.o (r + L - L) = ρP.o r; rw [Nat.add_sub_cancel]
  intro i Lc c R hch hcN s y hc ht1 ht2 hOy η hPη
  have hcmem : c ∈ children (TRIO.gexp M r L d0 0 2) i := by rw [hch]; simp
  have hcl := mem_children hcmem
  have hη : η ≠ z := hPz y η hPη
  rcases Nat.lt_or_ge i (r + L) with h | h
  · have hS := hSA i h
    rw [hS.ch] at hch hcmem
    have hcM : Counted M i c := (counted_iff_of_cnt (hS.cnt c hcmem)).mp hcN
    obtain ⟨hv, hpre⟩ := preState_lt hlen hL hA hd0e hn hpath hx2 hxnb (I.z2 r) hiu hiux (ρ := ρ) (ρP := ρP)
      (Z := Z) hOS h hch hcM
    rw [← hσ] at hv hpre
    rw [hpre] at ht1 ⊢
    rw [hv] at ht2
    have hcm := mem_children hcmem
    have hcx : c ≤ r + L := by have := (mem_children hcmem).2; omega
    by_cases hd : DepX M (r + L) true c
    · rcases Nat.lt_or_ge c (r + L) with hc' | hc'
      · -- a `D` child below `x`
        obtain ⟨s0, y0, h0⟩ := o_psi_form I.cons hcm.2
        have hσc : σ.o c = fsD (psi s0 y0 z) (Z c) := by
          rw [hσ, glueZ_o_dep ρ (shiftV ρP L) Z hc' hd, h0]
        obtain ⟨_, a', ha', hD⟩ := qr_holeD hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 h1 hq I.cons I.good
          I.kd I.td I.ad hro hox hOS true c hd hc'
        simp only [valB, cond_true] at hD
        rw [h0] at hD
        obtain ⟨k, _, hk⟩ := hZ c
        -- the old argument is nonzero
        have hy0 : y0 ≠ z := by
          intro hy0; subst hy0
          generalize hU : psi s0 z z = U at hD
          cases hD with
          | here hb _ _ => exact hb (T.psi.inj hU).2.1.symm
          | rest _ => exact absurd (T.psi.inj hU).2.2.symm (by simp)
          | arg hb _ _ => exact hb (T.psi.inj hU).2.1.symm
          | sub ha hs hD' =>
            -- `ψ_{s0}(0)` with `s0` not a successor: the new argument is `0`
            have hs0 : s0 ≠ z := by rw [(T.psi.inj hU).1]; exact ha
            have hs0s : isSucc s0 = false := by rw [(T.psi.inj hU).1]; exact hs
            rw [hσc, fsD_sub hs0 hs0s] at hc
            rw [← (T.psi.inj hc).2.1] at ht1
            exact T.not_lt_z _ ht1
        have hHc : HoleT μ br μ (psi s0 y0 z) := Or.inr ⟨a', ha', hD⟩
        have hy0s := not_succ_arg_of_holeT hy0 hHc
        have hHy := holeT_arg hy0 hHc hcbr
        have hOy0 := ohole_of_holeT hHy
        have hlev := holeLev_holeT hHy
        rw [hσc, fsD_psi hy0 hy0s] at hc
        obtain ⟨hss, hyy, _⟩ := T.psi.inj hc
        subst hss hyy
        have hlec : psi s0 (fsD y0 (Z c)) z ≤ psi s0 y0 z := by
          have := (hle c hc' hd).1
          rw [h0, fsD_psi hy0 hy0s] at this; exact this
        have hyy0 : fsD y0 (Z c) ≤ y0 := by
          rcases (le_iff _ _).mp hlec with h' | h'
          · rcases psi_lt_psi_z_iff.mp h' with h'' | ⟨_, h''⟩
            · exact absurd h'' (lt_irrefl' _)
            · exact le_of_lt h''
          · rw [(T.psi.inj h').2.1]
        have ht1M : lt (preState M ρ i Lc) y0 = true := lt_of_lt_of_le ht1 hyy0
        have ht2M : lt (psi (ρ.v i) z z) (psi s0 y0 z) = true := lt_of_lt_of_le ht2 hlec
        cases k with
        | succ j =>
          -- a chain term from the second on
          rw [hk] at hOy ⊢
          have hX : fs br (gamS μ br seed j) ≠ z := fs_ne_z_big hcbr (gamS_ne_z_gen hseedz j)
          have hζz : gamS μ br seed (j + 1) ≠ z := gamS_ne_z_gen hseedz (j + 1)
          have hζs : isSucc (gamS μ br seed (j + 1)) = false := isSucc_psi_ne (Or.inr hX)
          have hOζ := ohole_of_fsD hOy0 hζz hζs hOy
          rw [fsD_comp hOy0 hζz hζs]
          apply persist_of_tp1 hOy0 _ (I.tp1 i Lc c R hch hcM s0 y0 h0 ht1M ht2M hOy0)
          rw [hlev]; exact psi_one_le_fsD hX hOζ hη
        | zero =>
          -- the seed
          change Z c = seed at hk
          rw [hk] at hOy ⊢
          -- the shape of `y₀`
          generalize hU : psi s0 y0 z = U at hD
          cases hD with
          | here _ _ _ =>
            have hyb : y0 = br := (T.psi.inj hU).2.1
            subst hyb
            by_cases hbz : b = z
            · -- `b = 0`: TrigOmC makes the head `0`
              have hbr1 : br = psi (succ μ) z z := by rw [hbrdef, hbz]; rfl
              rw [hbr1] at h0 ht1M ht2M
              have hB0 := I.trig i Lc c R hch hcM s0 μ h0 ht1M ht2M
              rw [hB0]
              have := fsD_ne_z_oh hOy hη
              exact lt_of_le_of_ne (z_le _) (Ne.symm this)
            · -- `b ≠ 0`: the seed is at least `ψ_μ(1)`
              have hsb := hbig hbz
              obtain ⟨a, X, hsX⟩ := hHD.seedS
              have hsom := hSr.lt_om
              rw [hsX] at hsb hsom
              have haμ : a = μ := by
                rcases psi_lt_psi_z_iff.mp hsom with h' | ⟨_, h'⟩
                · rcases (le_iff _ _).mp hsb with h'' | h''
                  · rcases psi_lt_psi_z_iff.mp h'' with h3 | ⟨h3, _⟩
                    · exact absurd (lt_succ_iff.mp h') (fun hle' => lt_irrefl' _ (lt_of_lt_of_le h3 hle'))
                    · exact h3.symm
                  · exact (T.psi.inj h'').1.symm
                · exact absurd h' (T.not_lt_z _)
              have hXz : X ≠ z := by
                intro hX; subst hX haμ
                rcases (le_iff _ _).mp hsb with h'' | h''
                · rcases psi_lt_psi_z_iff.mp h'' with h3 | ⟨_, h3⟩
                  · exact lt_irrefl' _ h3
                  · exact T.not_lt_z _ h3
                · exact absurd (T.psi.inj h'').2.1 (by simp [one])
              have hζs : isSucc seed = false := by rw [hsX]; exact isSucc_psi_ne (Or.inr hXz)
              have hOζ := ohole_of_fsD hOy0 hseedz hζs hOy
              rw [fsD_comp hOy0 hseedz hζs]
              apply persist_of_tp1 hOy0 _ (I.tp1 i Lc c R hch hcM s0 _ h0 ht1M ht2M hOy0)
              rw [hlev]
              rw [hsX] at hOζ ⊢; rw [haμ] at hOζ ⊢
              exact psi_one_le_fsD hXz hOζ hη
          | rest _ => exact absurd (T.psi.inj hU).2.2.symm (by simp)
          | arg _ _ hDy =>
            have hyy : y0 = _ := (T.psi.inj hU).2.1
            rw [← hyy] at hDy
            have hcy : cof y0 = .omega := DiagAt.cof_omega hDy
            rcases hseed1 with h1s | hζs
            · -- the seed `1`: no hole is left
              exfalso
              rw [h1s] at hOy
              have hs1 : isSucc (fs br one) = true := by
                rw [hbrdef, fs_br, isSucc_app _ (by simp [one])]; rfl
              exact (diag_fsD_one hs1 hDy).2.2.2 hOy
            · have hOζ := ohole_of_fsD hOy0 hseedz hζs hOy
              rw [fsD_comp hOy0 hseedz hζs]
              exact persist_of_tp1 hOy0 (one_le_of_ne_z (fsD_ne_z_oh hOζ hη))
                (I.tp1w i Lc c R hch hcM s0 y0 h0 ht1M ht2M hcy hOy0)
          | sub _ _ _ => exact absurd (T.psi.inj hU).2.1 hy0
      · -- the frame of `x`: the new argument is `b + δ`
        have hcx' : c = r + L := by omega
        subst hcx'
        have hix : par M 0 (r + L) = some i := (mem_children_iff.mp hcmem).2
        have hir : i = r := Option.some.inj (hix.symm.trans hq)
        subst hir
        rw [hσx, hseedP] at hc
        have hR : R = [] := by
          rcases R with _ | ⟨d, R'⟩
          · rfl
          · exfalso
            have hdm : d ∈ children M i := by rw [hch]; simp
            have hsort := children_sorted M i
            rw [hch] at hsort
            have hcd := (List.pairwise_cons.mp (List.pairwise_append.mp hsort).2.1).1 d (by simp)
            have := (mem_children hdm).2; omega
        subst hR
        have hLc : (children M i).filter (fun d => decide (d < i + L)) = Lc := by
          rw [hch, List.filter_append]
          have h1' : Lc.filter (fun d => decide (d < i + L)) = Lc := by
            rw [List.filter_eq_self]
            intro d hd
            have hsort := children_sorted M i
            rw [hch] at hsort
            simpa using (List.pairwise_append.mp hsort).2.2 d hd (i + L) (by simp)
          rw [h1']; simp
        rw [← hLc, ← hbe] at ht1 ⊢
        -- the subscript of the seed is `μ`
        have hsom := hSr.lt_om
        have hnext := hSr.lt_next
        rw [hc] at hsom hnext
        have hsμ : s = μ := by
          have h2' : ρ.v i ≤ s := by
            rcases psi_lt_psi_z_iff.mp ht2 with h' | ⟨h', _⟩
            · exact le_of_lt h'
            · rw [h']
          rcases psi_lt_psi_z_iff.mp hsom with h' | ⟨_, h'⟩
          · have := lt_succ_iff.mp h'
            rcases (le_iff _ _).mp this with h'' | h''
            · exact absurd (lt_of_lt_of_le h'' h2') (lt_irrefl' _)
            · exact h''
          · exact absurd h' (T.not_lt_z _)
        rw [hsμ, hbrdef, fs_br] at hnext
        have hyb : y < app b (psi s y z) := by
          rcases psi_lt_psi_z_iff.mp hnext with h' | ⟨_, h'⟩
          · exact absurd h' (lt_irrefl' _)
          · rw [hsμ]; exact h'
        obtain ⟨c0, hc0, hc0z, _⟩ := between_app (A := b) (x := z) (y := psi s y z) (c := y)
          (by rw [app_z_right]; exact ht1) (le_of_lt hyb)
        have hc0z' : c0 ≠ z := by intro h'; rw [h'] at hc0z; exact T.not_lt_z _ hc0z
        rw [hc0] at hOy ⊢
        have hOc0 := ohole_app_inv hc0z' hOy
        rw [fsD_app _ hc0z']
        exact lt_app_of (fsD_ne_z_oh hOc0 hη)
    · -- not in `D`: the frame of `M`
      have hc' : c < r + L := by
        rcases Nat.lt_or_ge c (r + L) with h' | h'
        · exact h'
        · exact absurd (show c = r + L by omega ▸ DepX.leaf) hd
      rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hc' hd] at hc
      exact hTGM i Lc c R hch hcM s y hc ht1 ht2 hOy η hPη
  · -- a copy column: the frame of `M[1]`
    obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have ha : a < (2 - 1) * L := by omega
    have hσo : ∀ b, σ.o (r + L + b) = ρP.o (r + b) := by
      intro b; rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
      show ρP.o (r + L + b - L) = ρP.o (r + b); congr 1; omega
    have hσv : σ.v (r + L + a) = ρP.v (r + a) := by
      rw [hσ, glueZ_v_ge ρ (shiftV ρP L) Z (by omega)]
      show ρP.v (r + L + a - L) = ρP.v (r + a); congr 1; omega
    rw [children_shift (d0 := d0) hlen hL hA hd0e hn ha] at hch
    obtain ⟨Lc', T', hsplit, hLc, hT⟩ := List.map_eq_append_iff.mp hch
    obtain ⟨c', R', hT', hc', hR⟩ := List.map_eq_cons_iff.mp hT
    subst hLc hc' hR
    rw [hT'] at hsplit
    have hc'm : c' ∈ children (TRIO.gexp M r L d0 0 (2 - 1)) (r + a) := by rw [hsplit]; simp
    have hc'l := mem_children hc'm
    rw [hlP] at hc'l
    have hpre : preState (TRIO.gexp M r L d0 0 2) σ (r + L + a) (Lc'.map (· + L)) =
        preState (TRIO.gexp M r L d0 0 (2 - 1)) ρP (r + a) Lc' := by
      unfold preState
      rw [hσv, List.map_map]
      congr 3
      apply List.map_congr_left
      intro d hd
      have hdm : d ∈ children (TRIO.gexp M r L d0 0 (2 - 1)) (r + a) := by rw [hsplit]; simp [hd]
      exact cnt_copy hlen hL hA hd0e hn hpath (I.z2 r) ha hdm
    have hco : σ.o (c' + L) = ρP.o c' := by
      have := hσo (c' - r)
      rw [show r + L + (c' - r) = c' + L by omega, show r + (c' - r) = c' by omega] at this
      exact this
    rw [hpre] at ht1 ⊢
    rw [hσv] at ht2
    rw [hco] at hc
    have hcntP : Counted (TRIO.gexp M r L d0 0 (2 - 1)) (r + a) c' := by
      refine (counted_iff_of_cnt1 (cnt_copy hlen hL hA hd0e hn hpath (I.z2 r) (ρ := ρ) (Z := Z) ha hc'm)
        hco ?_).mp hcN
      obtain ⟨s1, y1, he⟩ := o_psi_form hCP (i := c') (by rw [hlP]; omega)
      rw [he]; simp
    exact hTPP (r + a) Lc' c' R' hsplit hcntP s y hc ht1 ht2 hOy η hPη

/-! ## FrameClosedOmN from the chain -/

/-- **The domination at a frame whose new argument extends the state**: if `y = B + δ` with `B` at or
above `Ω_{s+1}` and `0 < δ < Ω_{s+1}`, every `C ∈ (B, H(s, y)]` extends `B`, so the components of `B` are
components of `C`. -/
theorem frameDom_app {a B s δ : T} (hB : AllGeT (psi (succ s) z z) B) (hδz : δ ≠ z)
    (hδ : δ < psi (succ s) z z) (hot : isOT (psi s (app B δ) z) = true)
    (hsa : ∀ u, ¬ lt a u = true → ∀ g ∈ comps u s, ∃ d ∈ comps u a, g ≤ d) :
    FrameDom a B s (H s (app B δ)) := by
  have hsplit : split (app B δ) (psi (succ s) z z) = (B, δ) :=
    split_app_of hB (Or.inr (lt_of_le_of_lt (head_le_self δ) hδ))
  have hH : H s (app B δ) = app B (psi s (app B δ) z) := by
    rw [H_eq hot, hsplit]; simp only; rw [if_neg hδz]
  intro u hu C hBC _ hCX g hg
  rw [hH] at hCX
  obtain ⟨c0, hc0, _, _⟩ := between_app (A := B) (x := z) (y := psi s (app B δ) z) (c := C)
    (by rw [app_z_right]; exact hBC) hCX
  rcases hg with hg | hg
  · refine ⟨g, List.mem_cons_of_mem _ (List.mem_append_left _ ?_), le_refl _⟩
    rw [hc0, comps_app]; exact List.mem_append_left _ hg
  · obtain ⟨d, hd, hgd⟩ := hsa u hu g hg
    exact ⟨d, List.mem_cons_of_mem _ (List.mem_append_right _ hd), hgd⟩

/-- **FrameClosedOmN of the glued valuation** (`t = 1`), from the chain's hole information. Below `x` a
counted child with old value `Ω_{t+1}` is not in `D` (its new value is the old one, no trigger). At `x`:
for `q ≠ r` no trigger (F1); for `q = r` the new argument is `b + δ` with `δ < Ω_{μ+1}` (`frameDom_app`). -/
theorem frameClosedOmN_t1 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hn : 2 ≤ n)
    {ρP : Valn} {Z : Nat → T}
    (hGN : Good3 (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z))
    (hlex : ρP.o r ≤ ρ.o (r + L) ∧ ρP.o r ≠ z)
    (hH : ∃ μ br vr seed k0, HoleData M (r + L) ρ μ br vr seed ∧
      (∀ i, ∃ k, k0 ≤ k ∧ Z i = gamS μ br seed k) ∧ ρP.o r = gamS μ br seed k0 ∧ k0 = n - 2 ∧
      μ = vr ∧ ρ.o r = psi vr br z) :
    FrameClosedOmN M r L ρ (glueZ M (r + L) ρ (shiftV ρP L) Z) := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq
  have hox := o_last_t1 hlen I.cons I.good h1 (by have := par1_entry_lt h1; omega) hx2
  obtain ⟨μ', br', vr', seed, k0, hHD, _, hPr, hk0n, hμv, hro'⟩ := hH
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hσx : σ.o (r + L) = ρP.o r := by
    rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (Nat.le_refl _)]
    show ρP.o (r + L - L) = ρP.o r; rw [Nat.add_sub_cancel]
  intro i hi Lc c R hCL t hct htv s y hc ⟨ht1, ht2⟩
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcm : c ∈ children M i := cl_mem_children hcCL
  have hcnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
  have hcM := (mem_children hcm).2
  rcases Nat.lt_or_ge c (r + L) with hc' | hc'
  · exfalso
    by_cases hd : DepX M (r + L) true c
    · rcases hOS c hc' hd with ⟨hvc, hnc⟩ | ⟨_, L', c', R', hch', hcb', hcu', hR', _⟩
      · have hHv := hHD.hole false c hvc hc'
        simp only [valB, cond_false] at hHv
        have hoc := o_nocnt I.cons I.good hcM hnc
        rw [hct] at hoc
        have hs : succ t = ρ.v c := (T.psi.inj hoc).1
        have := holeT_not_succ hHv
        rw [← hs, isSucc_succ] at this; cases this
      · have hc'M := (mem_children (by rw [hch']; exact List.mem_append_right _ List.mem_cons_self :
          c' ∈ children M c)).2
        have hfr := o_frame I.cons I.good hcM hch' hcb' hcu' hR' hc'M
        obtain ⟨s3, y3, hc3⟩ := o_psi_form I.cons hc'M
        rw [hc3, spArg_single, hct] at hfr
        exact step_ne_z' _ _ _ _ _ (T.psi.inj hfr).2.1.symm
    · rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hc' hd, hct] at hc
      rw [← (T.psi.inj hc).2.1] at ht1
      exact T.not_lt_z _ ht1
  have hcx : c = r + L := by omega
  subst hcx
  have hix : par M 0 (r + L) = some i := (mem_children_iff.mp hcm).2
  have hiq : i = q := Option.some.inj (hix.symm.trans hq)
  subst hiq
  have hsy : psi s y z ≤ psi (succ (ρ.v r)) z z := by rw [← hc, hσx, ← hox]; exact hlex.1
  have hyz : y ≠ z := by intro h'; rw [h'] at ht1; exact T.not_lt_z _ ht1
  have hsr : s ≤ ρ.v r := by
    rcases (le_iff _ _).mp hsy with h' | h'
    · rcases psi_lt_psi_z_iff.mp h' with h'' | ⟨_, h''⟩
      · exact lt_succ_iff.mp h''
      · exact absurd h'' (T.not_lt_z _)
    · exact absurd (T.psi.inj h').2.1 hyz
  have his : ρ.v i ≤ s := by
    rcases psi_lt_psi_z_iff.mp ht2 with h' | ⟨h', _⟩
    · exact le_of_lt h'
    · rw [h']
  by_cases hqr : i = r
  · subst hqr
    obtain ⟨b, hro, hbe, hb⟩ := qr_o_r hlen I.r0p I.sd h1 hx2 hq I.cons I.good I.rank
    have hsμ : s = ρ.v i := le_antisymm hsr his
    subst hsμ
    -- the state is `b`
    have hRn : R = [] := by
      rcases R with _ | ⟨d, R'⟩
      · rfl
      · exfalso
        have hdCL : d ∈ CL M i := by rw [hCL]; simp
        have hdm := cl_mem_children hdCL
        have hsort := children_sorted M i
        have hdx : d ≤ i + L := by have := (mem_children hdm).2; omega
        have hCLs : (CL M i).Pairwise (· < ·) := List.Pairwise.filter _ hsort
        rw [hCL] at hCLs
        have := (List.pairwise_cons.mp (List.pairwise_append.mp hCLs).2.1).1 d (by simp)
        omega
    subst hRn
    have hBb : spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = b := by
      have hcv := cvals_eq_map I.cons I.good i
      rw [hCL] at hcv
      unfold cvals at hcv
      rw [qr_children hlen h1 hx2 hq, List.map_append, nzs_append] at hcv
      have hxc := qr_x_counted hlen h1 hx2 hq
      have hox0 : ρ.o (i + L) ≠ z := by rw [hox]; simp
      have hlast : nzs ([i + L].map (cnt M ρ i)) = [ρ.o (i + L)] := by
        simp only [List.map_cons, List.map_nil]
        rw [cnt_cnt ρ hxc.1 hxc.2]
        simp [nzs, hox0]
      rw [hlast, List.map_append, List.map_singleton] at hcv
      have := List.append_cancel_right hcv
      rw [hbe]; unfold preState; rw [this]
    rw [hBb] at ht1 ⊢
    -- pin the hole data
    rw [hro] at hro'
    obtain ⟨hvr, hbr', _⟩ := T.psi.inj hro'
    subst hvr hμv hbr'
    have hot : isOT (psi (ρ.v i) (app b (psi (succ (ρ.v i)) z z)) z) = true := by
      rw [← hro]; exact I.good.ot_o i (by omega)
    have hSr := hHD.S (ρ.v i) (lt_irrefl' _) hot
    have hcbr : cof (app b (psi (succ (ρ.v i)) z z)) = .big (ρ.v i) := cof_br
    have hotN : isOT (psi (ρ.v i) y z) = true := by rw [← hc]; exact hGN.ot_o (i + L) (by rw [hlN]; have := Nat.mul_pos (show 0 < n - 1 by omega) hL; omega)
    have hsa : ∀ u, ¬ lt (ρ.v i) u = true → ∀ g ∈ comps u (ρ.v i), ∃ d ∈ comps u (ρ.v i), g ≤ d :=
      fun _ _ g hg => ⟨g, hg, le_refl _⟩
    -- the new argument is `b + δ`
    rw [hσx, hPr] at hc
    cases k0 with
    | succ j =>
      change psi (ρ.v i) (fs (app b (psi (succ (ρ.v i)) z z)) (gamS (ρ.v i) _ seed j)) z = psi (ρ.v i) y z at hc
      rw [fs_br] at hc
      have hy := (T.psi.inj hc).2.1
      subst hy
      have hseedz : seed ≠ z := by obtain ⟨a, X, h⟩ := hHD.seedS; rw [h]; simp
      exact frameDom_app hb (gamS_ne_z_gen hseedz j)
        (gamS_lt_om hot hcbr (lt_irrefl' _) hSr j) hotN hsa
    | zero =>
      change seed = psi (ρ.v i) y z at hc
      have hnext := hSr.lt_next
      rw [fs_br, hc] at hnext
      have hyb : y < app b (psi (ρ.v i) y z) := by
        rcases psi_lt_psi_z_iff.mp hnext with h' | ⟨_, h'⟩
        · exact absurd h' (lt_irrefl' _)
        · exact h'
      obtain ⟨c0, hc0, hc0z, hc0le⟩ := between_app (A := b) (x := z) (y := psi (ρ.v i) y z) (c := y)
        (by rw [app_z_right]; exact ht1) (le_of_lt hyb)
      have hc0z' : c0 ≠ z := by intro h'; rw [h'] at hc0z; exact T.not_lt_z _ hc0z
      have hc0lt : c0 < psi (succ (ρ.v i)) z z := by
        apply lt_of_le_of_lt hc0le
        rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self _)
      rw [hc0] at hotN ⊢
      exact frameDom_app hb hc0z' hc0lt hotN hsa
  · -- `q ≠ r`: no trigger (F1)
    exfalso
    have hqr' : par M 0 (r + L) ≠ some r := fun h' => hqr (Option.some.inj (hq.symm.trans h'))
    have hri : r < i := by
      rcases Nat.eq_or_lt_of_le (par0_ge_of_anc hA (show r < r + L by omega) (Nat.le_refl _) hix) with h' | h'
      · exact absurd h'.symm hqr
      · exact h'
    have hdi : DepX M (r + L) true i := dep_anc_x I.uat I.z2 I.r12 I.be hlen hx2 (anc0_of_par M 0 i _ hix)
    have hvi : ¬ DepX M (r + L) false i := by
      rcases hOS i hi hdi with ⟨_, hnc⟩ | ⟨hv', _⟩
      · rcases hnc _ hcm with h' | h'
        · exact absurd h' hcnt.1
        · exact absurd h' hcnt.2
      · exact hv'
    have hF := hF1_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 I.cons I.good I.rank i hri hi hdi hvi
    exact lt_irrefl' _ (lt_of_lt_of_le hF (le_trans his hsr))

/-- **FrameClosed is carried** (`t = 1`), with no residual. -/
theorem expStep_frameClosed_t1' {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    ExpStepT1 (fun N σ => FrameClosed N σ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hox : ∃ t, ρ.o (r + L) = psi (succ t) z z :=
    ⟨_, o_last_t1 hlen I.cons I.good h1 (by have := par1_entry_lt h1; omega) hx2⟩
  intro n hn ρP Z hCP _ hFCP _ hGN hoto _ hle hlex hH
  have hxnb := hxnb_t1 hlen hL hA hd0e I.z2 I.z1 h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq
  exact frameClosed_N_t1 hlen hL hA hd0e hn hpath hx2 hxnb (I.z2 r) hiu hiux hCP hOS I.cons I.good I.fc
    (frameClosedOmN_t1 I hlen hL hd0e h1 hx2 hn hGN hlex hH) hoto hFCP
    (fun c hc hd => (hle c hc hd).1) hlex.1 hox

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
  VSmallF N σ ∧ AbsD N σ ∧ TPLoW N σ ∧ AbsUW N σ ∧ AbsDW N σ ∧ AbsDN N σ

/-- **The property carried along the `t = 1` chain.** -/
def PT1 (N : Mat) (σ : Valn) : Prop :=
  FrameOT N σ ∧ RootP N σ ∧ BumpDec N σ ∧ FrameClosed N σ ∧ TrigOmC N σ ∧ TP1C N σ ∧ TP1WC N σ ∧
    TPLoN N σ ∧ TPLo N σ ∧ QV N σ

theorem expStepAt_iff {P Q : Mat → Valn → Prop} (h : ∀ N σ, P N σ ↔ Q N σ) {M : Mat} {r L d0 n : Nat}
    {ρ : Valn} (hP : ExpStepT1At P M r L d0 ρ n) : ExpStepT1At Q M r L d0 ρ n :=
  fun ρP Z hCP hGP hQP hCN hGN ho hv hle hlex hH =>
    (h _ _).mp (hP ρP Z hCP hGP ((h _ _).mpr hQP) hCN hGN ho hv hle hlex hH)

theorem expStep_iff {P Q : Mat → Valn → Prop} (h : ∀ N σ, P N σ ↔ Q N σ) {M : Mat} {r L d0 : Nat}
    {ρ : Valn} (hP : ExpStepT1 P M r L d0 ρ) : ExpStepT1 Q M r L d0 ρ :=
  fun n hn ρP Z hCP hGP hQP hCN hGN ho hv hle hlex hH =>
    (h _ _).mp (hP n hn ρP Z hCP hGP ((h _ _).mpr hQP) hCN hGN ho hv hle hlex hH)

/-- **TP1C is carried** (`t = 1`). -/
theorem expStep_tp1C {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    ExpStepT1 TP1C M r L d0 ρ :=
  have hPz : ∀ y η, η = psi (holeLev y) one z → η ≠ z := fun y η h => by rw [h]; simp
  expStep_iff (fun _ _ => tpG_iff_tp1C)
    (expStep_tpG I _ hPz (tpG_iff_tp1C.mpr I.tp1) hlen hL hd0e h1 hx2
      (fun hq => qr2_tpG I _ hPz (tpG_iff_tp1C.mpr I.tp1) hlen hL hd0e h1 hx2 hq))

/-- **TP1WC is carried** (`t = 1`). -/
theorem expStep_tp1WC {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    ExpStepT1 TP1WC M r L d0 ρ :=
  have hPz : ∀ y η, (cof y = .omega ∧ η = one) → η ≠ z := fun y η h => by rw [h.2]; simp [one]
  expStep_iff (fun _ _ => tpG_iff_tp1WC)
    (expStep_tpG I _ hPz (tpG_iff_tp1WC.mpr I.tp1w) hlen hL hd0e h1 hx2
      (fun hq => qr2_tpG I _ hPz (tpG_iff_tp1WC.mpr I.tp1w) hlen hL hd0e h1 hx2 hq))

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
  let ⟨fo, rp, ⟨kd, td⟩, fc, trig, tp1, tp1w, tplon, tplo, vs, ad, tplow, auw, adw, adn⟩ := hP
  ⟨hC, hG, hR, vs, fc, fo, kd, td, ad, absU_of_absD hC hG ad, tp1, tplo, tp1w, tplow, auw, adw, trig, tplon, adn,
    rootS_of_good hC hG, rp⟩

/-- **`t = 1`, `n ≥ 2`, in the `gexp` form**: the valuation of `M[n]` with `Inv3V`, from the chains.
Residuals: the base `RestT` at `M.take x` and the step `hQs` of the uncarried value fields `QV`. -/
theorem inv3V_N_t1 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 1 (r + L) = some r)
    (hx2 : entry M 2 (r + L) = 0)
    (hRT : RestT M rk)
    (hQs : ExpStepT1 QV M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResN : TPLoNRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResL : TPLoRes M r L (entry M 0 (r + L) - entry M 0 r) ρ) :
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
    ⟨V1.fo, hRP1, ⟨V1.kd, V1.td⟩, V1.fc, trig, tp1, tp1w, tplon, tplo, V1.vs, ad, tplow, auw, adw, adn⟩
  have hPs : ExpStepT1 PT1 M r L (entry M 0 (r + L) - entry M 0 r) ρ :=
    expStep_and (expStep_frameOT_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.fo)
      (expStep_and (expStep_rootP_t1 hlen hL0 hd0e I.z2 I.uat I.r12 I.be I.r01 I.e00 hr hx2 I.rootP)
        (expStep_and (expStep_bumpDec_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.good
            ⟨I.kd, I.td⟩)
          (expStep_and (expStep_frameClosed_t1' I hlen hL0 hd0e hr hx2) (expStep_and (expStep_trigOmC I hlen hL0 hd0e hr hx2)
            (expStep_and (expStep_tp1C I hlen hL0 hd0e hr hx2)
              (expStep_and (expStep_tp1WC I hlen hL0 hd0e hr hx2)
                (expStep_and (expStep_tploN I hlen hL0 hd0e hr hx2 hResN)
                  (expStep_and (expStep_tplo I hlen hL0 hd0e hr hx2 hResL) hQs))))))))
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
- `hRes`: `Res3A` of `M[n]` (the drop residual `DropRes` of `M[n] → M[n].take` and the seed). -/
theorem hExp_t1
    (hRT : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → RestT M rk)
    (hQs : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      ExpStepT1 QV M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResN : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      TPLoNRes M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ TPLoRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
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
      (hQs M ρ rk hM hS I R r L hlen hr hx2)
      (hResN M ρ rk hM hS I R r L hlen hr hx2).1 (hResN M ρ rk hM hS I R r L hlen hr hx2).2 n hn
  rw [← hexp] at V
  exact ⟨ρN, rkN, V, hRes M ρ rk hM hS I R hz h1t n hn ρN rkN
    (Inv3.ofV (sInv_std (Std.exp n hM) hNS) V)⟩

end Ytosk
