/-
**3 行・t = 2: x より前の残り T2BelowXRes を 1 つの M ごとに分解する（2026-10-17、t2）。**

`t2BelowXRes_of_L`（V3T2SeedWire）の M ごとの形 `t2BelowXResAt_of_L`: T2BelowXResAt M ⟸ T2BelowResL（各 r, L）∧
種の残り G.T2SeedPRes M ∧ 種の閉じた形の標準形 T2SeedOTAt M。
V2 の文脈では T2BelowResL の T2HardB のうち VSmallRA・PH3cG は Inv3V2 から、RwClosed は t0 の T0RwRes から出る。
残りは種での RClaimU・REr と AbsWN（`T2BelowRV2`）と種の標準形（`T2SeedOTV2`）だけ（`t2BelowXResV2_of`）。
-/
import Ytosk.V3T2SeedWire
import Ytosk.V3ExpT2V2
import Ytosk.V3T0Inv2S

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- `T2BelowResL` at every `r, L` of one `M`. -/
def T2BelowResLAt (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
    T2BelowResL M ρ r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r)

/-- The standard forms of the seed closed forms at one `M` (the body of `T2SeedOTAll`). -/
def T2SeedOTAt (M : Mat) (ρ : Valn) : Prop :=
  ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r →
    (T2QRNoUpg M r L → ∀ Lc, CL M r = Lc ++ [r + L] → T2SeedQROT M ρ r L Lc) ∧
    (∀ q Lc, par M 0 (r + L) = some q → q ≠ r → CL M r = Lc ++ [q] → T2SeedQNOT M ρ r L q Lc) ∧
    (T2SVCase M r L → T2SeedSVOT M ρ r L) ∧
    (∀ q, par M 0 (r + L) = some q → q ≠ r → (¬ ∃ Lc, CL M r = Lc ++ [q]) → T2SeedCOT M ρ r L q)

/-- **`T2BelowXResAt` from `T2BelowResL`, the seed residuals and the seed standard forms, at one `M`.** -/
theorem t2BelowXResAt_of_L {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hL : T2BelowResLAt M ρ)
    (hP : G.T2SeedPRes M ρ) (hOTs : T2SeedOTAt M ρ) : T2BelowXResAt M ρ rk := by
  intro hM hS I R hz h2 r L hlen hr n hn hGlow σ hCN hOT
  obtain ⟨h2', h3⟩ := hL r L hlen hr n hn hGlow σ hCN hOT
  obtain ⟨hO1, hO2, hO3, hO4⟩ := hOTs r L hlen hr
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  have hrx : r < r + L := par_lt M 2 _ _ hr
  have hlen2 : 2 ≤ M.length := by omega
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hexp : ∀ m, expand M m = TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) m := by
    intro m
    have h := expand_eq_gexp M m hlen2 hzT (by rw [h2, show M.length - 1 = r + L by omega]; exact hr)
    rw [h2, show M.length - 1 = r + L by omega] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hRk : ∀ m, 1 ≤ m → ∃ rk', Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
      (entry M 1 (r + L) - entry M 1 r) m) rk' := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  obtain ⟨rkN, hRN⟩ := hRk n (by omega)
  obtain ⟨rkP, hRP⟩ := hRk (n - 1) (by omega)
  have hCP := cons_of_rk hRP
  have hGP := hGlow (n - 1) (by omega) (by omega) _ hCP
  have hcnt := counted_take_last (M := M) (by omega) I.r0p I.z2 I.sd I.z1 I.uat
  rw [show M.length - 1 = r + L by omega] at hcnt
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC0 := cons_of_rk hRk1
  have hP1 : TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) 1 =
      M.take (r + L) := gexp_one_gen hlen
  have hG0 : Good3 (M.take (r + L)) (rhsIt (M.take (r + L)) (rkBound (M.take (r + L)) rk)) := by
    have h := hGlow 1 (le_refl 1) (by omega) _ (by rw [hP1]; exact hC0)
    rwa [hP1] at h
  -- the seed is `r`
  have hpr : ∀ p, T2Seed M r L p → p = r := by
    intro p hp
    rcases hp with ⟨_, rfl⟩ | ⟨q, hq, hqr, hpq⟩
    · rfl
    · rw [par0_q_t2 hM hS I hlen hr hq hqr] at hpq; cases hpq; rfl
  -- the decrease of the counted children of the seed and of `q`
  have hD : (cvals (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n)
      σ r).Pairwise (fun a b => b ≤ a) ∧
      (∀ q, par M 0 (r + L) = some q → q ≠ r → (cvals (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n) σ q).Pairwise (fun a b => b ≤ a)) := by
    rw [cvals_eq_mapC hCN]
    rcases t2_seed_cases hlen hr with hc | hc | hc | hc
    · obtain ⟨hq, hXu⟩ := hc
      obtain ⟨he2r, h1lt⟩ := par2_facts I.z2 (by omega) hr
      have hxb : col M (r + L) ≠ bump M r := fun h => by
        have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
      obtain ⟨Lc, hCLM⟩ := cl_r_split hlen hq hXu hxb
      have hRes := hP.qr r L hlen hr hq hXu Lc hCLM
      have hks1 : succ (ρ.v r) < ρ.v (r + L) := by rw [succ_eq_addN_one]; exact hRes.ks 1
      refine ⟨seed_dec_qr hM hS I R hz h2 hlen hr hq hXu hCLM hn hCN hRN hCP hGP hRP hks1, ?_⟩
      intro q hq' hqr; rw [hq] at hq'; cases hq'; exact absurd rfl hqr
    · obtain ⟨q, Lc, hq, hqr, hCLM⟩ := hc
      have hRes := hP.qn r L q hlen hr hq hqr Lc hCLM
      have hvq := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
      obtain ⟨hd1, hd2⟩ := seed_dec_qn hM hS I R hz h2 hlen hr hq hqr hCLM hn hCN hRN hCP hGP hRP
        (by rw [hvq]; exact hRes.vqlt)
      refine ⟨hd1, fun q' hq' _ => ?_⟩
      rw [hq] at hq'; cases hq'
      rw [cvals_eq_mapC hCN]; exact hd2
    · obtain ⟨hq, hux⟩ := hc
      have hRes := hP.sv r L hlen hr hq hux
      refine ⟨seed_dec_sv hM hS I R hz h2 hlen hr hq hux (topP_sv hlen I.z2 I.z1 hr hq hux) hn hCN hRN hCP hGP hRP hC0 hG0 hRk1
        (hRes.decP _ hC0), ?_⟩
      intro q hq' hqr; rw [hq] at hq'; cases hq'; exact absurd rfl hqr
    · obtain ⟨q, hq, hqr, hncl⟩ := hc
      have hRes := (hP.C r L q hlen hr hq hqr hncl).1
      have hvq := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
      obtain ⟨hd1, hd2⟩ := seed_dec_C hM hS I R hz h2 hlen hr hq hqr (qP_C hM hS I hlen hr hq hqr hncl hRes.un) hRes.un hn hCN hRN hCP hGP hRP
        hC0 hG0 hRk1 (v_take_of_untopped I hlen hrx (topP_C hM hS I hlen hr hq hqr) hC0) (by rw [hvq]; exact hRes.vqP _ hC0)
        (fun Lc c0 h => by rw [hvq]; exact hRes.decP _ hC0 Lc c0 h)
      refine ⟨hd1, fun q' hq' _ => ?_⟩
      rw [hq] at hq'; cases hq'
      rw [cvals_eq_mapC hCN]; exact hd2
  -- the seed `r` keeps its `v` (the frame lemmas of the four cases)
  have hvr : σ.v r = ρ.v r := by
    rcases t2_seed_cases hlen hr with hc | hc | hc | hc
    · obtain ⟨hq, hXu⟩ := hc
      obtain ⟨he2r, h1lt⟩ := par2_facts I.z2 (by omega) hr
      have hxb : col M (r + L) ≠ bump M r := fun h => by
        have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
      obtain ⟨Lc, hCLM⟩ := cl_r_split hlen hq hXu hxb
      exact (qr_frame hM hS I R hz h2 hlen hr hq hXu hCLM hn hCN hRN hCP hGP hRP).2.1
    · obtain ⟨q, Lc, hq, hqr, hCLM⟩ := hc
      exact (qn_frame hM hS I R hz h2 hlen hr hq hqr hCLM hn hCN hRN hCP hGP hRP).2.2.1
    · obtain ⟨hq, hux⟩ := hc
      have htP := topP_sv hlen I.z2 I.z1 hr hq hux
      rw [(sv_frame hM hS I R hz h2 hlen hr hq hux htP hn hCN hRN hCP hGP hRP hC0 hG0 hRk1).2.2.1]
      exact v_take_of_untopped I hlen hrx htP hC0
    · obtain ⟨q, hq, hqr, hncl⟩ := hc
      have hRes := (hP.C r L q hlen hr hq hqr hncl).1
      have hvq := vq_eq_gexp hM hS I hz h2 hlen hr hn hCN hq hqr
      exact (C_frame hM hS I R hz h2 hlen hr hq hqr (qP_C hM hS I hlen hr hq hqr hncl hRes.un) hRes.un hn hCN hRN
        hCP hGP hRP hC0 hG0 hRk1 (v_take_of_untopped I hlen hrx (topP_C hM hS I hlen hr hq hqr) hC0)
        (by rw [hvq]; exact hRes.vqP _ hC0)).2.2.1
  have hdecr : ((CL (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) r).map
      σ.o).Pairwise (fun a b => b ≤ a) := by rw [← cvals_eq_mapC hCN]; exact hD.1
  -- the standard form of the seed and of `q`
  have hOTr : isOT (σ.o r) = true ∧ ∀ q, par M 0 (r + L) = some q → q ≠ r → isOT (σ.o q) = true := by
    rcases t2_seed_cases hlen hr with hc | hc | hc | hc
    · obtain ⟨hq, hXu⟩ := hc
      obtain ⟨he2r, h1lt⟩ := par2_facts I.z2 (by omega) hr
      have hxb : col M (r + L) ≠ bump M r := fun h => by
        have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
      obtain ⟨Lc, hCLM⟩ := cl_r_split hlen hq hXu hxb
      refine ⟨seed_ot_qr hM hS I R hz h2 hlen hr hq hXu hCLM
        (hP.qr r L hlen hr hq hXu Lc hCLM) (hO1 ⟨hq, hXu⟩ Lc hCLM) n hn hGlow σ hCN, ?_⟩
      intro q hq' hqr; rw [hq] at hq'; cases hq'; exact absurd rfl hqr
    · obtain ⟨q, Lc, hq, hqr, hCLM⟩ := hc
      obtain ⟨hqo, hro⟩ := seed_ot_qn hM hS I R hz h2 hlen hr hq hqr hCLM
        (hP.qn r L q hlen hr hq hqr Lc hCLM) (hO2 q Lc hq hqr hCLM) n hn hGlow σ hCN hdecr
      refine ⟨hro, fun q' hq' _ => ?_⟩
      rw [hq] at hq'; cases hq'; exact hqo
    · obtain ⟨hq, hux⟩ := hc
      refine ⟨seed_ot_sv hM hS I R hz h2 hlen hr hq hux (hP.sv r L hlen hr hq hux)
        (hO3 ⟨hq, hux⟩) n hn hGlow σ hCN hdecr, ?_⟩
      intro q hq' hqr; rw [hq] at hq'; cases hq'; exact absurd rfl hqr
    · obtain ⟨q, hq, hqr, hncl⟩ := hc
      obtain ⟨hqo, hro⟩ := seed_ot_C hM hS I R hz h2 hlen hr hq hqr hncl
        ((hP.C r L q hlen hr hq hqr hncl).1) (hO4 q hq hqr hncl) n hn hGlow σ hCN hdecr
      refine ⟨hro, fun q' hq' _ => ?_⟩
      rw [hq] at hq'; cases hq'; exact hqo
  refine ⟨fun p hp => by have e := hpr p hp; rw [e] at hp ⊢; exact T2HardA.of_B (h2' r hp) hvr, fun p hp => ?_, fun q hq hqr => ⟨hOTr.2 q hq hqr, hD.2 q hq hqr⟩, h3⟩
  have hp' := hpr p hp
  subst p
  have hot := hOTr.1
  have hdec := hD.1
  refine ⟨?_, hot, hdec⟩
  rcases t2_seed_cases hlen hr with hc | hc | hc | hc
  · obtain ⟨hq, hXu⟩ := hc
    obtain ⟨he2r, h1lt⟩ := par2_facts I.z2 (by omega) hr
    have hxb : col M (r + L) ≠ bump M r := fun h => by
      have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
    obtain ⟨Lc, hCLM⟩ := cl_r_split hlen hq hXu hxb
    exact seedL_qr hM hS I R hz h2 hlen hr hq hXu hCLM
      (hP.qr r L hlen hr hq hXu Lc hCLM) n hn hGlow σ hCN
  · obtain ⟨q, Lc, hq, hqr, hCLM⟩ := hc
    exact seedL_qn hM hS I R hz h2 hlen hr hq hqr hCLM (hP.qn r L q hlen hr hq hqr Lc hCLM)
      n hn hGlow σ hCN (hOTr.2 q hq hqr) (by rw [← cvals_eq_mapC hCN]; exact hdec)
  · obtain ⟨hq, hux⟩ := hc
    exact seedL_sv hM hS I R hz h2 hlen hr hq hux (hP.sv r L hlen hr hq hux)
      n hn hGlow σ hCN (by rw [← cvals_eq_mapC hCN]; exact hdec)
  · obtain ⟨q, hq, hqr, hncl⟩ := hc
    exact seedL_C hM hS I R hz h2 hlen hr hq hqr hncl ((hP.C r L q hlen hr hq hqr hncl).1)
      n hn hGlow σ hCN (hOTr.2 q hq hqr) (by rw [← cvals_eq_mapC hCN]; exact hdec)

/-- **The seed part of `T2HardB` that the step context does not give**: `RClaimU` and the right-end change. -/
def T2SeedRR (M : Mat) (ρ σ : Valn) (p : Nat) : Prop :=
  (∀ U : T → Prop, (∀ u, U u → PathLvA M ρ p u) → RClaimU U ρ σ p) ∧
    (∀ X X', ρ.o p = psi (ρ.v p) X z → σ.o p = psi (ρ.v p) X' z → X' ≠ X → REr X X')

/-- **Residual (t2): the part before `x` in the step context**: at the seeds `RClaimU` and `REr`, and the weak
absorption `AbsWN`. (`VSmallRA`・`PH3cG` come from `Inv3V2`, `RwClosed` from t0's `T0RwRes`.) -/
def T2BelowRV2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    ∀ r L, r + L + 1 = M.length → par M 2 (r + L) = some r → ∀ n, 2 ≤ n →
      (∀ m, 1 ≤ m → m < n → ∀ τ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ → Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) m) τ) →
      ∀ σ, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n) σ →
      (∀ b j, r + L ≤ j → j < (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r)
        (entry M 1 (r + L) - entry M 1 r) n).length → isOT (valB σ b j) = true) →
      (∀ p, T2Seed M r L p → T2SeedRR M ρ σ p) ∧
      AbsWN M (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) (entry M 1 (r + L) - entry M 1 r) n)
        (r + L) ρ σ

/-- **Residual (t2): the standard forms of the seed closed forms** in the step context. -/
def T2SeedOTV2 : Prop :=
  ∀ M ρ rk, StepCtxV2 M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
    T2SeedOTAt M ρ

/-- **`T2BelowXResV2` from the named residuals** (`T0RwRes` for `RwClosed M`, the seed residuals
`T2SeedPResV2`, `T2BelowRV2` and `T2SeedOTV2`). -/
theorem t2BelowXResV2_of (hRw : T0RwRes) (hR : T2BelowRV2) (hP : T2SeedPResV2) (hOT : T2SeedOTV2) :
    T2BelowXResV2 := by
  intro M ρ rk C hM hS I R hz h2
  refine t2BelowXResAt_of_L (fun r L hlen hr n hn hG σ hCN hOTx => ?_) (hP M ρ rk C hz h2) (hOT M ρ rk C hz h2)
    hM hS I R hz h2
  obtain ⟨h1, h3⟩ := hR M ρ rk C hz h2 r L hlen hr n hn hG σ hCN hOTx
  exact ⟨fun p hp => ⟨C.I.vra.toLast, C.I.ph, hRw M ρ rk C, (h1 p hp).1, (h1 p hp).2⟩, h3⟩

end Ytosk
