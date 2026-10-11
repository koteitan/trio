/-
**3 行・t = 1: TPLoNSeed（M[n] の最後の列の枠、種 < Ω_μ）を帯の条件 TPLoNBand に帰着する。**

種 = M.take x の o(r) が Ω_μ 未満なら L = 1 で 種 = Ω_{ν+1}（ν = v(P_1 r)、seed_shape_gen）。TPLo（添字 ψ_μ(Ω_{μ+1})）から
TPLoN（添字 = 種）へ移すには fsD_transfer で「s の部分項で ψ_μ(Ω_{μ+1}) 未満のものは Ω_{ν+1} 未満」があればよい。
-/
import Ytosk.V3ExpT1SL

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- `seed_shape_qr` from the structural invariants (any matrix with `Cons`・`Good3` and a ranked prefix). -/
theorem seed_shape_gen {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hS : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
    {r L : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hq : par M 0 (r + L) = some r) (hμ : ρ.v r ≠ z)
    {ρ1 : Valn} (hC1 : Cons (M.take (r + L)) ρ1) (hRk1 : Rk (M.take (r + L)) rk)
    (hlow : ¬ psi (ρ.v r) one z ≤ ρ1.o r) :
    L = 1 ∧ ρ1.o r = psi (succ (vOpt ρ (par M 1 r))) z z := by
  have hrx : r < r + L := par_lt M 1 _ r h1
  have hL1 : L = 1 := by
    by_contra hne
    exact hlow (qr_seed_big (x := r + L) hlen hS.r0p hS.z2 hS.sibDec hS.z1c hS.uat hS.uab h1 hC hG hC1 hRk1
      (by omega))
  subst hL1
  refine ⟨rfl, ?_⟩
  have hrM : r < M.length := by omega
  have hrT : r < (M.take (r + 1)).length := by rw [List.length_take]; omega
  have hch : children (M.take (r + 1)) r = [] := by
    rw [children_take, List.eq_nil_iff_forall_not_mem]
    intro c hc
    have h' := List.mem_filter.mp hc
    have hrc := (mem_children h'.1).1
    have := of_decide_eq_true h'.2
    omega
  have he1 : entry M 1 r ≠ 0 := fun h => hμ (v_z_of_e1L hC hrM h)
  have he2 : entry M 2 r = 0 := by
    have hz2 := hS.z2 r
    by_contra hne
    have h21 : entry M 2 r = 1 := by omega
    have hxc : r + 1 ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
    have := hS.z1c r (r + 1) h21 hxc
    have := par1_entry_lt h1
    omega
  have hvp : vOpt ρ1 (par M 1 r) = vOpt ρ (par M 1 r) := by
    cases hp : par M 1 r with
    | none => rfl
    | some g =>
      have hgr : g < r := par_lt M 1 r g hp
      have hpT : par (M.take (r + 1)) 1 (r + 0) = some g := by
        have := par_take M (k := r + 1) 1 r (by omega)
        simpa [this] using hp
      exact (base_v_read hlen hS.r0p hS.z2 hS.sibDec hS.z1c hS.uat hS.uab hC hG hC1 hRk1 (le_of_lt hgr)
        (by omega) (Or.inl hpT)).symm
  have hVot : isOT (vOpt ρ (par M 1 r)) = true := vOpt_ot hG hrM
  have hv1 : ρ1.v r = succ (vOpt ρ (par M 1 r)) := by
    rw [(hC1 r hrT).2]
    unfold vRhs
    rw [entry_take M 1 (by omega), if_neg he1, entry_take M 2 (by omega), if_pos he2,
      upg_last_none (by rw [List.length_take]; omega), par_take M 1 r (by omega), hvp]
    show sf (add (vOpt ρ (par M 1 r)) one) = _
    rw [add_one_eq_succ hVot, sf_ot (isOT_succ hVot)]
  rw [(hC1 r hrT).1]
  unfold oRhs
  rw [hch, hv1]
  show sf (psi (succ (vOpt ρ (par M 1 r))) (sumN []) z) = _
  rw [sf_psi_spArg (isOT_succ hVot) rfl]
  rfl

/-- **Residual of `TPLoNSeed`** (M only): at `L = 1`, the subterms of `s` below `ψ_μ(Ω_{μ+1})` are below the seed
`Ω_{v(P_1 r)+1}`. -/
def TPLoNBand (M : Mat) (ρ : Valn) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ (app b (psi (succ μ) z z)) z → M.length - 1 = r + 1 →
    ∀ c, c < M.length - 1 → DepX M (M.length - 1) true c →
    ∀ s y, ρ.o c = psi s y z → y ≠ app b (psi (succ μ) z z) → (split y (psi (succ s) z z)).2 = z →
    ∀ a, last y = psi a z z → isSucc a = false → OHole a → cof a = .omega → NotNode a → μ ≠ z →
    ∀ u, SubS s u → u < etaOm μ → u < psi (succ (vOpt ρ (par M 1 r))) z z

theorem tploNSeed_of_band {M : Mat} {ρ : Valn} (I : FrameV M ρ) (hB : TPLoNBand M ρ) : TPLoNSeed M ρ := by
  intro ρ' rk' hC' hR' r μ b h1 hq hx2 hro c hc hd hd0 s y ho hyb hspl a hla hns hOa hca hNa hμ hsd
  have hrx : r < M.length - 1 := par_lt M 1 _ r h1
  have hrM : r < M.length := by omega
  have hμr : μ = ρ.v r := chain_level I.cons I.good hrM hro
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  have hlow : ¬ psi (ρ.v r) one z ≤ ρ'.o r := fun h => hsd (by rw [hμr]; exact le_trans (om_le_psi _ _ _) h)
  rw [hL] at hC' hR'
  obtain ⟨hL1, hseed⟩ := seed_shape_gen I.s I.cons I.good hlen (by rw [← hL]; exact h1) (by rw [← hL]; exact hx2)
    (by rw [← hL]; exact hq) (by rw [← hμr]; exact hμ) hC' hR' hlow
  have hH := frame_hole I h1 hq hx2 hro true c hd hc
  simp only [valB, cond_true] at hH
  rw [ho] at hH
  have hyz : y ≠ z := by intro h; rw [h] at hla; simp [last] at hla
  have hlev : holeLev y = μ := by rw [← holeLev_psi_arg (a := s) hyz]; exact holeLev_holeT hH
  have hT := tpl_iff.mp (I.tplo c (by omega) s y ho hspl a hla hns hOa)
  rw [hlev] at hT
  have hband := hB r μ b h1 hq hx2 hro (by omega) c hc hd s y ho hyb hspl a hla hns hOa hca hNa hμ
  apply tpl_iff.mpr
  rw [hseed]
  exact fsD_transfer (subClosed_subS s) (fun u hu h1' _ => hband u hu h1') hOa s (subT_subS (.refl s)) hT hT

/-- **`TPLoSeedLow` holds outright**: a small index is the seed `Ω_{ν+1}`, which is not a good index
(its argument is `0`); that case belongs to `DegRes`. -/
theorem tploSeedLow_holds {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    TPLoSeedLow M r L d0 ρ := by
  intro n hn ρP Z hH hCP hCN c hc hd s0 y0 h0 hy0 hgood hpat hμ hsd hlow
  exfalso
  have hH' := hH
  obtain ⟨μ, br, vr, seed, k0, hHD, _, _, _, hμv, hro⟩ := hH'
  have hHc := hHD.hole true c hd hc
  simp only [valB, cond_true] at hHc
  rw [h0] at hHc
  have hlev : holeLev y0 = μ := by rw [← holeLev_psi_arg (a := s0) hy0]; exact holeLev_holeT hHc
  have hrM : r < M.length := by have := par_lt M 1 _ r h1; omega
  have hμr : μ = ρ.v r := hμv.trans (chain_level I.cons I.good hrM hro)
  rw [hlev, hμr] at hlow hμ
  obtain ⟨_, hZc⟩ := seedLow_shape I hlen h1 hx2 hn hH hCP hμ (by simp [etaOm]) hlow
  obtain ⟨_, μ', X, hζ, hX⟩ := hgood
  rw [hZc] at hζ
  exact hX (T.psi.inj hζ).2.1.symm

/-- **`hExp_t1GP6` with `TPLoNSeed` reduced to `TPLoNBand`.** -/
theorem hExp_t1GP7
    (hRT : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → RestT M rk)
    (hFrm : ∀ N σ, Std N → N ≠ SRO → FrameV N σ → BandLast N σ →
      TPLoWLFRes2 N σ ∧ TPLoW0 N σ ∧ AbsDW0 N σ ∧ TPLoNBand N σ ∧ TPLoN0 N σ)
    (hResN : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      (DegRes TPLoAt M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ TPLoLFRes2 M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
        (TPLoGapRes M r L ρ ∧ TPLoSeedLow0 M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ TPLoResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      ((AbsDGapRes M r L ρ ∧ AbsDSeedLow0 M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ AbsDResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      ((AbsUWGapRes M r L ρ ∧ AbsUWSeedLow0 M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ AbsUWResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      ((AbsDNGapRes M r L ρ ∧ AbsDNSeedLow0 M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ AbsDNZero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ PassRootRes M r L ρ)
    (hLL : ∀ N σ, Std N → N ≠ SRO → Cons N σ → Good3 N σ → BandLast N σ) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 →
      ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hz h1t n hn _ _
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
  have hexpA := fun n' => expand_eq_gexp_t1 M n' hlen2 hzT (by rw [h1t]; exact hr) h1t
  have hrx : r < M.length - 1 := par_lt M 1 _ r hr
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  rw [hL] at hexp hexpA hr hx2
  simp only [Nat.add_sub_cancel_left] at hexp hexpA
  have hlen : r + L + 1 = M.length := by omega
  have hVK := hLL M ρ hM hS I.cons I.good
  have hRN := hResN M ρ rk hM hS I R r L hlen hr hx2
  obtain ⟨ρN, rkN, V, _, _⟩ :=
    inv3V_N_t1Bd I R hlen hr hx2 (hRT M ρ rk hM hS I R hz h1t)
      (tploRes_of_L ⟨hRN.1.1, tploResL_lf_of_leafB I hlen hr hx2 hVK (tploLFRes_ofB I hlen hr hx2 hVK hRN.1.2.1),
        tploResL_seed_of (tploResL_lf_of_leafB I hlen hr hx2 hVK (tploLFRes_ofB I hlen hr hx2 hVK hRN.1.2.1)) (tploSeedLow_of_gap I hlen hr hx2 hRN.1.2.2.1.1 hRN.1.2.2.1.2), hRN.1.2.2.2⟩)
      (absDRes_of_L I hlen hr hx2 ⟨absDResL_lf_of_leafB I hlen hr hx2 hVK,
        absDResL_seed_of (absDResL_lf_of_leafB I hlen hr hx2 hVK)
          (absDSeedLow_of_gap I hlen hr hx2 hRN.2.1.1.1 hRN.2.1.1.2), hRN.2.1.2⟩)
      (absUWRes_of_L hx2 ⟨absUWResL_lf_of_leafB I hlen hr hx2 hVK,
        absUWResL_seed_of (absUWResL_lf_of_leafB I hlen hr hx2 hVK) (absUWSeedLow_of_gap I hlen hr hx2 hRN.2.2.1.1.1 hRN.2.2.1.1.2), hRN.2.2.1.2⟩)
      (absDNRes_of_leafB I hlen hr hx2 hVK (absDNSeedLow_of_gap I hlen hr hx2 hRN.2.2.2.1.1.1 hRN.2.2.2.1.1.2) hRN.2.2.2.1.2) hRN.2.2.2.2
      (fun n' σ rkN hn' hRk hC hG hkd htd had htplo => by
        have hexp' := hexpA n'
        rw [← hexp'] at hRk hC hG hkd htd had htplo ⊢
        have hvk := hLL _ σ (Std.exp n' hM) (ne_SRO_of_rk hRk) hC hG
        have hS' := sInv_std (Std.exp n' hM) (ne_SRO_of_rk hRk)
        obtain ⟨h1, h2, h4, h5, h6⟩ := hFrm _ σ (Std.exp n' hM) (ne_SRO_of_rk hRk) ⟨hS', hC, hG, hkd, htd, had, htplo⟩ hvk
        exact ⟨tplow_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (tploWLF_of_leafB hC hG hvk (tploWLFRes_ofB hC hG hvk h1)) h2,
          absDW_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (absDWLF_of_leafB hC hG hvk) h4,
          tplon_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (tploWLF_of_leafB hC hG hvk (tploWLFRes_ofB hC hG hvk h1)) (tploNSeed_of_band ⟨hS', hC, hG, hkd, htd, had, htplo⟩ h5) h6⟩) n hn
  rw [← hexp] at V
  exact ⟨ρN, rkN, V⟩

/-- **`hExp_t1GP7` without the TPLo seed residuals** (`tploSeedLow_holds`). -/
theorem hExp_t1GP8
    (hRT : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → RestT M rk)
    (hFrm : ∀ N σ, Std N → N ≠ SRO → FrameV N σ → BandLast N σ →
      TPLoWLFRes2 N σ ∧ TPLoW0 N σ ∧ AbsDW0 N σ ∧ TPLoNBand N σ ∧ TPLoN0 N σ)
    (hResN : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      (DegRes TPLoAt M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ TPLoLFRes2 M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
        TPLoResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      ((AbsDGapRes M r L ρ ∧ AbsDSeedLow0 M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ AbsDResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      ((AbsUWGapRes M r L ρ ∧ AbsUWSeedLow0 M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ AbsUWResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      ((AbsDNGapRes M r L ρ ∧ AbsDNSeedLow0 M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ AbsDNZero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ PassRootRes M r L ρ)
    (hLL : ∀ N σ, Std N → N ≠ SRO → Cons N σ → Good3 N σ → BandLast N σ) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 →
      ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hz h1t n hn _ _
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
  have hexpA := fun n' => expand_eq_gexp_t1 M n' hlen2 hzT (by rw [h1t]; exact hr) h1t
  have hrx : r < M.length - 1 := par_lt M 1 _ r hr
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  rw [hL] at hexp hexpA hr hx2
  simp only [Nat.add_sub_cancel_left] at hexp hexpA
  have hlen : r + L + 1 = M.length := by omega
  have hVK := hLL M ρ hM hS I.cons I.good
  have hRN := hResN M ρ rk hM hS I R r L hlen hr hx2
  obtain ⟨ρN, rkN, V, _, _⟩ :=
    inv3V_N_t1Bd I R hlen hr hx2 (hRT M ρ rk hM hS I R hz h1t)
      (tploRes_of_L ⟨hRN.1.1, tploResL_lf_of_leafB I hlen hr hx2 hVK (tploLFRes_ofB I hlen hr hx2 hVK hRN.1.2.1),
        tploResL_seed_of (tploResL_lf_of_leafB I hlen hr hx2 hVK (tploLFRes_ofB I hlen hr hx2 hVK hRN.1.2.1)) (tploSeedLow_holds I hlen hr hx2), hRN.1.2.2⟩)
      (absDRes_of_L I hlen hr hx2 ⟨absDResL_lf_of_leafB I hlen hr hx2 hVK,
        absDResL_seed_of (absDResL_lf_of_leafB I hlen hr hx2 hVK)
          (absDSeedLow_of_gap I hlen hr hx2 hRN.2.1.1.1 hRN.2.1.1.2), hRN.2.1.2⟩)
      (absUWRes_of_L hx2 ⟨absUWResL_lf_of_leafB I hlen hr hx2 hVK,
        absUWResL_seed_of (absUWResL_lf_of_leafB I hlen hr hx2 hVK) (absUWSeedLow_of_gap I hlen hr hx2 hRN.2.2.1.1.1 hRN.2.2.1.1.2), hRN.2.2.1.2⟩)
      (absDNRes_of_leafB I hlen hr hx2 hVK (absDNSeedLow_of_gap I hlen hr hx2 hRN.2.2.2.1.1.1 hRN.2.2.2.1.1.2) hRN.2.2.2.1.2) hRN.2.2.2.2
      (fun n' σ rkN hn' hRk hC hG hkd htd had htplo => by
        have hexp' := hexpA n'
        rw [← hexp'] at hRk hC hG hkd htd had htplo ⊢
        have hvk := hLL _ σ (Std.exp n' hM) (ne_SRO_of_rk hRk) hC hG
        have hS' := sInv_std (Std.exp n' hM) (ne_SRO_of_rk hRk)
        obtain ⟨h1, h2, h4, h5, h6⟩ := hFrm _ σ (Std.exp n' hM) (ne_SRO_of_rk hRk) ⟨hS', hC, hG, hkd, htd, had, htplo⟩ hvk
        exact ⟨tplow_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (tploWLF_of_leafB hC hG hvk (tploWLFRes_ofB hC hG hvk h1)) h2,
          absDW_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (absDWLF_of_leafB hC hG hvk) h4,
          tplon_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (tploWLF_of_leafB hC hG hvk (tploWLFRes_ofB hC hG hvk h1)) (tploNSeed_of_band ⟨hS', hC, hG, hkd, htd, had, htplo⟩ h5) h6⟩) n hn
  rw [← hexp] at V
  exact ⟨ρN, rkN, V⟩

/-- **The `t = 1` part of `hExp` with the residuals in their original form** (the seed conditions at the actual
chain index; `M[n]`'s last-column frame fields). No `BandLast`/`LevLeafInv`/`NoGapP`: the strong M-only splits of the
`lf` parts are false on ext1x・T2Ext, the original forms hold on the checked counterexamples. -/
theorem hExp_t1O
    (hRT : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → RestT M rk)
    (hFrm : ∀ N σ, Std N → N ≠ SRO → FrameV N σ → TPLoW N σ ∧ AbsDW N σ ∧ TPLoN N σ)
    (hResN : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      TPLoRes M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsDRes M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
      AbsUWRes M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsDNRes M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
      PassRootRes M r L ρ) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 →
      ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN := by
  intro M ρ rk hM hS hE I R hz h1t n hn _ _
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
  have hexpA := fun n' => expand_eq_gexp_t1 M n' hlen2 hzT (by rw [h1t]; exact hr) h1t
  have hrx : r < M.length - 1 := par_lt M 1 _ r hr
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  rw [hL] at hexp hexpA hr hx2
  simp only [Nat.add_sub_cancel_left] at hexp hexpA
  have hlen : r + L + 1 = M.length := by omega
  have hRN := hResN M ρ rk hM hS I R r L hlen hr hx2
  obtain ⟨ρN, rkN, V, _, _⟩ :=
    inv3V_N_t1Bd I R hlen hr hx2 (hRT M ρ rk hM hS I R hz h1t)
      hRN.1 hRN.2.1 hRN.2.2.1 hRN.2.2.2.1 hRN.2.2.2.2
      (fun n' σ rkN hn' hRk hC hG hkd htd had htplo => by
        have hexp' := hexpA n'
        rw [← hexp'] at hRk hC hG hkd htd had htplo ⊢
        have hS' := sInv_std (Std.exp n' hM) (ne_SRO_of_rk hRk)
        exact hFrm _ σ (Std.exp n' hM) (ne_SRO_of_rk hRk) ⟨hS', hC, hG, hkd, htd, had, htplo⟩) n hn
  rw [← hexp] at V
  exact ⟨ρN, rkN, V⟩

end Ytosk
