/-
**3 行・t = 1: groupA の LevLeafInv（標準形で偽）の代わりに BandLast を使う。**

BandLast M: 最後の列 x が t = 1 の葉（r = P_1 x、行 2 = 0、v(r) ≠ 0）なら、行 1 の子を持つどの列 p でも BandS (v(r)) (v(p))
（添字 v(r) の節点の引数は Ω_{v(r)+1} 以上）。lf の欄はどれも帯 [Ω_μ, ψ_μ(Ω_{μ+1})) が空であることしか使わない
（lt_Om_of_bandS）。LevLeafInv が偽になる groupA の t = 2 の族でも BandLast は成り立つ。
-/
import Ytosk.V3ExpT1S
import Ytosk.V3BandS

namespace Ytosk

open T

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **The band condition at the chain level** for every row-1 parent (`t = 1`, the last column a leaf). -/
def BandLast (M : Mat) (ρ : Valn) : Prop :=
  ∀ r, par M 1 (M.length - 1) = some r → entry M 2 (M.length - 1) = 0 → ρ.v r ≠ z →
    ∀ d c, d < M.length → par M 1 d = some c → BandS (ρ.v r) (ρ.v c)

theorem bandS_vOpt_of_last {M : Mat} {ρ : Valn} (hVK : BandLast M ρ)
    {r : Nat} (h1 : par M 1 (M.length - 1) = some r) (hx2 : entry M 2 (M.length - 1) = 0) (hμ : ρ.v r ≠ z)
    {i : Nat} (hi : i < M.length) : BandS (ρ.v r) (vOpt ρ (par M 1 i)) := by
  cases hp : par M 1 i with
  | none => exact bandS_z _
  | some p => exact hVK r h1 hx2 hμ i p hi hp

theorem absDResL_lf_of_leafB {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hVK : BandLast M ρ) : AbsDResL_lf M r L d0 ρ := by
  intro n hn ρP Z hH hCN i hi hv h2 hμ
  obtain ⟨μ, br, vr, seed, k0, hHD, _, _, _, hμv, hro⟩ := hH
  have hlev := holeLev_bumpW_D I hlen h1 hx2 hHD hi hv h2
  rw [hlev] at hμ ⊢
  rw [hμv, chain_level I.cons I.good (by omega) hro] at hμ ⊢
  exact bandS_vOpt_of_last hVK (by rw [show M.length - 1 = r + L by omega]; exact h1)
    (by rw [show M.length - 1 = r + L by omega]; exact hx2) hμ (by omega)

theorem absUWResL_lf_of_leafB {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hVK : BandLast M ρ) : AbsUWResL_lf M r L d0 ρ := by
  intro n hn ρP Z hH hCN i k hi hu hkv hμ
  obtain ⟨μ, br, vr, seed, k0, hHD, _, _, _, hμv, hro⟩ := hH
  have hkx : k < r + L := by
    have hk1 := upg_le hu
    have hk2 := upg_target_e2 hu
    rcases Nat.lt_or_ge k (r + L) with h | h
    · exact h
    · exfalso
      have : k = r + L := by omega
      rw [this, hx2] at hk2; omega
  have hHv := hHD.hole false k hkv hkx
  simp only [valB, cond_false] at hHv
  have hlev : holeLev (last (ρ.v k)) = μ := holeLev_holeT (holeT_last hHv)
  rw [hlev] at hμ ⊢
  rw [hμv, chain_level I.cons I.good (by omega) hro] at hμ ⊢
  exact bandS_vOpt_of_last hVK (by rw [show M.length - 1 = r + L by omega]; exact h1)
    (by rw [show M.length - 1 = r + L by omega]; exact hx2) hμ (by omega)

theorem tploResL_lf_of_leafB {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hVK : BandLast M ρ) (hRes : TPLoLFRes M r L d0 ρ) : TPLoResL_lf M r L d0 ρ := by
  intro n hn ρP Z hH hCN c hc hd s0 y0 h0 hy0 hgood hpat hμ
  have hcM : c < M.length := by omega
  by_cases he1 : entry M 1 c = 0
  · rw [o_sub_eq_v I.cons I.good hcM h0, v_z_of_e1L I.cons hcM he1]; exact bandS_z _
  by_cases hch : ∃ d, d < M.length ∧ par M 1 d = some c
  · obtain ⟨d, hdM, hdc⟩ := hch
    obtain ⟨μ, br, vr, seed, k0, hHD, _, _, _, hμv, hro⟩ := hH
    have hHc := hHD.hole true c hd hc
    simp only [valB, cond_true] at hHc
    rw [h0] at hHc
    have hlev : holeLev y0 = μ := by rw [← holeLev_psi_arg (a := s0) hy0]; exact holeLev_holeT hHc
    rw [hlev] at hμ ⊢
    rw [hμv, chain_level I.cons I.good (by omega) hro] at hμ ⊢
    rw [o_sub_eq_v I.cons I.good hcM h0]
    obtain ⟨hcv, hvs⟩ := leaf_last I.cons I.good (by rw [show M.length - 1 = r + L by omega]; exact h1)
      (by rw [show M.length - 1 = r + L by omega]; exact hx2)
    exact hVK r (by rw [show M.length - 1 = r + L by omega]; exact h1) (by rw [show M.length - 1 = r + L by omega]; exact hx2) hμ d c hdM hdc
  · exact hRes n hn ρP Z hH hCN c hc hd s0 y0 h0 hy0 hgood hpat hμ he1 (fun d hd' h => hch ⟨d, hd', h⟩)

/-- **`AbsDNRes` from `LevLeafInv`** (and the seed-below and level-0 residuals). -/
theorem absDNRes_of_leafB {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hVK : BandLast M ρ) (hS : AbsDNSeedLow M r L d0 ρ) (h0 : AbsDNZero M r L d0 ρ) : AbsDNRes M r L d0 ρ := by
  intro n hn ρP Z hH hCP hCN i hi hv h2
  by_cases hμ : holeLev (bumpW M ρ i) = z
  · exact h0 n hn ρP Z hH hCN i hi hv h2 hμ
  obtain ⟨μ, br, vr, seed, k0, hHD, hZk, h3, h4, hμv, hro⟩ := hH
  have hlev := holeLev_bumpW_D I hlen h1 hx2 hHD hi hv h2
  have hLF : BandS (holeLev (bumpW M ρ i)) (vOpt ρ (par M 1 i)) := by
    have hμ' := hμ
    rw [hlev, hμv, chain_level I.cons I.good (by omega) hro] at hμ' ⊢
    exact bandS_vOpt_of_last hVK (by rw [show M.length - 1 = r + L by omega]; exact h1)
      (by rw [show M.length - 1 = r + L by omega]; exact hx2) hμ' (by omega)
  obtain ⟨k, _, hZe⟩ := hZk i
  cases k with
  | zero =>
    by_cases h : isSucc (Z i) = false ∧ psi (holeLev (bumpW M ρ i)) z z ≤ fsD (Z i) one
    · exact Or.inl ⟨h.1, seedCond_of_bandS hLF h.2⟩
    · exact hS n hn ρP Z ⟨μ, br, vr, seed, k0, hHD, hZk, h3, h4, hμv, hro⟩ hCP hCN i hi hv h2 hμ
        ⟨μ, br, vr, seed, hHD, hZe⟩ h
  | succ k' =>
    have hseedz : seed ≠ z := by obtain ⟨a, X, h⟩ := hHD.seedS; rw [h]; simp
    have hμz : μ ≠ z := by rw [← hlev]; exact hμ
    left
    refine ⟨by rw [hZe]; exact isSucc_psi_z (Or.inl hμz), seedCond_of_bandS hLF ?_⟩
    rw [hlev, hZe]
    exact om_le_gamS_succ hHD.cb hseedz (by simp [one]) k'

/-- **AbsDWLF from LevLeafInv** (any matrix). -/
theorem absDWLF_of_leafB {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) (hVK : BandLast M ρ) :
    AbsDWLF M ρ := by
  intro r μ b h1 _ hx2 hro i hi _ _ _ _ _ hμ
  have hrM : r < M.length := by have := par_lt M 1 _ r h1; omega
  rw [chain_level hC hG hrM hro] at hμ ⊢
  exact bandS_vOpt_of_last hVK h1 hx2 hμ (by omega)

theorem tploWLF_of_leafB {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) (hVK : BandLast M ρ)
    (hRes : TPLoWLFRes M ρ) : TPLoWLF M ρ := by
  intro r μ b h1 hq hx2 hro c hc hd s y ho hyb hspl a hla hns hOa hca hμ
  have hcM : c < M.length := by omega
  have hrM : r < M.length := by have := par_lt M 1 _ r h1; omega
  by_cases he1 : entry M 1 c = 0
  · rw [o_sub_eq_v hC hG hcM ho, v_z_of_e1L hC hcM he1]; exact bandS_z _
  by_cases hch : ∃ d, d < M.length ∧ par M 1 d = some c
  · obtain ⟨d, hdM, hdc⟩ := hch
    rw [chain_level hC hG hrM hro] at hμ ⊢
    rw [o_sub_eq_v hC hG hcM ho]
    obtain ⟨hcv, hvs⟩ := leaf_last hC hG h1 hx2
    exact hVK r h1 hx2 hμ d c hdM hdc
  · exact hRes r μ b h1 hq hx2 hro c hc hd s y ho hyb hspl a hla hns hOa hca hμ he1
      (fun d hd' h => hch ⟨d, hd', h⟩)

theorem bandS_v_plain {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) (hVK : BandLast M ρ)
    {r : Nat} (h1 : par M 1 (M.length - 1) = some r) (hx2 : entry M 2 (M.length - 1) = 0) (hμ : ρ.v r ≠ z)
    {c : Nat} (hc : c < M.length)
    (hsimp : (entry M 2 c = 0 ∧ upg M c = none) ∨
      (entry M 2 c ≠ 0 ∧ ∀ j ∈ children M c, col M j ≠ bump M c)) :
    BandS (ρ.v r) (ρ.v c) := by
  have hp := bandS_vOpt_of_last hVK h1 hx2 hμ hc
  have hvo := vOpt_ot hG hc
  rw [(hC c hc).2]
  unfold vRhs
  by_cases he1 : entry M 1 c = 0
  · rw [if_pos he1]; exact bandS_z _
  rw [if_neg he1]
  rcases hsimp with ⟨h2, hu⟩ | ⟨h2, hb⟩
  · rw [if_pos h2, hu]
    show BandS (ρ.v r) (sf (add (vOpt ρ (par M 1 c)) one))
    rw [sf_ot (isOT_add hvo isOT_one)]
    exact bandS_add hp (bandS_of_levFree (levFree_one hμ))
  · rw [if_neg h2]
    have hz : ∀ t ∈ (children M c).map (bumpTerm M ρ c), t = z := by
      intro t ht
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
      unfold bumpTerm
      rw [if_neg (hb j hj)]
    rw [sumN_cons_zeros isOT_one hz]
    rw [sf_ot (isOT_add hvo (isOT_omega isOT_one))]
    exact bandS_add hp (bandS_of_levFree (levFree_omega_one hμ))

theorem tploLFRes_ofB {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hVK : BandLast M ρ) (hRes : TPLoLFRes2 M r L d0 ρ) : TPLoLFRes M r L d0 ρ := by
  intro n hn ρP Z hH hCN c hc hd s0 y0 h0 hy0 hgood hpat hμ he1 hnc
  by_cases hs : (entry M 2 c = 0 ∧ upg M c = none) ∨
      (entry M 2 c ≠ 0 ∧ ∀ j ∈ children M c, col M j ≠ bump M c)
  · have hcM : c < M.length := by omega
    obtain ⟨μ, br, vr, seed, k0, hHD, _, _, _, hμv, hro⟩ := hH
    have hHc := hHD.hole true c hd hc
    simp only [valB, cond_true] at hHc
    rw [h0] at hHc
    have hlev : holeLev y0 = μ := by rw [← holeLev_psi_arg (a := s0) hy0]; exact holeLev_holeT hHc
    rw [hlev] at hμ ⊢
    rw [hμv, chain_level I.cons I.good (by omega) hro] at hμ ⊢
    rw [o_sub_eq_v I.cons I.good hcM h0]
    exact bandS_v_plain I.cons I.good hVK (by rw [show M.length - 1 = r + L by omega]; exact h1)
      (by rw [show M.length - 1 = r + L by omega]; exact hx2) hμ hcM hs
  · exact hRes n hn ρP Z hH hCN c hc hd s0 y0 h0 hy0 hgood hpat hμ he1 hnc hs

theorem tploWLFRes_ofB {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) (hVK : BandLast M ρ)
    (hRes : TPLoWLFRes2 M ρ) : TPLoWLFRes M ρ := by
  intro r μ b h1 hq hx2 hro c hc hd s y ho hyb hspl a hla hns hOa hca hμ he1 hnc
  by_cases hs : (entry M 2 c = 0 ∧ upg M c = none) ∨
      (entry M 2 c ≠ 0 ∧ ∀ j ∈ children M c, col M j ≠ bump M c)
  · have hcM : c < M.length := by omega
    have hrM : r < M.length := by have := par_lt M 1 _ r h1; omega
    rw [chain_level hC hG hrM hro] at hμ ⊢
    rw [o_sub_eq_v hC hG hcM ho]
    exact bandS_v_plain hC hG hVK h1 hx2 hμ hcM hs
  · exact hRes r μ b h1 hq hx2 hro c hc hd s y ho hyb hspl a hla hns hOa hca hμ he1 hnc hs

/-- **The `t = 1` part of `hExp` for `trio_terminates_main_GP` with `BandLast`** (in place of groupA's
`LevLeafInv`, false on standard matrices). Residuals: `hRT`, `hFrm`, `hResN`, `hNGM` (`NoGapP`), `hLL` (`BandLast`). -/
theorem hExp_t1GP3
    (hRT : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → RestT M rk)
    (hFrm : ∀ N σ, Std N → N ≠ SRO → FrameV N σ → BandLast N σ →
      TPLoWLFRes2 N σ ∧ TPLoW0 N σ ∧ AbsDW0 N σ ∧ TPLoNSeed N σ ∧ TPLoN0 N σ)
    (hResN : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      (DegRes TPLoAt M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ TPLoLFRes2 M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
        TPLoSeedLow M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ TPLoResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      (AbsDSeedLow2 M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsDResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      (AbsUWSeedLow M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsUWResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      (AbsDNSeedLow M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsDNZero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ PassRootRes M r L ρ)
    (hNGM : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → NoGapP M ρ)
    (hLL : ∀ N σ, Std N → N ≠ SRO → Cons N σ → Good3 N σ → BandLast N σ) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 →
      ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∃ ρN rkN, Inv3V (expand M n) ρN rkN ∧ NoGapP (expand M n) ρN := by
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
  obtain ⟨ρN, rkN, V, NG, _, _⟩ :=
    inv3V_N_t1P I R hlen hr hx2 (hRT M ρ rk hM hS I R hz h1t)
      (tploRes_of_L ⟨hRN.1.1, tploResL_lf_of_leafB I hlen hr hx2 hVK (tploLFRes_ofB I hlen hr hx2 hVK hRN.1.2.1),
        tploResL_seed_of (tploResL_lf_of_leafB I hlen hr hx2 hVK (tploLFRes_ofB I hlen hr hx2 hVK hRN.1.2.1)) hRN.1.2.2.1, hRN.1.2.2.2⟩)
      (absDRes_of_L I hlen hr hx2 ⟨absDResL_lf_of_leafB I hlen hr hx2 hVK,
        absDResL_seed_of (absDResL_lf_of_leafB I hlen hr hx2 hVK)
          (absDSeedLow_of_noGap hlen (hNGM M ρ rk hM hS I R) hRN.2.1.1), hRN.2.1.2⟩)
      (absUWRes_of_L hx2 ⟨absUWResL_lf_of_leafB I hlen hr hx2 hVK,
        absUWResL_seed_of (absUWResL_lf_of_leafB I hlen hr hx2 hVK) hRN.2.2.1.1, hRN.2.2.1.2⟩)
      (absDNRes_of_leafB I hlen hr hx2 hVK hRN.2.2.2.1.1 hRN.2.2.2.1.2) hRN.2.2.2.2 (hNGM M ρ rk hM hS I R)
      (fun n' σ rkN hn' hRk hC hG hkd htd had htplo => by
        have hexp' := hexpA n'
        rw [← hexp'] at hRk hC hG hkd htd had htplo ⊢
        have hvk := hLL _ σ (Std.exp n' hM) (ne_SRO_of_rk hRk) hC hG
        have hS' := sInv_std (Std.exp n' hM) (ne_SRO_of_rk hRk)
        obtain ⟨h1, h2, h4, h5, h6⟩ := hFrm _ σ (Std.exp n' hM) (ne_SRO_of_rk hRk) ⟨hS', hC, hG, hkd, htd, had, htplo⟩ hvk
        exact ⟨tplow_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (tploWLF_of_leafB hC hG hvk (tploWLFRes_ofB hC hG hvk h1)) h2,
          absDW_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (absDWLF_of_leafB hC hG hvk) h4,
          tplon_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (tploWLF_of_leafB hC hG hvk (tploWLFRes_ofB hC hG hvk h1)) h5 h6⟩) n hn
  rw [← hexp] at V NG
  exact ⟨ρN, rkN, V, NG⟩

/-- **`t = 1` chain without `NoGapP`** (only `PT1C` is carried). -/
theorem inv3V_N_t1Bd {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 1 (r + L) = some r)
    (hx2 : entry M 2 (r + L) = 0)
    (hRT : RestT M rk)
    (hResL : TPLoRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResD : AbsDRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResU : AbsUWRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hResDN : AbsDNRes M r L (entry M 0 (r + L) - entry M 0 r) ρ)
    (hPR : PassRootRes M r L ρ)
    (hFr : ∀ n σ rkN, 2 ≤ n → Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) rkN →
      Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      BumpKidsDec (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      BumpTermDec (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      AbsD (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      TPLo (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ →
      TPLoW (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ ∧
      AbsDW (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ ∧ TPLoN (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) σ) :
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
  have hcntG := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1' : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcntG
  have hC1' : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1'
  have hAg := agr_base hlen hL0 hA hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 I.cons I.good I.rank
  have hP1 : (fun N σ => PT1C M r ρ N σ) (M.take (r + L)) (drop1 M (r + L) rk) :=
    ⟨V1.fo, hRP1, ⟨V1.kd, V1.td⟩, V1.fc, trig, tp1, tp1w, tplo, ⟨hAg, ad⟩, ⟨hAg, auw⟩, ⟨hAg, adn⟩,
      ⟨vrle_base I R hlen hr, V1.vs⟩⟩
  have hPs : ExpStepT1 (fun N σ => PT1C M r ρ N σ) M r L (entry M 0 (r + L) - entry M 0 r) ρ :=
    expStep_and (expStep_frameOT_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.fo)
      (expStep_and (expStep_rootP_t1 hlen hL0 hd0e I.z2 I.uat I.r12 I.be I.r01 I.e00 hr hx2 I.rootP)
        (expStep_and (expStep_bumpDec_t1 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab hr hx2 hq I.good
            ⟨I.kd, I.td⟩)
          (expStep_and (expStep_frameClosed_t1' I hlen hL0 hd0e hr hx2)
            (expStep_and (expStep_trigOmC I hlen hL0 hd0e hr hx2)
              (expStep_and (expStep_tp1C I hlen hL0 hd0e hr hx2)
                (expStep_and (expStep_tp1WC I hlen hL0 hd0e hr hx2)
                  (expStep_and (expStep_tplo I hlen hL0 hd0e hr hx2 hResL)
                    (expStep_and (expStep_absD I hlen hL0 hd0e hr hx2 hResD)
                      (expStep_and (expStep_absUW I hlen hL0 hd0e hr hx2 hResU)
                        (expStep_and (expStep_absDN I hlen hL0 hd0e hr hx2 hResDN)
                          (expStep_vsmallF2 I hlen hL0 hd0e hr hx2 hPR)))))))))))
  by_cases hqr : q = r
  · subst hqr
    obtain ⟨ρN, rkN, hCN, hRN, hGN, hPN, hot, hlt⟩ :=
      qr_final4 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2 hq
        I.cons I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua I.ad I.tp1w
        I.tplow I.auw I.adw I.tp1 I.trig I.tplon I.adn I.rootS I.rootP (hsd q hr hq) (fun N σ => PT1C M q ρ N σ)
        hP1 hPs n hn
    exact ⟨ρN, rkN, inv3V_of_PT1C hCN hRN hGN hPN (hFr n ρN rkN hn hRN hCN hGN hPN.2.2.1.1 hPN.2.2.1.2
      hPN.2.2.2.2.2.2.2.2.1.2 hPN.2.2.2.2.2.2.2.1),
      hot, hlt⟩
  · obtain ⟨s0, y0, h0⟩ := o_psi_form I.cons (show r < M.length by omega)
    obtain ⟨ρN, rkN, hCN, hRN, hGN, hPN, hot, hlt⟩ :=
      t1_main_final hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2
        (fun h' => hqr (Option.some.inj (hq.symm.trans h'))) I.cons I.good I.rank I.vs I.fc I.fo
        I.tp1 I.tplo I.ad I.au hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua rfl h0 I.rootS I.rootP
        V1.g (fun N σ => PT1C M r ρ N σ)
        hP1 hPs n hn
    exact ⟨ρN, rkN, inv3V_of_PT1C hCN hRN hGN hPN (hFr n ρN rkN hn hRN hCN hGN hPN.2.2.1.1 hPN.2.2.1.2
      hPN.2.2.2.2.2.2.2.2.1.2 hPN.2.2.2.2.2.2.2.1),
      hot, hlt⟩

/-- **The `t = 1` part of `hExp` for `trio_terminates_main_GP` without `NoGapP`** (false on standard matrices,
groupA): the AbsD seed below `Ω_μ` is the residual `AbsDSeedLow` itself; `BandLast` in place of `LevLeafInv`. -/
theorem hExp_t1GP4
    (hRT : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → RestT M rk)
    (hFrm : ∀ N σ, Std N → N ≠ SRO → FrameV N σ → BandLast N σ →
      TPLoWLFRes2 N σ ∧ TPLoW0 N σ ∧ AbsDW0 N σ ∧ TPLoNSeed N σ ∧ TPLoN0 N σ)
    (hResN : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      (DegRes TPLoAt M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ TPLoLFRes2 M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
        TPLoSeedLow M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ TPLoResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      (AbsDSeedLow M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsDResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      (AbsUWSeedLow M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsUWResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      (AbsDNSeedLow M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsDNZero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ PassRootRes M r L ρ)
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
        tploResL_seed_of (tploResL_lf_of_leafB I hlen hr hx2 hVK (tploLFRes_ofB I hlen hr hx2 hVK hRN.1.2.1)) hRN.1.2.2.1, hRN.1.2.2.2⟩)
      (absDRes_of_L I hlen hr hx2 ⟨absDResL_lf_of_leafB I hlen hr hx2 hVK,
        absDResL_seed_of (absDResL_lf_of_leafB I hlen hr hx2 hVK)
          hRN.2.1.1, hRN.2.1.2⟩)
      (absUWRes_of_L hx2 ⟨absUWResL_lf_of_leafB I hlen hr hx2 hVK,
        absUWResL_seed_of (absUWResL_lf_of_leafB I hlen hr hx2 hVK) hRN.2.2.1.1, hRN.2.2.1.2⟩)
      (absDNRes_of_leafB I hlen hr hx2 hVK hRN.2.2.2.1.1 hRN.2.2.2.1.2) hRN.2.2.2.2
      (fun n' σ rkN hn' hRk hC hG hkd htd had htplo => by
        have hexp' := hexpA n'
        rw [← hexp'] at hRk hC hG hkd htd had htplo ⊢
        have hvk := hLL _ σ (Std.exp n' hM) (ne_SRO_of_rk hRk) hC hG
        have hS' := sInv_std (Std.exp n' hM) (ne_SRO_of_rk hRk)
        obtain ⟨h1, h2, h4, h5, h6⟩ := hFrm _ σ (Std.exp n' hM) (ne_SRO_of_rk hRk) ⟨hS', hC, hG, hkd, htd, had, htplo⟩ hvk
        exact ⟨tplow_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (tploWLF_of_leafB hC hG hvk (tploWLFRes_ofB hC hG hvk h1)) h2,
          absDW_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (absDWLF_of_leafB hC hG hvk) h4,
          tplon_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (tploWLF_of_leafB hC hG hvk (tploWLFRes_ofB hC hG hvk h1)) h5 h6⟩) n hn
  rw [← hexp] at V
  exact ⟨ρN, rkN, V⟩

end Ytosk
