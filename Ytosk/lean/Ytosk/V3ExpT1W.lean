/-
**3 行・t = 1: TPLoLFRes・TPLoWLFRes を bump の子を持つ列だけに狭める。**

行 1 ≠ 0 で行 1 の子を持たない列 c の v は v(c) = v(P_1 c) ⊕ t（t は 1、ω、上げ先の値の最後、bump の項のどれか）。
P_1 c は行 1 の子 c を持つので、groupA の LevLeafInv から LevFree (v(r)) (v(P_1 c))（levFree_vOpt_of_leaf）。
t = 1（行 2 = 0、上げなし）と t = ω（行 2 ≠ 0、bump の子なし）は添字 0 の節点しか持たないので LevFree。
実測（C′ 195711 行列）: TPLoLFRes の場面の c はいつも行 2 = 1 で、bump の子がないのは 13920/14956。
残りは bump の子を持つ c（と上げのある行 2 = 0、実測 0 件）だけ（TPLoLFRes2・TPLoWLFRes2）。
-/
import Ytosk.V3ExpT1V

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem levFree_add {μ A X : T} (hA : LevFree μ A) (hX : LevFree μ X) : LevFree μ (add A X) := by
  obtain ⟨P, hP, hs⟩ := add_eq_app_prefix A X
  rw [hP]
  intro a b c h
  rcases subT_app_cases P X _ h with h | ⟨a', b', R, hq, hw⟩
  · exact hX a b c h
  · obtain ⟨c1, hc1⟩ := subT_of_summand (hs _ hq)
    rcases hw with he | hw | hw
    · cases he; exact hA a b c1 hc1
    · exact hA a b c (SubT.trans hw (SubT.sub (.refl a') |>.trans hc1))
    · exact hA a b c (SubT.trans hw (SubT.arg (.refl b') |>.trans hc1))

theorem levFree_psi {μ a b c : T} (ha : a ≠ μ) (h1 : LevFree μ a) (h2 : LevFree μ b) (h3 : LevFree μ c) :
    LevFree μ (psi a b c) := by
  intro a' b' c' h
  cases h with
  | refl => exact ha
  | sub h => exact h1 a' b' c' h
  | arg h => exact h2 a' b' c' h
  | rest h => exact h3 a' b' c' h

theorem levFree_one {μ : T} (hμ : μ ≠ z) : LevFree μ one :=
  levFree_psi (Ne.symm hμ) (levFree_z μ) (levFree_z μ) (levFree_z μ)

theorem levFree_omega_one {μ : T} (hμ : μ ≠ z) : LevFree μ (omega one) := by
  rw [omega_small one_lt_E0]
  exact levFree_psi (Ne.symm hμ) (levFree_z μ) (levFree_one hμ) (levFree_z μ)

/-- **The plain columns**: `v(c) = v(P_1 c) + 1` or `v(P_1 c) + ω` keeps `LevFree (v(r))` from `LevLeafInv`. -/
theorem levFree_v_plain {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) (hVK : LevLeafInv M ρ)
    {r : Nat} (h1 : par M 1 (M.length - 1) = some r) (hx2 : entry M 2 (M.length - 1) = 0) (hμ : ρ.v r ≠ z)
    {c : Nat} (hc : c < M.length)
    (hsimp : (entry M 2 c = 0 ∧ upg M c = none) ∨
      (entry M 2 c ≠ 0 ∧ ∀ j ∈ children M c, col M j ≠ bump M c)) :
    LevFree (ρ.v r) (ρ.v c) := by
  have hp := levFree_vOpt_of_leaf hC hG hVK h1 hx2 hμ hc
  have hvo := vOpt_ot hG hc
  rw [(hC c hc).2]
  unfold vRhs
  by_cases he1 : entry M 1 c = 0
  · rw [if_pos he1]; exact levFree_z _
  rw [if_neg he1]
  rcases hsimp with ⟨h2, hu⟩ | ⟨h2, hb⟩
  · rw [if_pos h2, hu]
    show LevFree (ρ.v r) (sf (add (vOpt ρ (par M 1 c)) one))
    rw [sf_ot (isOT_add hvo isOT_one)]
    exact levFree_add hp (levFree_one hμ)
  · rw [if_neg h2]
    have hz : ∀ t ∈ (children M c).map (bumpTerm M ρ c), t = z := by
      intro t ht
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
      unfold bumpTerm
      rw [if_neg (hb j hj)]
    rw [sumN_cons_zeros isOT_one hz]
    rw [sf_ot (isOT_add hvo (isOT_omega isOT_one))]
    exact levFree_add hp (levFree_omega_one hμ)

/-- **Residual of `TPLoLFRes`**: only the columns with a bump child (or row 2 zero with an upgrade). -/
def TPLoLFRes2 (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
  Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
  ∀ c, c < r + L → DepX M (r + L) true c → ∀ s0 y0, ρ.o c = psi s0 y0 z → y0 ≠ z →
  GoodIdx (Z c) → TPLoPatN s0 y0 (Z c) → holeLev y0 ≠ z →
  entry M 1 c ≠ 0 → (∀ d, d < M.length → par M 1 d ≠ some c) →
  ¬ ((entry M 2 c = 0 ∧ upg M c = none) ∨ (entry M 2 c ≠ 0 ∧ ∀ j ∈ children M c, col M j ≠ bump M c)) →
  BandS (holeLev y0) s0

theorem tploLFRes_of {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hVK : LevLeafInv M ρ) (hRes : TPLoLFRes2 M r L d0 ρ) : TPLoLFRes M r L d0 ρ := by
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
    exact bandS_of_levFree <| levFree_v_plain I.cons I.good hVK (by rw [show M.length - 1 = r + L by omega]; exact h1)
      (by rw [show M.length - 1 = r + L by omega]; exact hx2) hμ hcM hs
  · exact hRes n hn ρP Z hH hCN c hc hd s0 y0 h0 hy0 hgood hpat hμ he1 hnc hs

/-- **Residual of `TPLoWLFRes`**: only the columns with a bump child (or row 2 zero with an upgrade). -/
def TPLoWLFRes2 (M : Mat) (ρ : Valn) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ (app b (psi (succ μ) z z)) z →
    ∀ c, c < M.length - 1 → DepX M (M.length - 1) true c → ∀ s y, ρ.o c = psi s y z →
    y ≠ app b (psi (succ μ) z z) → (split y (psi (succ s) z z)).2 = z →
    ∀ a, last y = psi a z z → isSucc a = false → OHole a → cof a = .omega → μ ≠ z →
    entry M 1 c ≠ 0 → (∀ d, d < M.length → par M 1 d ≠ some c) →
    ¬ ((entry M 2 c = 0 ∧ upg M c = none) ∨ (entry M 2 c ≠ 0 ∧ ∀ j ∈ children M c, col M j ≠ bump M c)) →
    BandS μ s

theorem tploWLFRes_of {M : Mat} {ρ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ) (hVK : LevLeafInv M ρ)
    (hRes : TPLoWLFRes2 M ρ) : TPLoWLFRes M ρ := by
  intro r μ b h1 hq hx2 hro c hc hd s y ho hyb hspl a hla hns hOa hca hμ he1 hnc
  by_cases hs : (entry M 2 c = 0 ∧ upg M c = none) ∨
      (entry M 2 c ≠ 0 ∧ ∀ j ∈ children M c, col M j ≠ bump M c)
  · have hcM : c < M.length := by omega
    have hrM : r < M.length := by have := par_lt M 1 _ r h1; omega
    rw [chain_level hC hG hrM hro] at hμ ⊢
    rw [o_sub_eq_v hC hG hcM ho]
    exact bandS_of_levFree <| levFree_v_plain hC hG hVK h1 hx2 hμ hcM hs
  · exact hRes r μ b h1 hq hx2 hro c hc hd s y ho hyb hspl a hla hns hOa hca hμ he1 hnc hs

/-- **`hExp_t1GP` with `TPLoLFRes2`・`TPLoWLFRes2`** (the `LevFree` residuals only at columns with a bump child). -/
theorem hExp_t1GP2
    (hRT : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → RestT M rk)
    (hFrm : ∀ N σ, Std N → N ≠ SRO → FrameV N σ → LevLeafInv N σ →
      TPLoWLFRes2 N σ ∧ TPLoW0 N σ ∧ AbsDW0 N σ ∧ TPLoNSeed N σ ∧ TPLoN0 N σ)
    (hResN : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      (DegRes TPLoAt M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ TPLoLFRes2 M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
        TPLoSeedLow M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ TPLoResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      (AbsDSeedLow2 M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsDResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      (AbsUWSeedLow M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsUWResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      (AbsDNSeedLow M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ AbsDNZero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ PassRootRes M r L ρ)
    (hNGM : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → NoGapP M ρ)
    (hLL : ∀ N σ, Std N → N ≠ SRO → Cons N σ → Good3 N σ → LevLeafInv N σ) :
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
      (tploRes_of_L ⟨hRN.1.1, tploResL_lf_of_leaf I hlen hr hx2 hVK (tploLFRes_of I hlen hr hx2 hVK hRN.1.2.1),
        tploResL_seed_of (tploResL_lf_of_leaf I hlen hr hx2 hVK (tploLFRes_of I hlen hr hx2 hVK hRN.1.2.1)) hRN.1.2.2.1, hRN.1.2.2.2⟩)
      (absDRes_of_L I hlen hr hx2 ⟨absDResL_lf_of_leaf I hlen hr hx2 hVK,
        absDResL_seed_of (absDResL_lf_of_leaf I hlen hr hx2 hVK)
          (absDSeedLow_of_noGap hlen (hNGM M ρ rk hM hS I R) hRN.2.1.1), hRN.2.1.2⟩)
      (absUWRes_of_L hx2 ⟨absUWResL_lf_of_leaf I hlen hr hx2 hVK,
        absUWResL_seed_of (absUWResL_lf_of_leaf I hlen hr hx2 hVK) hRN.2.2.1.1, hRN.2.2.1.2⟩)
      (absDNRes_of_leaf I hlen hr hx2 hVK hRN.2.2.2.1.1 hRN.2.2.2.1.2) hRN.2.2.2.2 (hNGM M ρ rk hM hS I R)
      (fun n' σ rkN hn' hRk hC hG hkd htd had htplo => by
        have hexp' := hexpA n'
        rw [← hexp'] at hRk hC hG hkd htd had htplo ⊢
        have hvk := hLL _ σ (Std.exp n' hM) (ne_SRO_of_rk hRk) hC hG
        have hS' := sInv_std (Std.exp n' hM) (ne_SRO_of_rk hRk)
        obtain ⟨h1, h2, h4, h5, h6⟩ := hFrm _ σ (Std.exp n' hM) (ne_SRO_of_rk hRk) ⟨hS', hC, hG, hkd, htd, had, htplo⟩ hvk
        exact ⟨tplow_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (tploWLF_of_leaf hC hG hvk (tploWLFRes_of hC hG hvk h1)) h2,
          absDW_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (absDWLF_of_leaf hC hG hvk) h4,
          tplon_of_lf ⟨hS', hC, hG, hkd, htd, had, htplo⟩ (tploWLF_of_leaf hC hG hvk (tploWLFRes_of hC hG hvk h1)) h5 h6⟩) n hn
  rw [← hexp] at V NG
  exact ⟨ρN, rkN, V, NG⟩

end Ytosk
