/-
**3 行・t = 1: 種 < Ω_μ の欄（TPLoSeedLow・AbsDSeedLow）を、L = 1 の行列の隙間の条件 GapAt に帰着する。**

種が小さい（ψ_{v(r)}(1) 未満、または fsD 後に Ω_μ 未満）なら、添字は種そのもの（鎖の 1 項目以降は Ω_μ 以上）で n = 2、
L = 1、種 = Ω_{ν+1}（ν = v(P_1 r)、seed_shape_qr）。このとき fsD(Ω_{ν+1}, ψ_ν(Ω_{ν+1})) = ψ_ν(Ω_{ν+1}) なので、
種の条件は「段 ν の隙間 [ψ_ν(Ω_{ν+1}), Ω_{ν+1}) に（ψ_μ(Ω_{μ+1}) 未満の）部分項がない」こと（GapAt ν μ V）。
残りは M だけの性質 TPLoGapRes・AbsDGapRes（L = 1 の行列の D の列で GapAt）。ν = 0 は段 0（groupA）。
-/
import Ytosk.V3ExpT1Bd

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The gap at `ν`** (below `ψ_μ(Ω_{μ+1})`). -/
def GapAt (ν μ V : T) : Prop := ∀ u, SubS V u → u < psi (succ ν) z z → u < etaOm μ → u < etaOm ν

/-- `seed_shape_qr` without the hypothesis `q = r` (it follows from `L = 1`). -/
theorem seed_shape {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hμ : ρ.v r ≠ z) {ρ1 : Valn} (hC1 : Cons (M.take (r + L)) ρ1)
    (hlow : ¬ psi (ρ.v r) one z ≤ ρ1.o r) :
    L = 1 ∧ ρ1.o r = psi (succ (vOpt ρ (par M 1 r))) z z := by
  have hcntG := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcntG
  have hL1 : L = 1 := by
    by_contra hne
    have hrx : r < r + L := par_lt M 1 _ r h1
    exact hlow (qr_seed_big (x := r + L) hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 I.cons I.good hC1 hRk1
      (by omega))
  subst hL1
  have hq : par M 0 (r + 1) = some r := child_succ (anc0_of_par M 1 r (r + 1) h1) (by omega)
  exact seed_shape_qr I hlen h1 hx2 hq hμ hC1 hlow

/-- **A small index is the seed `Ω_{v(P_1 r)+1}`, with `L = 1`.** -/
theorem seedLow_shape {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hn : 2 ≤ n) {ρP : Valn} {Z : Nat → T} (hH : HoleInfo M r L n ρ ρP Z)
    (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP) (hμz : ρ.v r ≠ z) {j : Nat} {θ : T} (hθ : θ ≠ z)
    (hlow : ¬ (isSucc (Z j) = false ∧ psi (ρ.v r) z z ≤ fsD (Z j) θ)) :
    L = 1 ∧ Z j = psi (succ (vOpt ρ (par M 1 r))) z z := by
  obtain ⟨μ, br, vr, seed, k0, hHD, hZk, hP, hk0, hμv, hro⟩ := hH
  have hrM : r < M.length := by have := par_lt M 1 _ r h1; omega
  have hvr : vr = ρ.v r := chain_level I.cons I.good hrM hro
  have hμr : μ = ρ.v r := hμv.trans hvr
  have hseedz : seed ≠ z := by obtain ⟨a, X, h⟩ := hHD.seedS; rw [h]; simp
  obtain ⟨k, hkk, hZe⟩ := hZk j
  cases k with
  | succ k' =>
    exfalso
    apply hlow
    rw [hZe, ← hμr]
    refine ⟨?_, om_le_gamS_succ hHD.cb hseedz hθ k'⟩
    show isSucc (psi μ (fs br (gamS μ br seed k')) z) = false
    exact isSucc_psi_z (Or.inl (by rw [hμr]; exact hμz))
  | zero =>
    have hk00 : k0 = 0 := by omega
    have hn2 : n = 2 := by omega
    subst hn2
    rw [hk00] at hP
    have hPs : ρP.o r = seed := hP
    have hC1 : Cons (M.take (r + L)) ρP := by
      have h21 : (2 : Nat) - 1 = 1 := rfl
      rw [h21, gexp_one_gen hlen] at hCP
      exact hCP
    have hlow' : ¬ psi (ρ.v r) one z ≤ ρP.o r := by
      intro hle
      rw [hPs] at hle
      obtain ⟨a, X, hsX⟩ := hHD.seedS
      have hlt := (hHD.S vr (lt_irrefl' vr) hHD.rot).lt_om
      rw [hsX, hμr] at hlt
      rw [hsX] at hle
      have ha : a = ρ.v r := sub_eq_of_band (le_trans (om_le_psi _ _ _) hle) hlt
      subst ha
      have hX : X ≠ z := by
        intro hX0
        rw [hX0] at hle
        exact absurd hle (not_le.mpr (T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨rfl, T.z_lt_psi _ _ _⟩))))
      apply hlow
      rw [hZe]
      show isSucc seed = false ∧ psi (ρ.v r) z z ≤ fsD seed θ
      rw [hsX]
      exact ⟨isSucc_psi_z (Or.inr hX), om_le_fsD_psi hX hθ⟩
    obtain ⟨hL1, hseed⟩ := seed_shape I hlen h1 hx2 hμz hC1 hlow'
    refine ⟨hL1, ?_⟩
    rw [hZe]
    show seed = _
    rw [← hPs, hseed]

/-- **The seed condition at the seed `Ω_{ν+1}`** from the gap. -/
theorem seedCond_of_gap {ν μ V : T} (h : GapAt ν μ V) :
    SeedCond V (psi (succ ν) z z) (etaOm μ) (etaOm (holeLev (psi (succ ν) z z))) := by
  intro u hu h1 h2
  rw [holeLev_Om_succ, fsD_leaf (isSucc_succ ν) (succ_ne_z ν)]
  exact h u hu h1 h2

/-- **Residual (TPLo, the seed below `Ω_μ`)**: in a `t = 1` matrix with `L = 1`, the subscript of every `o` call of
`D` with a hole has no subterm in the gap at `ν = v(P_1 r)`. -/
def TPLoGapRes (M : Mat) (r L : Nat) (ρ : Valn) : Prop :=
  L = 1 → vOpt ρ (par M 1 r) ≠ z → ∀ c, c < r + L → DepX M (r + L) true c → ∀ s0 y0, ρ.o c = psi s0 y0 z → y0 ≠ z → holeLev y0 ≠ z →
    GapAt (vOpt ρ (par M 1 r)) (ρ.v r) s0

/-- **Residual (TPLo, the seed `Ω_1`, level `0`)**: `TPLoSeedLow` when `v(P_1 r) = 0`. -/
def TPLoSeedLow0 (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
  Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
  Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
  ∀ c, c < r + L → DepX M (r + L) true c → ∀ s0 y0, ρ.o c = psi s0 y0 z → y0 ≠ z →
  GoodIdx (Z c) → TPLoPatN s0 y0 (Z c) → holeLev y0 ≠ z →
  (∃ μ br vr seed, HoleData M (r + L) ρ μ br vr seed ∧ Z c = seed) →
  ¬ (isSucc (Z c) = false ∧ psi (holeLev y0) z z ≤ fsD (Z c) (etaOm (holeLev (Z c)))) →
  vOpt ρ (par M 1 r) = z → SeedCond s0 (Z c) (etaOm (holeLev y0)) (etaOm (holeLev (Z c)))

/-- **Residual (AbsD, the seed below `Ω_μ`)**: the same for `v(P_1 i)` at the bump columns of `D`. -/
def AbsDGapRes (M : Mat) (r L : Nat) (ρ : Valn) : Prop :=
  L = 1 → vOpt ρ (par M 1 r) ≠ z → ∀ i, i < r + L → DepX M (r + L) false i → entry M 2 i ≠ 0 → holeLev (bumpW M ρ i) ≠ z →
    GapAt (vOpt ρ (par M 1 r)) (ρ.v r) (vOpt ρ (par M 1 i))

/-- **Residual (AbsD, the seed `Ω_1`, level `0`)**: `AbsDSeedLow` when `v(P_1 r) = 0`. -/
def AbsDSeedLow0 (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
  Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
  Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
  ∀ i, i < r + L → DepX M (r + L) false i → entry M 2 i ≠ 0 → holeLev (bumpW M ρ i) ≠ z →
  (∃ μ br vr seed, HoleData M (r + L) ρ μ br vr seed ∧ Z i = seed) →
  ¬ (isSucc (Z i) = false ∧ psi (holeLev (bumpW M ρ i)) z z ≤ fsD (Z i) (etaOm (holeLev (Z i)))) →
  vOpt ρ (par M 1 r) = z →
  (isSucc (Z i) = false ∧
    SeedCond (vOpt ρ (par M 1 i)) (Z i) (etaOm (holeLev (bumpW M ρ i))) (etaOm (holeLev (Z i)))) ∨
  (OHole (fsD (bumpW M ρ i) (Z i)) → ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < fsD (bumpW M ρ i) (Z i) →
    q < fsD (fsD (bumpW M ρ i) (Z i)) (etaOm (holeLev (fsD (bumpW M ρ i) (Z i)))))

theorem tploSeedLow_of_gap {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hR : TPLoGapRes M r L ρ) (hR0 : TPLoSeedLow0 M r L d0 ρ) : TPLoSeedLow M r L d0 ρ := by
  intro n hn ρP Z hH hCP hCN c hc hd s0 y0 h0 hy0 hgood hpat hμ hsd hlow
  by_cases hν : vOpt ρ (par M 1 r) = z
  · exact hR0 n hn ρP Z hH hCP hCN c hc hd s0 y0 h0 hy0 hgood hpat hμ hsd hlow hν
  have hH' := hH
  obtain ⟨μ, br, vr, seed, k0, hHD, _, _, _, hμv, hro⟩ := hH'
  have hHc := hHD.hole true c hd hc
  simp only [valB, cond_true] at hHc
  rw [h0] at hHc
  have hlev : holeLev y0 = μ := by rw [← holeLev_psi_arg (a := s0) hy0]; exact holeLev_holeT hHc
  have hrM : r < M.length := by have := par_lt M 1 _ r h1; omega
  have hμr : μ = ρ.v r := hμv.trans (chain_level I.cons I.good hrM hro)
  rw [hlev, hμr] at hlow hμ ⊢
  obtain ⟨hL1, hZc⟩ := seedLow_shape I hlen h1 hx2 hn hH hCP hμ (by simp [etaOm]) hlow
  rw [hZc]
  exact seedCond_of_gap (hR hL1 hν c hc hd s0 y0 h0 hy0 (by rw [hlev, hμr]; exact hμ))

theorem absDSeedLow_of_gap {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hR : AbsDGapRes M r L ρ) (hR0 : AbsDSeedLow0 M r L d0 ρ) : AbsDSeedLow M r L d0 ρ := by
  intro n hn ρP Z hH hCP hCN i hi hv h2 hμ hsd hlow
  by_cases hν : vOpt ρ (par M 1 r) = z
  · exact hR0 n hn ρP Z hH hCP hCN i hi hv h2 hμ hsd hlow hν
  have hH' := hH
  obtain ⟨μ, br, vr, seed, k0, hHD, _, _, _, hμv, hro⟩ := hH'
  have hlev := holeLev_bumpW_D I hlen h1 hx2 hHD hi hv h2
  have hrM : r < M.length := by have := par_lt M 1 _ r h1; omega
  have hμr : μ = ρ.v r := hμv.trans (chain_level I.cons I.good hrM hro)
  have hμ' := hμ
  rw [hlev, hμr] at hlow hμ'
  obtain ⟨hL1, hZc⟩ := seedLow_shape I hlen h1 hx2 hn hH hCP hμ' (by simp [etaOm]) hlow
  left
  rw [hZc, hlev, hμr]
  exact ⟨isSucc_psi_z (Or.inl (succ_ne_z _)), seedCond_of_gap (hR hL1 hν i hi hv h2 hμ)⟩

/-- **`hExp_t1GP4` with the seeds below `Ω_μ` reduced to the gap residuals** `TPLoGapRes`・`AbsDGapRes`
(M-only, at `L = 1`). -/
theorem hExp_t1GP5
    (hRT : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 → RestT M rk)
    (hFrm : ∀ N σ, Std N → N ≠ SRO → FrameV N σ → BandLast N σ →
      TPLoWLFRes2 N σ ∧ TPLoW0 N σ ∧ AbsDW0 N σ ∧ TPLoNSeed N σ ∧ TPLoN0 N σ)
    (hResN : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → ∀ r L, r + L + 1 = M.length →
      par M 1 (r + L) = some r → entry M 2 (r + L) = 0 →
      (DegRes TPLoAt M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧ TPLoLFRes2 M r L (entry M 0 (r + L) - entry M 0 r) ρ ∧
        (TPLoGapRes M r L ρ ∧ TPLoSeedLow0 M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ TPLoResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
      ((AbsDGapRes M r L ρ ∧ AbsDSeedLow0 M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧ AbsDResL_zero M r L (entry M 0 (r + L) - entry M 0 r) ρ) ∧
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
        tploResL_seed_of (tploResL_lf_of_leafB I hlen hr hx2 hVK (tploLFRes_ofB I hlen hr hx2 hVK hRN.1.2.1)) (tploSeedLow_of_gap I hlen hr hx2 hRN.1.2.2.1.1 hRN.1.2.2.1.2), hRN.1.2.2.2⟩)
      (absDRes_of_L I hlen hr hx2 ⟨absDResL_lf_of_leafB I hlen hr hx2 hVK,
        absDResL_seed_of (absDResL_lf_of_leafB I hlen hr hx2 hVK)
          (absDSeedLow_of_gap I hlen hr hx2 hRN.2.1.1.1 hRN.2.1.1.2), hRN.2.1.2⟩)
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
