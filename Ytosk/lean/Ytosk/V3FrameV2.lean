/-
**FrameV の作り直し `FrameV2`（2026-10-16、top）。**

`FrameV`（V3ExpT1L）は大域の AbsD・TPLo を含む。どちらも ext1 で偽（破れは q ≠ r の枠）。
`tplow_of_lf`・`absDW_of_lf`・`tplon_of_lf` が使うのは、最後の列の q = r の枠（段 μ ≠ 0）の D の列での
AbsD・TPLo だけで、穴の段は frame_hole により μ。そこで、その枠だけの形に狭める。

- `AbsDQR`: q = r の枠、μ ≠ 0、D の v の呼び出し i（cof W = ω）で、v(P_1 i) の W 未満の加数は fsD(W, ψ_μ(Ω_{μ+1})) 未満。
- `TPLoQR`: q = r の枠、μ ≠ 0、D の o の呼び出し c（y ≠ b_r、cof a = ω）で、TPL の比較を ψ_μ(Ω_{μ+1}) で。
- `FrameV2`: FrameV の ad・tplo を adq・tplq に替えたもの。`FrameV.toV2` で旧形から出る（狭めであることの確認）。
- `tplow_of_lf2`・`absDW_of_lf2`・`tplon_of_lf2`: 旧補題と同じ証明。段は枠の μ で直接述べるので frame_hole は要らない。
- `FrmLF2`: 行列ごとの LevFree の残り（FrmLF の前件 FrameV を FrameV2 に替えたもの）。
- `frameFields_of_V2`: FrmLF2 と FrameV2 から、その行列の TPLoW・AbsDW・TPLoN。どの仕組みの行列にも使える。
-/
import Ytosk.V3T0LF

namespace Ytosk

open T

/-- **AbsD at the `D` `v`-calls of the last-column frame** (`t = 1`, `q = r`, level `μ ≠ 0`). -/
def AbsDQR (M : Mat) (ρ : Valn) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ (app b (psi (succ μ) z z)) z → μ ≠ z →
    ∀ i, i < M.length - 1 → DepX M (M.length - 1) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
    OHole (bumpW M ρ i) → cof (bumpW M ρ i) = .omega →
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i → q < fsD (bumpW M ρ i) (etaOm μ)

/-- **TPLo at the `D` `o`-calls of the last-column frame** (`t = 1`, `q = r`, level `μ ≠ 0`). -/
def TPLoQR (M : Mat) (ρ : Valn) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ (app b (psi (succ μ) z z)) z → μ ≠ z →
    ∀ c, c < M.length - 1 → DepX M (M.length - 1) true c → ∀ s y, ρ.o c = psi s y z →
    y ≠ app b (psi (succ μ) z z) → (split y (psi (succ s) z z)).2 = z →
    ∀ a, last y = psi a z z → isSucc a = false → OHole a → cof a = .omega →
    ¬ psi (fsD a (etaOm μ)) z z < psi (succ s) z z

/-- `FrameV` with `AbsD`・`TPLo` narrowed to the last-column frame. -/
structure FrameV2 (M : Mat) (ρ : Valn) : Prop where
  s : SInv M
  cons : Cons M ρ
  good : Good3 M ρ
  kd : BumpKidsDec M ρ
  td : BumpTermDec M ρ
  adq : AbsDQR M ρ
  tplq : TPLoQR M ρ

/-- The narrowed fields follow from the old global ones (the hole level of the frame is `μ`). -/
theorem FrameV.toV2 {M : Mat} {ρ : Valn} (I : FrameV M ρ) : FrameV2 M ρ := by
  refine ⟨I.s, I.cons, I.good, I.kd, I.td, ?_, ?_⟩
  · intro r μ b h1 hq hx2 hro _ i hi hd he1 he2 hO _ q hqm hlt
    have hH := frame_hole I h1 hq hx2 hro false i hd hi
    simp only [valB, cond_false] at hH
    have hiM : i < M.length := by omega
    have hlev : holeLev (bumpW M ρ i) = μ := by
      rw [← last_v_bumpW I.cons I.good hiM he1 he2]; exact holeLev_holeT (holeT_last hH)
    have hA := I.ad i hiM he1 he2 hO q hqm hlt
    rwa [hlev] at hA
  · intro r μ b h1 hq hx2 hro _ c hc hd s y ho _ hspl a hla hns hOa _
    have hH := frame_hole I h1 hq hx2 hro true c hd hc
    simp only [valB, cond_true] at hH
    rw [ho] at hH
    have hyz : y ≠ z := by intro h; rw [h] at hla; simp [last] at hla
    have hlev : holeLev y = μ := by rw [← holeLev_psi_arg (a := s) hyz]; exact holeLev_holeT hH
    have hT := I.tplo c (by omega) s y ho hspl a hla hns hOa
    rwa [hlev] at hT

/-- **TPLoW from `TPLoQR` and `LevFree`** at a positive level; the level `0` is the residual `h0`. -/
theorem tplow_of_lf2 {M : Mat} {ρ : Valn} (I : FrameV2 M ρ)
    (hLF : TPLoWLF M ρ) (h0 : TPLoW0 M ρ) : TPLoW M ρ := by
  intro r μ b h1 hq hx2 hro c hc hd s y ho hyb hspl a hla hns hOa hca
  by_cases hμ : μ = z
  · exact h0 r μ b h1 hq hx2 hro c hc hd s y ho hyb hspl a hla hns hOa hca hμ
  have hLFs := hLF r μ b h1 hq hx2 hro c hc hd s y ho hyb hspl a hla hns hOa hca hμ
  have hT := tpl_iff.mp (I.tplq r μ b h1 hq hx2 hro hμ c hc hd s y ho hyb hspl a hla hns hOa hca)
  apply tpl_iff.mpr
  obtain ⟨k, hk⟩ : ∃ k, max 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) c) = k + 1 :=
    ⟨max 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) c) - 1, by
      have := le_max_left 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) c); omega⟩
  rw [hk]
  refine fsD_transfer (subClosed_subS s) (fun u hu h1' _ => ?_) hOa s (subT_subS (.refl s)) hT hT
  exact lt_of_lt_of_le (lt_Om_of_bandS hLFs hu h1') (om_le_psi μ _ z)

/-- **AbsDW from `AbsDQR` and `LevFree`** at a positive level; the level `0` is the residual `h0`. -/
theorem absDW_of_lf2 {M : Mat} {ρ : Valn} (I : FrameV2 M ρ)
    (hLF : AbsDWLF M ρ) (h0 : AbsDW0 M ρ) : AbsDW M ρ := by
  intro r μ b h1 hq hx2 hro i hi hd he1 he2 hO hcof q hqm hlt
  by_cases hμ : μ = z
  · exact h0 r μ b h1 hq hx2 hro i hi hd he1 he2 hO hcof hμ q hqm hlt
  have hLFs := hLF r μ b h1 hq hx2 hro i hi hd he1 he2 hO hcof hμ
  have hA := I.adq r μ b h1 hq hx2 hro hμ i hi hd he1 he2 hO hcof q hqm hlt
  obtain ⟨k, hk⟩ : ∃ k, max 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) i) = k + 1 :=
    ⟨max 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) i) - 1, by
      have := le_max_left 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) i); omega⟩
  rw [hk]
  refine fsD_transfer (subClosed_subS _) (fun u hu h1' _ => ?_) hO q (summand_subS hqm) hA hA
  exact lt_of_lt_of_le (lt_Om_of_bandS hLFs hu h1') (om_le_psi μ _ z)

/-- **TPLoN from `TPLoQR` and `LevFree`** when the seed is at least `Ω_μ` (`μ ≠ 0`). -/
theorem tplon_of_lf2 {M : Mat} {ρ : Valn} (I : FrameV2 M ρ) (hLF : TPLoWLF M ρ)
    (hS : TPLoNSeed M ρ) (h0 : TPLoN0 M ρ) : TPLoN M ρ := by
  intro ρ' rk' hC' hR' r μ b h1 hq hx2 hro c hc hd hd0 s y ho hyb hspl a hla hns hOa hca hNa
  by_cases hμ : μ = z
  · exact h0 ρ' rk' hC' hR' r μ b h1 hq hx2 hro c hc hd hd0 s y ho hyb hspl a hla hns hOa hca hNa hμ
  by_cases hsd : psi μ z z ≤ ρ'.o r
  · have hLFs := hLF r μ b h1 hq hx2 hro c hc hd s y ho hyb hspl a hla hns hOa hca hμ
    have hT := tpl_iff.mp (I.tplq r μ b h1 hq hx2 hro hμ c hc hd s y ho hyb hspl a hla hns hOa hca)
    apply tpl_iff.mpr
    refine fsD_transfer (subClosed_subS s) (fun u hu h1' _ => ?_) hOa s (subT_subS (.refl s)) hT hT
    exact lt_of_lt_of_le (lt_Om_of_bandS hLFs hu h1') hsd
  · exact hS ρ' rk' hC' hR' r μ b h1 hq hx2 hro c hc hd hd0 s y ho hyb hspl a hla hns hOa hca hNa hμ hsd

/-- **The matrix-wise `LevFree` residual of the frame fields**, with the narrowed `FrameV2`. -/
def FrmLF2 : Prop :=
  ∀ N σ, Std N → N ≠ SRO → FrameV2 N σ →
    TPLoWLF N σ ∧ TPLoW0 N σ ∧ AbsDWLF N σ ∧ AbsDW0 N σ ∧ TPLoNSeed N σ ∧ TPLoN0 N σ

/-- **TPLoW・AbsDW・TPLoN of any standard matrix** from `FrmLF2` and its `FrameV2`. -/
theorem frameFields_of_V2 (hF : FrmLF2) {N : Mat} {σ : Valn} (hN : Std N) (hS : N ≠ SRO)
    (I : FrameV2 N σ) : TPLoW N σ ∧ AbsDW N σ ∧ TPLoN N σ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hF N σ hN hS I
  exact ⟨tplow_of_lf2 I h1 h2, absDW_of_lf2 I h3 h4, tplon_of_lf2 I h1 h5 h6⟩

end Ytosk
