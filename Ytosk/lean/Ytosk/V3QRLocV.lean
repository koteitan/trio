/-
**3 行・t = 1・q = r: v の局所条件 `VLocZ` をすべての D の呼び出しで（`qr_vloc`）。**

値の不変条件（大域、cof ω の穴に限る）:
- **AbsUW**: 上げ i → k で、v(P_1 i) の加数で last v(k) より小さいものは fsD(last v(k), 1) より小さい。
- **AbsDW**: のりしろの項 W について同じ（fsD(W, 1)）。
補題:
- `qr_lkeep`: D の列 c（c < x、o(c) ≠ A）の (L)(ii) を鎖の添字 gamS(m + d_c) で（y = b_r なら引き上げの数 ≥ 1、
  y ≠ b_r なら TPLoW か始点の仮定 hLs）。
- のりしろの ω の交換: 引き上げ 2（`omega_lift2`）、1（`omega_lift1`）、0（`omega_fsD_hole_Q` を 2 回）。
-/
import Ytosk.V3QROmega

namespace Ytosk

open T

/-- **Value invariant AbsUW** (`η = 1`, holes with cofinality `ω`). -/
def AbsUW (M : Mat) (ρ : Valn) : Prop :=
  ∀ i k, upg M i = some k → OHole (last (ρ.v k)) → cof (last (ρ.v k)) = .omega →
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < last (ρ.v k) → q < fsD (last (ρ.v k)) one

/-- **Value invariant AbsDW** (`η = 1`, holes with cofinality `ω`). -/
def AbsDW (M : Mat) (ρ : Valn) : Prop :=
  ∀ i, i < M.length → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → OHole (bumpW M ρ i) →
    cof (bumpW M ρ i) = .omega →
    ∀ q ∈ summands (vOpt ρ (par M 1 i)), q < bumpW M ρ i → q < fsD (bumpW M ρ i) one

/-- In a standard `P ++ X`, every summand of `P` is at least the head of `X`. -/
theorem summands_ge_of_app : ∀ {P X : T}, isOT (app P X) = true → ∀ q ∈ summands P, head X ≤ q
  | z, _, _, q, hq => by simp [summands] at hq
  | psi a b c, X, h, q, hq => by
    rw [app_psi, isOT_psi_iff] at h
    obtain ⟨_, _, h3, h4, _⟩ := h
    have ih := summands_ge_of_app h3
    have hhd : head X ≤ head (app c X) := by
      cases c with
      | z => exact le_refl _
      | psi c1 c2 c3 =>
        rw [app_psi]
        show head X ≤ psi c1 c2 z
        exact ih _ (by simp [summands])
    simp only [summands, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact le_trans hhd h4
    · exact ih q hq

/-- `A = ψ_μ(b + Ω_{μ+1})` is not below `ε_0`. -/
theorem A_not_lt_E0 {μ b : T} (hb : AllGeT (psi (succ μ) z z) b) :
    ¬ psi μ (app b (psi (succ μ) z z)) z < E0 := by
  have hall : AllGeT (psi (succ μ) z z) (app b (psi (succ μ) z z)) := by
    intro q hq
    rw [summands_app] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hb q hq
    · simp [summands] at hq; rw [hq]; exact lt_irrefl' _
  intro hE
  obtain ⟨hμz, hlt⟩ := below_E0 hE
  have h3 : psi (succ μ) z z = Om one := by rw [hμz]; rfl
  exact not_lt_of_lo_z (by intro h; exact absurd (app_eq_z h).2 (by simp))
    (split_snd_z_of_ge hall) (by rw [h3]; rw [h3] at hlt; exact hlt)

/-- A nonempty decreasing list of single summands has a nonzero sum. -/
theorem sumN_ne_z_of_single {l : List T} (hs : ∀ t ∈ l, Single t)
    (hp : l.Pairwise (fun a b => b ≤ a)) (hne : l ≠ []) : sumN l ≠ z := by
  obtain ⟨l', t, rfl⟩ : ∃ l' t, l = l' ++ [t] := by
    rcases List.eq_nil_or_concat l with h | ⟨l', t, h⟩
    · exact absurd h hne
    · exact ⟨l', t, by rw [h, List.concat_eq_append]⟩
  rw [sumN_snoc_dec hs hp]
  intro h
  exact single_ne_z (hs t (List.mem_append_right _ (List.mem_singleton_self _))) (app_eq_z h).2

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ b seed : T} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) (h1 : par M 1 x = some r) (hq : par M 0 x = some r)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ) (hAD : AbsD M ρ)
  (hro : ρ.o r = psi μ (app b (psi (succ μ) z z)) z)
  (hox : ρ.o x = psi (succ μ) z z)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hAD hro hox hOS

/-- **Every `D` value below `x` has a hole and a diagonal point** (`q = r`). -/
theorem qr_holeD : ∀ bb i, DepX M x bb i → i < x →
    HoleT μ (app b (psi (succ μ) z z)) μ (valB ρ bb i) ∧
    ∃ a', ¬ lt μ a' = true ∧ DiagAt a' (app b (psi (succ μ) z z)) μ (valB ρ bb i) := by
  have hbr : app b (psi (succ μ) z z) ≠ z := fun h => absurd (app_eq_z h).2 (by simp)
  have hrx : r < x := par_lt M 1 x r h1
  have hA : Anc0 M r x := anc0_of_par M 1 r x h1
  have hdep := qr_dep hx hR0 hZ2 hSD hZ1 hUAT hUAB h1 hx2 hq
  have hHx : HoleT μ (app b (psi (succ μ) z z)) μ (ρ.o x) :=
    Or.inl (by rw [hox]; exact cof_omega_succ μ)
  have hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true :=
    fun i h2 h3 h4 _ => absurd h4 (hdep.2.2 true i h2 h3)
  have hHole := t1_hole0 hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hAD hrx hA hro
    cof_br rfl hbr hHx hF1 hOS (hS2_t1 hR0 hA (by omega)) (hS3_t1 h1 hA (by omega) hx hR0 hZ2 hSD hZ1)
  intro bb i hD hi
  have hir : i ≤ r := by
    by_contra h
    exact hdep.2.2 bb i (by omega) hi hD
  obtain ⟨hH, hDL, _⟩ := hHole bb i hD (Or.inl hi)
  exact ⟨hH, hDL hir⟩

variable (hb : AllGeT (psi (succ μ) z z) b)
  (hVS : ∀ i, i < x → DepX M x false i → VShape M x i)
  (hBk : ∀ i j k, i < x → DepX M x false i → j ∈ children M i → col M j = bump M i →
    k ∈ children M j → DepX M x true k → k < x)
  (hxv : ¬ DepX M x false x)
  (hseedS : ∃ a X, seed = psi a X z)
  (hTPL : TPLoW M ρ)
  (hLs : ∀ c, c < x → DepX M x true c → dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c = 0 →
    ∀ s y, ρ.o c = psi s y z → y ≠ app b (psi (succ μ) z z) →
    (split y (psi (succ s) z z)).2 = z → (split (fsD y seed) (psi (succ s) z z)).2 = z)
include hb hVS hBk hxv hseedS hTPL hLs

/-- **(L)(ii) at a `D` column** (not `A`) with its own index. -/
theorem qr_lkeep (m : Nat) {c : Nat} (hc : c < x) (hdc : DepX M x true c) {s y : T}
    (hcv : ρ.o c = psi s y z) (hyz : y ≠ z) (hnA : ¬ (s = μ ∧ y = app b (psi (succ μ) z z)))
    (hl : (split y (psi (succ s) z z)).2 = z) :
    (split (fsD y (gamS μ (app b (psi (succ μ) z z)) seed
      (m + dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c))) (psi (succ s) z z)).2 = z := by
  have hseedz : seed ≠ z := by obtain ⟨a, X, he⟩ := hseedS; rw [he]; simp
  obtain ⟨_, a', _, hDc⟩ := qr_holeD hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 h1 hq hC hG hKD hTD hAD hro hox hOS
    true c hdc hc
  simp only [valB, cond_true] at hDc
  rw [hcv] at hDc
  by_cases hyb : y = app b (psi (succ μ) z z)
  · subst hyb
    have hsμ : s ≠ μ := fun h => hnA ⟨h, rfl⟩
    have hsle := diag_here_inv hDc
    have hslt : lt s μ = true := by
      rcases lt_trichotomy' s μ with h | h | h
      · exact h
      · exact absurd h hsμ
      · exact absurd h hsle
    have hdpos := qr_d_pos hx hC hG hKD hTD hq hro hOS hVS hBk hxv hc hdc hcv hsμ
    obtain ⟨k', hk'⟩ : ∃ k', m + dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c = k' + 1 :=
      ⟨m + dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c - 1, by omega⟩
    rw [hk', gamS_succ_q]
    exact lo_keep_br hb hslt rfl
  · rcases Nat.eq_zero_or_pos (m + dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c) with hk0 | hkpos
    · rw [hk0]
      exact hLs c hc hdc (by omega) s y hcv hyb hl
    · obtain ⟨k', hk'⟩ : ∃ k', m + dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c = k' + 1 :=
      ⟨m + dOf M x (loQ M ρ μ b) (lbQ M ρ μ b) c - 1, by omega⟩
      have hDy : DiagAt a' _ μ y := DiagAt.arg_inv hDc hyz (fun h => hyb h.2)
      have hlev : holeLev y = μ := DiagAt.holeLev_eq hDy
      rw [hk']
      refine lo_keep_Q hDc hyz hyb ?_ (gamS_ge_psi1 hseedz k') hl
      intro hl' a hla hns hOa hca
      have := hTPL c (by omega) s y hcv hl' a hla hns hOa hca
      rw [hlev] at this; exact this

end

end Ytosk
