/-
**3 行・t = 1・q = r: 枠の条件 (W)・(L)(ii) と鎖の下限。**

値の不変条件（大域）:
- **TP1W**: 書き換えの枠で cof y = ω の穴のある y について B < fsD(y, 1)。
- **TPLoW**: o(c) = ψ_s(y) で y に低い部分がなく、最後の項 Ω_a の a が対角化の点の穴（cof a = ω）をもつなら
  Ω_{fsD(a, η)} ≥ Ω_{s+1}。η は最後の列の枠（t = 1・q = r）の D の列 c の鎖の項の下限 gamS μ b_r 1 (max 1 d_c)
  （旧形の η = ψ_μ(1) は標準形で偽）。添字 0（始点）は TPLoN から（V3QRFinal4 の hLs0）。
補題:
- `lo_keep_Q`: y ≠ b_r で対角化の点の下に穴があれば、η₀ ≤ ζ で (L)(ii)。
- `lo_keep_br`: y = b_r（ψ_s(b_r)、s < μ）では ζ = ψ_μ(X) なら (L)(ii)。
- 鎖: gamS(k+1) = next(gamS k)、2 項目以降は ψ_μ(1) 以上。
-/
import Ytosk.V3QRDiag

namespace Ytosk

open T

/-- **Value invariant TP1W**: persistence at `η = 1` for holes with cofinality `ω`. -/
def TP1W (M : Mat) (ρ : Valn) : Prop :=
  ∀ i L c R, children M i = L ++ c :: R → ∀ s y, ρ.o c = psi s y z →
    lt (preState M ρ i L) y = true → lt (psi (ρ.v i) z z) (psi s y z) = true →
    cof y = .omega → OHole y → lt (preState M ρ i L) (fsD y one) = true

/-- **Value invariant TPLoW**: in the frame of the last column `x` (`t = 1`, `q = r`,
`o(r) = ψ_μ(b + Ω_{μ+1})`), at a `D` column `c` the low part stays empty at the lower bound
`gamS μ b_r 1 (max 1 d_c)` of its chain term (`d_c = dOf c`; the index `0` is the seed, handled by
`TPLoN`). The earlier form at `η = ψ_μ(1)` is false on standard matrices:
`(0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,0,0)(3,0,0)(2,1,1)(2,1,0)(3,2,1)(4,2,1)(5,0,0)(6,1,0)`
(`c = 4`, `d_c = 2`). -/
def TPLoW (M : Mat) (ρ : Valn) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ (app b (psi (succ μ) z z)) z →
    ∀ c, c < M.length - 1 → DepX M (M.length - 1) true c → ∀ s y, ρ.o c = psi s y z →
    y ≠ app b (psi (succ μ) z z) → (split y (psi (succ s) z z)).2 = z →
    ∀ a, last y = psi a z z → isSucc a = false → OHole a → cof a = .omega →
    ¬ psi (fsD a (gamS μ (app b (psi (succ μ) z z)) one
      (max 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) c)))) z z < psi (succ s) z z

/-- **(L)(ii) for `y ≠ b_r`** under a diagonal point, from the condition at `η₀ ≤ ζ`. -/
theorem lo_keep_Q {a' br μ s y ζ η₀ : T} (hD : DiagAt a' br μ (psi s y z)) (hy : y ≠ z) (hyb : y ≠ br)
    (hTPLf : (split y (psi (succ s) z z)).2 = z →
      ∀ a, last y = psi a z z → isSucc a = false → OHole a → cof a = .omega →
      ¬ psi (fsD a η₀) z z < psi (succ s) z z)
    (hζ0 : η₀ ≤ ζ) (hl : (split y (psi (succ s) z z)).2 = z) :
    (split (fsD y ζ) (psi (succ s) z z)).2 = z := by
  have hDy : DiagAt a' br μ y := DiagAt.arg_inv hD hy (fun h => hyb h.2)
  apply lo_z_keep hy hl
  have hyall : ∀ q ∈ summands y, ¬ q < psi (succ s) z z := by
    intro q hq
    have e := split_app (psi (succ s) z z) y
    rw [hl, app_z_right] at e
    rw [← e] at hq
    exact split_fst_ge _ y q hq
  have hDl := hDy.last_g
  have hlh := hyall _ (last_mem hy)
  obtain ⟨a, b, hlc⟩ := last_psi_form hy
  rw [hlc] at hlh hDl ⊢
  by_cases hb : b = z
  · subst hb
    have hns := DiagAt.not_omega_succ hDl
    have haz : a ≠ z := by
      intro h; subst h
      have := DiagAt.not_succ hDl
      have h1 : isSucc (psi z z z) = true := rfl
      rw [h1] at this; cases this
    have hDa : DiagAt a' br μ a := by
      cases hDl with
      | here hb' _ _ => exact absurd rfl hb'
      | arg hb' _ _ => exact absurd rfl hb'
      | sub _ _ h => exact h
    have hOa := ohole_of_diag hDa
    rw [fsD_sub haz hns]
    intro q hq
    simp only [summands, List.mem_cons, List.mem_nil_iff, or_false] at hq
    subst hq
    intro hlt
    apply hTPLf hl a hlc hns hOa (DiagAt.cof_omega hDa)
    exact lt_of_le_of_lt (le_psi_sub (fsD_mono_eta hOa hζ0)) hlt
  · intro q hq
    obtain ⟨b', rfl⟩ := summands_fsD_psi hb q hq
    intro hlt
    apply hlh
    rw [psi_lt_psi_z_iff] at hlt ⊢
    rcases hlt with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact absurd h' (T.not_lt_z _)

/-- **(L)(ii) for `y = b_r`**: the child `ψ_s(b_r)` with `s < μ` and an index `ψ_μ(X)`. -/
theorem lo_keep_br {μ b s ζ X : T} (hb : AllGeT (psi (succ μ) z z) b) (hsμ : lt s μ = true)
    (hζ : ζ = psi μ X z) :
    (split (fsD (app b (psi (succ μ) z z)) ζ) (psi (succ s) z z)).2 = z := by
  rw [fsD_eq_fs cof_br, fs_br]
  have hle : ¬ psi (succ μ) z z < psi (succ s) z z := by
    rw [psi_lt_psi_z_iff]
    rintro (h | ⟨_, h⟩)
    · exact lt_irrefl' _ (lt_of_le_of_lt (lt_succ_iff.mp h)
        (lt_trans (show s < μ from hsμ) (lt_succ_self μ)))
    · exact T.not_lt_z _ h
  apply split_snd_z_of_ge
  intro q hq
  rw [summands_app] at hq
  rcases List.mem_append.mp hq with hq | hq
  · intro hlt; exact hb q hq (lt_of_lt_of_le hlt (le_of_not_gt hle))
  · rw [hζ] at hq; simp [summands] at hq; subst hq
    rw [psi_lt_psi_z_iff]
    rintro (h | ⟨_, h⟩)
    · exact lt_irrefl' _ (lt_of_lt_of_le (show s < μ from hsμ) (lt_succ_iff.mp h))
    · exact T.not_lt_z _ h

/-- **(W) at `y = b_r`** from `B ≤ b`. -/
theorem hW_br {B μ b ζ : T} (hB : B ≤ b) (hζz : ζ ≠ z) :
    lt B (fsD (app b (psi (succ μ) z z)) ζ) = true := by
  rw [fsD_eq_fs cof_br, fs_br]
  exact lt_of_le_of_lt hB (lt_app_of hζz)

/-! ## 鎖 -/

theorem gamS_succ_q (μ b seed : T) (k : Nat) :
    gamS μ (app b (psi (succ μ) z z)) seed (k + 1) =
      qnext μ b (gamS μ (app b (psi (succ μ) z z)) seed k) := by
  show psi μ (fs _ _) z = _
  rw [fs_br]; rfl

theorem gamS_ne_z_q {μ b seed : T} (hs : seed ≠ z) :
    ∀ k, gamS μ (app b (psi (succ μ) z z)) seed k ≠ z
  | 0 => hs
  | k + 1 => by rw [gamS_succ_q]; unfold qnext; simp

/-- **From the second term on, the chain is at least `ψ_μ(1)`.** -/
theorem gamS_ge_psi1 {μ b seed : T} (hs : seed ≠ z) (k : Nat) :
    psi μ one z ≤ gamS μ (app b (psi (succ μ) z z)) seed (k + 1) := by
  rw [gamS_succ_q]; unfold qnext
  apply le_psi_arg
  exact one_le_of_ne_z (fun h => gamS_ne_z_q hs k (app_eq_z h).2)

/-- **The chain from `1` bounds the chain from the seed** from the first term on. -/
theorem gamS_lb {μ b seed : T} (hs : one ≤ seed) :
    ∀ j k, 1 ≤ j → j ≤ k →
      gamS μ (app b (psi (succ μ) z z)) one j ≤ gamS μ (app b (psi (succ μ) z z)) seed k := by
  have hmono1 : ∀ j, gamS μ (app b (psi (succ μ) z z)) one j ≤
      gamS μ (app b (psi (succ μ) z z)) one (j + 1) := by
    intro j
    induction j with
    | zero =>
      rw [gamS_succ_q]; unfold qnext
      exact one_le_of_ne_z (by simp)
    | succ j ih =>
      rw [gamS_succ_q, gamS_succ_q μ b one (j + 1)]
      exact le_psi_arg (app_le_app_left b ih)
  have hseed : ∀ k, gamS μ (app b (psi (succ μ) z z)) one k ≤ gamS μ (app b (psi (succ μ) z z)) seed k := by
    intro k
    induction k with
    | zero => exact hs
    | succ k ih =>
      rw [gamS_succ_q, gamS_succ_q μ b seed k]
      exact le_psi_arg (app_le_app_left b ih)
  have hidx : ∀ j d, gamS μ (app b (psi (succ μ) z z)) one j ≤
      gamS μ (app b (psi (succ μ) z z)) one (j + d) := by
    intro j d
    induction d with
    | zero => exact le_refl _
    | succ d ih => exact le_trans ih (hmono1 (j + d))
  intro j k _ hjk
  obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
  exact le_trans (hidx j d) (hseed (j + d))

/-- **TPLoW at the actual chain terms** (2026-10-24): the comparison of `TPLoW` at every chain term
`gamS μ b_r (sd r) k`, `k ≥ max 1 d_c`, of the seed `sd r` (`sd r = o_{M.take x}(r)` in `Inv3V2`). `TPLoW` asks it at
the lower bound `gamS μ b_r 1 (max 1 d_c)` and is false on grafted standard matrices (desc); the consumers use only
the actual chain terms. -/
def TPLoWAt (M : Mat) (ρ : Valn) (sd : Nat → T) : Prop :=
  ∀ r μ b, par M 1 (M.length - 1) = some r → par M 0 (M.length - 1) = some r →
    entry M 2 (M.length - 1) = 0 → ρ.o r = psi μ (app b (psi (succ μ) z z)) z → one ≤ sd r →
    ∀ c, c < M.length - 1 → DepX M (M.length - 1) true c → ∀ s y, ρ.o c = psi s y z →
    y ≠ app b (psi (succ μ) z z) → (split y (psi (succ s) z z)).2 = z →
    ∀ a, last y = psi a z z → isSucc a = false → OHole a → cof a = .omega →
    ∀ k, max 1 (dOf M (M.length - 1) (loQ M ρ μ b) (lbQ M ρ μ b) c) ≤ k →
      ¬ psi (fsD a (gamS μ (app b (psi (succ μ) z z)) (sd r) k)) z z < psi (succ s) z z

/-- `TPLoW` gives `TPLoWAt` (`gamS_lb`, `fsD` is monotone in the index). -/
theorem TPLoW.toAt {M : Mat} {ρ : Valn} (h : TPLoW M ρ) (sd : Nat → T) : TPLoWAt M ρ sd := by
  intro r μ b h1 h0 h2 hro hs c hc hd s y hcv hyb hl a hla hns hOa hca k hk hlt
  exact h r μ b h1 h0 h2 hro c hc hd s y hcv hyb hl a hla hns hOa hca
    (lt_of_le_of_lt (le_psi_sub (fsD_mono_eta hOa (gamS_lb hs _ k (le_max_left _ _) hk))) hlt)

/-- `TPLoWAt` with the seed of the row-1 parent of `x` as a constant. -/
theorem TPLoWAt.const {M : Mat} {ρ : Valn} {sd : Nat → T} {r : Nat} (h : TPLoWAt M ρ sd)
    (hr : par M 1 (M.length - 1) = some r) : TPLoWAt M ρ (fun _ => sd r) := by
  intro r' μ b h1 h0 h2 hro hs
  rw [hr] at h1; cases h1
  exact h r μ b hr h0 h2 hro hs

end Ytosk
