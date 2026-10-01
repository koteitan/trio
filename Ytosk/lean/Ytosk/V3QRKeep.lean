/-
**3 行・t = 1・q = r: 枠の条件 (W)・(L)(ii) と鎖の下限。**

値の不変条件（大域）:
- **TP1W**: 書き換えの枠で cof y = ω の穴のある y について B < fsD(y, 1)。
- **TPLoW**: o(c) = ψ_s(y) で y に低い部分がなく、最後の項 Ω_a の a が対角化の点の穴（cof a = ω）をもつなら
  Ω_{fsD(a, ψ_μ(1))} ≥ Ω_{s+1}（μ = 穴の段）。
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

/-- **Value invariant TPLoW**: the low part stays empty at `η = ψ_μ(1)` for a diagonal-point hole. -/
def TPLoW (M : Mat) (ρ : Valn) : Prop :=
  ∀ c, c < M.length → ∀ s y, ρ.o c = psi s y z → (split y (psi (succ s) z z)).2 = z →
    ∀ a, last y = psi a z z → isSucc a = false → OHole a → cof a = .omega →
    ¬ psi (fsD a (psi (holeLev y) one z)) z z < psi (succ s) z z

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

end Ytosk
