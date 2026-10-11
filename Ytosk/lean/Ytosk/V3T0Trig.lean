/-
**3 行・t = 0: T0TrigRes（古い枠が書き換えるなら新しい枠も、PH3c の cut の種類）を PH3c・RE・CutResG に帰着。**

D の枠 (i, c)、c は最後の数える子、o(c) = ψ_s(y)、o_N(c) = ψ_s(y′)。古い枠が書き換え、状態 B が hi(y) の先頭部分でないとき:
- B = 0 なら hi(y) = 0 + hi(y) で先頭部分。B ≠ 0 なら M の PH3c で種類は eq・pre・cut。eq・pre は先頭部分なので cut。
- RE: y = P + t（t は 1 項）、y′ = P + T′（T′ ≠ 0）。
  - lo(y) ≠ 0: y = hi + lo と P + t を比べて P = hi + R0。B ≤ hi ≤ P < y′。
  - lo(y) = 0: hi(y) = y = P + t。切り口は P の中（B ≤ P < y′）か t の中（B = P + κ、CutResG で κ < T′）。
- 書き換えの後半 ψ_a(0) < ψ_s(y′) は a < s か、a = s で y′ ≠ 0 から。
-/
import Ytosk.V3T0TopR
import Ytosk.V3T0Cut

namespace Ytosk

open T

/-- **Residual RE** (same subscript, the argument changes): the new argument differs from the old one only in
the last summand, with a nonzero new tail. -/
def T0RE2 : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ c, c < r → DepX M (r + L) true c →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z → y' ≠ y →
        ∃ P a x T', y = app P (psi a x z) ∧ y' = app P T' ∧ T' ≠ z

/-- **Residual: the cut in the last summand** (`T0CutRes` without the condition on the low part of `y′`). -/
def T0CutResG : Prop :=
  ∀ (M : Mat) (ρ : Valn) (rk : Bool → Nat → Nat) (r L : Nat), Std M → M ≠ SRO → Inv3 M ρ rk →
    Res3A M ρ rk → r + L + 1 = M.length → 0 < L → par M 0 (r + L) = some r → entry M 1 (r + L) = 0 →
    ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
      ∀ i c (Lc : List Nat), i < r → c < r → CL M i = Lc ++ [c] → DepX M (r + L) true c →
      ∀ s y y', ρ.o c = psi s y z → σ.o c = psi s y' z →
      (split y (psi (succ s) z z)).2 = z →
      spArg (ρ.v i) z (sumN (Lc.map ρ.o)) ≠ z →
      Trig (ρ.v i) (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) s y →
      ∀ P a x T', y = app P (psi a x z) → y' = app P T' →
      ∀ κ ∈ cutsNS s (psi a x z), spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = app P κ → κ < T'

/-- **The pure step**: an old rewriting frame of the cut kind keeps rewriting when the argument changes only in
its last summand. -/
theorem trig_keep {a B s P a' x T' : T} (hT : T' ≠ z) (hB : B ≠ z)
    (hK : PH3cKind B (split (app P (psi a' x z)) (psi (succ s) z z)).1
      (split (app P (psi a' x z)) (psi (succ s) z z)).2 s)
    (hnp : ¬ ∃ R, (split (app P (psi a' x z)) (psi (succ s) z z)).1 = app B R)
    (hcut : (split (app P (psi a' x z)) (psi (succ s) z z)).2 = z →
      ∀ κ ∈ cutsNS s (psi a' x z), B = app P κ → κ < T')
    (htr : lt B (app P (psi a' x z)) = true ∧ lt (psi a z z) (psi s (app P (psi a' x z)) z) = true) :
    lt B (app P T') = true ∧ lt (psi a z z) (psi s (app P T') z) = true := by
  set θ := psi (succ s) z z
  set y := app P (psi a' x z) with hy
  have hPT : P < app P T' := lt_app_ne hT
  have hBlt : B < app P T' := by
    rcases hK with ⟨heq, _⟩ | ⟨_, (⟨R, _, hR⟩ | ⟨_, hc⟩)⟩
    · exact absurd ⟨z, by rw [heq, app_z_right]⟩ hnp
    · exact absurd ⟨R, hR⟩ hnp
    · by_cases hlo : (split y θ).2 = z
      · have e := split_app θ y
        rw [hlo, app_z_right] at e
        rw [e, hy] at hc
        rcases cutsNS_app hc with h | ⟨κ, hκ, rfl⟩
        · exact lt_of_le_of_lt (cutsNS_le h) hPT
        · exact app_lt_app_left P (hcut hlo κ hκ rfl)
      · have e := split_app θ y
        rw [hy] at e
        obtain ⟨R0, hR0⟩ := prefix_of_app_single e hlo
        have hle : (split y θ).1 ≤ P := by rw [hR0]; exact le_app_self _ _
        exact lt_of_le_of_lt (le_trans (cutsNS_le hc) hle) hPT
  refine ⟨hBlt, ?_⟩
  have h2 : psi a z z < psi s y z := htr.2
  show psi a z z < psi s (app P T') z
  rcases psi_lt_psi_z_iff.mp h2 with h | ⟨rfl, _⟩
  · exact psi_lt_psi_z_iff.mpr (Or.inl h)
  · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_lt (z_le _) hPT⟩)

/-- **`T0TrigRes` from PH3c of `M`, RE and the cut residual.** -/
theorem t0TrigRes_of (hPH : ∀ M ρ rk, Std M → M ≠ SRO → Inv3 M ρ rk → Res3A M ρ rk → PH3c M ρ)
    (hRE : T0RE2) (hCut : T0CutResG) : T0TrigRes := by
  intro M ρ rk r L hM hS I R hlen hL hp he1 n hn σ hCN i c Lc hi hc hCL hD s y y' hy hy' htr hnp
  set B := spArg (ρ.v i) z (sumN (Lc.map ρ.o)) with hBdef
  by_cases hB : B = z
  · exact absurd ⟨(split y (psi (succ s) z z)).1, by rw [hB]; rfl⟩ hnp
  by_cases hyy : y' = y
  · rw [hyy]; exact htr
  have hK := hPH M ρ rk hM hS I R i (by omega) Lc c [] hCL s y hy hB htr
  obtain ⟨P, a', x, T', rfl, rfl, hT⟩ := hRE M ρ rk r L hM hS I R hlen hL hp he1 n hn σ hCN c hc hD s _ _ hy hy' hyy
  exact trig_keep hT hB hK hnp
    (fun hlo κ hκ hBk => hCut M ρ rk r L hM hS I R hlen hL hp he1 n hn σ hCN i c Lc hi hc hCL hD s _ _ hy hy'
      hlo hB htr P a' x T' rfl rfl κ hκ hBk) htr

end Ytosk
