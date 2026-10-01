/-
**3 行・t = 1・q = r: 鎖の項と引き上げ。**

A = o(r) = ψ_μ(b + Ω_{μ+1})（b の加数は Ω_{μ+1} 以上）。次の項 next(ζ) = ψ_μ(b + ζ) = ψ_μ(br[ζ])。
- fsD(A, ζ) = next(ζ)（`fsD_A`）。
- ω^A = A（A は ω 冪の不動点、`omega_A`）だが、ζ < Ω_{μ+1} が 0 でなければ ω^{next ζ} = next(next ζ)（`omega_next`）。
  これがのりしろの枠の引き上げ。
-/
import Ytosk.V3QRShape

namespace Ytosk

open T

/-- The next term of the chain. -/
def qnext (μ b ζ : T) : T := psi μ (app b ζ) z

section
variable {μ b : T} (hb : AllGeT (psi (succ μ) z z) b)
include hb

omit hb in
theorem fs_br (ζ : T) : fs (app b (psi (succ μ) z z)) ζ = app b ζ := by
  rw [fs_app b (by simp), fs_Om_succ]

omit hb in
theorem cof_br : cof (app b (psi (succ μ) z z)) = .big μ := by
  rw [cof_app b (by simp)]; exact cof_omega_succ μ

omit hb in
/-- **`fsD(A, ζ) = next(ζ)`.** -/
theorem fsD_A (ζ : T) : fsD (psi μ (app b (psi (succ μ) z z)) z) ζ = qnext μ b ζ := by
  rw [fsD_here (by intro h; exact absurd (app_eq_z h).2 (by simp)) cof_br, fs_br]; rfl

/-- The parts of `b ++ ζ` at and below `Ω_{μ+1}`. -/
theorem split_b_app {ζ : T} (hζ : ζ < psi (succ μ) z z) :
    split (app b ζ) (psi (succ μ) z z) = (b, ζ) :=
  split_app_of hb (by
    cases ζ with
    | z => exact Or.inl rfl
    | psi a c d => right; exact lt_of_le_of_lt (head_le_self _) hζ)

/-- **`A` is a fixed point of `ω`.** -/
theorem omega_A (hot : isOT (psi μ (app b (psi (succ μ) z z)) z) = true) :
    omega (psi μ (app b (psi (succ μ) z z)) z) = psi μ (app b (psi (succ μ) z z)) z := by
  have hall : AllGeT (psi (succ μ) z z) (app b (psi (succ μ) z z)) := by
    intro q hq
    rw [summands_app] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hb q hq
    · simp [summands] at hq; rw [hq]; exact lt_irrefl' _
  apply omega_fix_nolo hot
  · intro hE
    obtain ⟨hμz, hlt⟩ := below_E0 hE
    have h3 : psi (succ μ) z z = Om one := by rw [hμz]; rfl
    exact not_lt_of_lo_z (by intro h; exact absurd (app_eq_z h).2 (by simp))
      (split_snd_z_of_ge hall) (by rw [h3]; rw [h3] at hlt; exact hlt)
  · unfold loOf; exact split_snd_z_of_ge hall


/-- **`ω^{next ζ} = next(next ζ)`** (the chain terms are not fixed points of `ω`). -/
theorem omega_next {ζ : T} (hζz : ζ ≠ z) (hζ : ζ < psi (succ μ) z z) (hot : isOT (qnext μ b ζ) = true) :
    omega (qnext μ b ζ) = qnext μ b (qnext μ b ζ) := by
  unfold qnext at hot ⊢
  by_cases hE : psi μ (app b ζ) z < E0
  · rw [omega_small hE]
    obtain ⟨hμz, hlt⟩ := below_E0 hE
    have hbz : b = z := by
      by_contra hbz
      obtain ⟨a, c, d, rfl⟩ : ∃ a c d, b = psi a c d := by
        cases b with
        | z => exact absurd rfl hbz
        | psi a c d => exact ⟨a, c, d, rfl⟩
      have h1 := hb _ (show psi a c z ∈ summands (psi a c d) by simp [summands])
      apply h1
      have h3 : psi (succ μ) z z = Om one := by rw [hμz]; rfl
      rw [h3]
      have h4 : head (app (psi a c d) ζ) = psi a c z := by rw [app_psi]; rfl
      rw [← h4]; exact lt_of_le_of_lt (head_le_self _) hlt
    rw [hbz, hμz]; simp
  · rw [omega_big' hot hE]
    unfold hiOf loOf
    rw [split_b_app hb hζ]
    simp [hζz]

end

end Ytosk
