/-
**3 行: ω 冪と fsD の交換（のりしろの枠の部品）。**

ψ_0(Ω_1) 以上の標準形 x = ψ_s(b) + c では ω^x = ψ_s(P + W)（P = b の Ω_{s+1} 以上の部分、W は b に低い部分があれば x、
なければ c、`omega_big`）。fsD は一番深い位置に作用するので、
- c ≠ 0 なら fsD は c に作用し、P も低い部分の有無も変わらない（`omega_fsD_rest`）。
- c = 0 で b に低い部分があり、fsD(x) でも P が同じで低い部分が残るなら交換する（`omega_fsD_lo`）。
- ω^x = x かつ ω^{fsD x} = fsD x なら自明（`omega_fsD_fix`）。
-/
import Ytosk.V3Path
import Ytosk.Omega

namespace Ytosk

open T

/-- The part of `b` at or above `Ω_{s+1}`, and the rest. -/
def hiOf (s b : T) : T := (split b (psi (succ s) z z)).1
def loOf (s b : T) : T := (split b (psi (succ s) z z)).2

theorem omega_big' {s b c : T} (hx : isOT (psi s b c) = true) (h : ¬ psi s b c < E0) :
    omega (psi s b c) = psi s (app (hiOf s b) (if loOf s b = z then c else psi s b c)) z :=
  omega_big hx h

/-- **Rest case.** `c ≠ 0`: `fsD` acts on `c`. -/
theorem omega_fsD_rest {s b c ζ : T} (hx : isOT (psi s b c) = true) (h : ¬ psi s b c < E0)
    (hc : c ≠ z) (hcs : isSucc c = false) (hx' : isOT (psi s b (fsD c ζ)) = true)
    (hc' : fsD c ζ ≠ z) (hcs' : isSucc (fsD c ζ) = false) :
    fsD (omega (psi s b c)) ζ = omega (fsD (psi s b c) ζ) := by
  have hfx : fsD (psi s b c) ζ = psi s b (fsD c ζ) := by
    cases c with
    | z => exact absurd rfl hc
    | psi c1 c2 c3 => rfl
  have h' : ¬ psi s b (fsD c ζ) < E0 := by
    intro hl
    obtain ⟨rfl, hb⟩ := below_E0 hl
    apply h; unfold E0; rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, hb⟩)
  rw [hfx, omega_big' hx h, omega_big' hx' h']
  by_cases hlo : loOf s b = z
  · rw [if_pos hlo, if_pos hlo]
    rw [fsD_psi (by intro he; exact hc (app_eq_z he).2) (by rw [isSucc_app _ hc]; exact hcs),
      fsD_app _ hc]
  · rw [if_neg hlo, if_neg hlo]
    rw [fsD_psi (by intro he; have h2 := (app_eq_z he).2; cases h2)
        (by rw [isSucc_app _ (by simp), isSucc_psi_rest _ _ _ hc]; exact hcs),
      fsD_app _ (by simp), hfx]

/-- **Low-part case.** `c = 0`, `b` has a low part, and `fsD` keeps the high part and a low part. -/
theorem omega_fsD_lo {s b ζ b' : T} (hx : isOT (psi s b z) = true) (h : ¬ psi s b z < E0)
    (hlo : loOf s b ≠ z) (hfx : fsD (psi s b z) ζ = psi s b' z)
    (hx' : isOT (psi s b' z) = true) (h' : ¬ psi s b' z < E0)
    (hhi : hiOf s b' = hiOf s b) (hlo' : loOf s b' ≠ z) (hbs : isSucc (psi s b z) = false) :
    fsD (omega (psi s b z)) ζ = omega (fsD (psi s b z) ζ) := by
  rw [hfx, omega_big' hx h, omega_big' hx' h', if_neg hlo, if_neg hlo', hhi,
    fsD_psi (by intro he; have h2 := (app_eq_z he).2; cases h2) (by rw [isSucc_app _ (by simp)]; exact hbs),
    fsD_app _ (by simp), hfx]

/-- **Fixed points.** -/
theorem omega_fsD_fix {x ζ : T} (h1 : omega x = x) (h2 : omega (fsD x ζ) = fsD x ζ) :
    fsD (omega x) ζ = omega (fsD x ζ) := by
  rw [h1, h2]

/-- A standard `ψ_s(b)` with no low part is a fixed point of `ω`. -/
theorem omega_fix_nolo {s b : T} (hx : isOT (psi s b z) = true) (h : ¬ psi s b z < E0)
    (hlo : loOf s b = z) : omega (psi s b z) = psi s b z := by
  rw [omega_big' hx h, if_pos hlo, app_z_right]
  have := split_app (psi (succ s) z z) b
  unfold hiOf; unfold loOf at hlo
  rw [hlo, app_z_right] at this
  rw [this]

end Ytosk
