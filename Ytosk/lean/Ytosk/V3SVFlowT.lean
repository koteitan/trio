/-
**σ increases strictly (term lemmas for the flow of `T2SVStrict`, 2026-11-08).**

`σ = sh V V'` with `V < V'` does not decrease standard terms (`le_sh`) and acts summand by summand. A strict
increase at one place gives a strict increase of the whole term:
- the subscript (`lt_sh_of_shf`) or the argument (`lt_sh_of_arg`) of a summand,
- the last summand of a sum (`add_lt_sh_of_right`, `sumN_snoc_lt_sh`),
- the exponent of `ω` (`omega_lt_sh`) and of the `v` equation (`shf_lt_of_omega`),
- one step of `sp` (`step_lt_sh`): without the trigger the summand stays; with the trigger and a low part `ψ_s(y)`
  stays (`H_lt_sh`); with the trigger and no low part the state is `y` itself, so `y` must grow.
-/
import Ytosk.V3SVFlowM

namespace Ytosk.V3Main.SeedPF
open T Classical WfExQ1 WfExQ2 WfAbsW WfT2X G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {V V' : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
include hV hV' hVV

theorem lt_sh_of_shf {s y c : T} (hVs : V < s) (h : s < shf V V' s) :
    psi s y c < sh V V' (psi s y c) := by
  rw [sh_psi_gt hVs, T.psi_lt_psi]; exact Or.inl h

theorem lt_sh_of_arg {s y c : T} (hs : isOT s = true) (hVs : V < s) (hy : y < sh V V' y) :
    psi s y c < sh V V' (psi s y c) := by
  rw [sh_psi_gt hVs, T.psi_lt_psi]
  rcases lt_or_eq_of_le (le_shf_self hV hV' (le_of_lt hVV) hs (le_of_lt hVs)) with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h, hy⟩)

theorem succ_lt_shf_succ : succ V < shf V V' (succ V) := by
  rw [shf_succ hV hV' hVV hV (le_refl V), shf_self]
  exact succ_lt_succ' hVV

theorem omega_lt_sh {W : T} (hW : isOT W = true) (h : W < sh V V' W) : omega W < sh V V' (omega W) := by
  rw [sh_omega hV hV' hVV hW]
  exact omega_lt_omega hW (isOT_sh hV hV' hVV hW) h

theorem add_lt_sh_of_right {B t : T} (hB : isOT B = true) (ht : isOT t = true) (h : t < sh V V' t) :
    add B t < sh V V' (add B t) := by
  rw [sh_add hV hV' hVV hB ht]
  exact lt_of_lt_of_le (add_lt_add_left B h)
    (add_le_add_right _ (isOT_sh hV hV' hVV hB) (isOT_sh hV hV' hVV ht) (le_sh hV hV' (le_of_lt hVV) hB))

theorem sumN_snoc_lt_sh {l : List T} {t : T} (hl : ∀ u ∈ l, isOT u = true) (ht : isOT t = true)
    (h : t < sh V V' t) : sumN (l ++ [t]) < sh V V' (sumN (l ++ [t])) := by
  rw [sumN_snoc_add hl ht]
  exact add_lt_sh_of_right hV hV' hVV (isOT_sumN l hl) ht h

theorem shf_lt_of_omega {A W : T} (hA : isOT A = true) (hW : isOT W = true) (hVA : V ≤ A)
    (h : W < sh V V' W) : sf (add A (omega W)) < shf V V' (sf (add A (omega W))) := by
  rw [← shf_add_omega hV hV' hVV hA hW hVA]
  have hw := isOT_omega hW
  have hw' := isOT_omega (isOT_sh hV hV' hVV hW)
  rw [sf_ot (isOT_add hA hw), sf_ot (isOT_add (isOT_shf hV hV' hVV hA) hw')]
  exact lt_of_lt_of_le (add_lt_add_left A (omega_lt_omega hW (isOT_sh hV hV' hVV hW) h))
    (add_le_add_right _ (isOT_shf hV hV' hVV hA) hw' (le_shf_self hV hV' (le_of_lt hVV) hA hVA))

theorem H_lt_sh {s y : T} (hy : isOT (psi s y z) = true) (hlo : (split y (psi (succ s) z z)).2 ≠ z)
    (h : psi s y z < sh V V' (psi s y z)) : H s y < sh V V' (H s y) := by
  have hH : isOT (H s y) = true := isOT_arg (CutClosed.isOT_H_self hy)
  have hHe := H_eq hy
  rw [if_neg hlo] at hHe
  rw [hHe] at hH ⊢
  rw [← add_eq_app hH]
  exact add_lt_sh_of_right hV hV' hVV (isOT_app_left hH) hy h

/-- **One step of `sp` grows** when its summand grows, and its argument grows if the trigger leaves no low
part. -/
theorem step_lt_sh {a B s y : T} (hB : isOT B = true) (hy : isOT (psi s y z) = true) (hVs : V < s)
    (h : y < sh V V' y ∨ (s < shf V V' s ∧ y = z)) : step a B s y z < sh V V' (step a B s y z) := by
  have hsv : psi s y z < sh V V' (psi s y z) := by
    rcases h with h | ⟨h, _⟩
    · exact lt_sh_of_arg hV hV' hVV (isOT_sub hy) hVs h
    · exact lt_sh_of_shf hV hV' hVV hVs h
  unfold step
  split_ifs with htr
  · have hyz : y ≠ z := by
      rintro rfl; cases B <;> simp [lt] at htr
    by_cases hlo : (split y (psi (succ s) z z)).2 = z
    · have hHy : H s y = y := by
        rw [H_eq hy, if_pos hlo]
        have := split_app (psi (succ s) z z) y
        rw [hlo] at this; exact this
      rw [hHy]
      rcases h with h | ⟨_, h⟩
      · exact h
      · exact absurd h hyz
    · exact H_lt_sh hV hV' hVV hy hlo hsv
  · exact add_lt_sh_of_right hV hV' hVV hB hy hsv

end

end Ytosk.V3Main.SeedPF
