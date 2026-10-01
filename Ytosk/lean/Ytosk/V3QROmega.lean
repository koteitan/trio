/-
**3 行・t = 1・q = r: `ω` と fsD の交換（鎖の項が `ω` の不動点でないとき）。**

t1 の `omega_fsD_hole` と同じ形で、仮定を q = r 用に変える:
- 葉 Ω_{succ} の場合は対角化の点があるので起きない（不動点の仮定 hζfix が要らない）。
- 低い部分の保存 (L)(ii) は呼ぶ側が渡す（hLY）。
- fsD が後者にならないことは対角化の点から（`DiagAt.fsD_not_succ`、ζ = ψ_μ(X) の形が要らない）。
-/
import Ytosk.V3QRLocOA

namespace Ytosk

open T

/-- The rest of a sum keeps the diagonal point. -/
theorem DiagAt.rest_inv {a b μ s y c : T} (hc : c ≠ z) (h : DiagAt a b μ (psi s y c)) : DiagAt a b μ c := by
  cases c with
  | z => exact absurd rfl hc
  | psi c d e =>
    cases h with
    | rest h' => exact h'

theorem DiagAt.fsD_ne_z {a b μ ζ t : T} (hζ : ζ ≠ z) (h : DiagAt a b μ t) : fsD t ζ ≠ z :=
  fsD_ne_z_of_holeT (vr := a) hζ (Or.inr ⟨a, lt_irrefl' a, h⟩)

/-- **`fsD` at a diagonal point is not a successor** (for a nonzero index). -/
theorem DiagAt.fsD_not_succ {a b μ ζ : T} (hζ : ζ ≠ z) : ∀ {t : T}, DiagAt a b μ t → isSucc (fsD t ζ) = false
  | _, DiagAt.here hb hc _ => by
    rw [fsD_here hb hc]
    exact isSucc_psi_z (Or.inr (fs_ne_z_big hc hζ))
  | _, DiagAt.rest (c := c) (d := d) (e := e) (a' := a') (b' := b') h => by
    show isSucc (psi a' b' (fsD (psi c d e) ζ)) = false
    have ih := DiagAt.fsD_not_succ hζ h
    have hne : fsD (psi c d e) ζ ≠ z := DiagAt.fsD_ne_z hζ h
    unfold isSucc at ih ⊢
    obtain ⟨c', d', e', he⟩ : ∃ c' d' e', fsD (psi c d e) ζ = psi c' d' e' := by
      cases h' : fsD (psi c d e) ζ with
      | z => exact absurd h' hne
      | psi c' d' e' => exact ⟨c', d', e', rfl⟩
    rw [he] at ih ⊢
    simpa [last] using ih
  | _, DiagAt.arg (a' := a') (b' := b') hb hs h => by
    rw [fsD_psi hb hs]
    exact isSucc_psi_z (Or.inr (DiagAt.fsD_ne_z hζ h))
  | _, DiagAt.sub (a' := a') ha hs h => by
    rw [fsD_sub ha hs]
    exact isSucc_psi_z (Or.inl (DiagAt.fsD_ne_z hζ h))

/-- **`ω` commutes with `fsD`** at a diagonal point (`q = r`). -/
theorem omega_fsD_hole_Q {a' μ br vr Y ζ : T} (hY : isOT Y = true) (hH : HoleT μ br vr Y)
    (hD : DiagAt a' br μ Y) (hcb : cof br = .big μ) (hζz : ζ ≠ z)
    (hok : ∀ t, isOT t = true → HoleT μ br vr t → isOT (fsD t ζ) = true ∧ fsD t ζ < t)
    (hLY : ∀ s b, Y = psi s b z → b ≠ z → (split b (psi (succ s) z z)).2 = z →
      (split (fsD b ζ) (psi (succ s) z z)).2 = z) :
    fsD (omega Y) ζ = omega (fsD Y ζ) := by
  have hYz := holeT_ne_z hH
  have hYs := holeT_not_succ hH
  obtain ⟨hYot', hYlt⟩ := hok Y hY hH
  by_cases hE : Y < E0
  · rw [omega_small hE, fsD_psi hYz hYs, omega_small (lt_trans hYlt hE)]
  cases Y with
  | z => exact absurd rfl hYz
  | psi s b c =>
    by_cases hc : c = z
    · subst hc
      have hθ : psi (succ s) z z = psi (succ s) z z := rfl
      by_cases hlo : loOf s b = z
      · rw [omega_fix_nolo hY hE hlo]
        symm
        by_cases hb : b = z
        · subst hb
          have hsz : s ≠ z := by
            intro he; subst he; rw [show isSucc (psi z z z) = true from rfl] at hYs; cases hYs
          by_cases hs : isSucc s = true
          · exact absurd (DiagAt.not_omega_succ hD) (by rw [hs]; simp)
          · have hns : isSucc s = false := by simpa using hs
            have hHs := holeT_sub_inv hns hH
            rw [fsD_sub hsz hns] at hYot' ⊢
            apply omega_fix_nolo hYot'
            · intro hE'; exact fsD_ne_z_of_holeT hζz hHs (below_E0 hE').1
            · rfl
        · have hHb := holeT_arg hb hH hcb
          have hbs := not_succ_arg_of_holeT hb hH
          rw [fsD_psi hb hbs] at hYot' ⊢
          have hlo' := hLY s b rfl hb hlo
          apply omega_fix_nolo hYot'
          · intro hE'
            obtain ⟨hsz, hlt⟩ := below_E0 hE'
            subst hsz
            exact not_lt_of_lo_z (fsD_ne_z_of_holeT hζz hHb) hlo' hlt
          · exact hlo'
      · -- the low part survives
        have hb : b ≠ z := by intro he; subst he; exact hlo rfl
        have hHb := holeT_arg hb hH hcb
        have hbs := not_succ_arg_of_holeT hb hH
        have hfx : fsD (psi s b z) ζ = psi s (fsD b ζ) z := fsD_psi hb hbs ζ
        have e := split_app (psi (succ s) z z) b
        set hi := (split b (psi (succ s) z z)).1 with hhi
        set lo := (split b (psi (succ s) z z)).2 with hlodef
        have hlo0 : lo ≠ z := hlo
        have hbot : isOT b = true := isOT_arg hY
        have hloot : isOT lo = true := isOT_app_right (by rw [e]; exact hbot)
        have hHlo : HoleT μ br vr lo := holeT_app_inv hlo0 (by rw [e]; exact hHb)
        have hfb : fsD b ζ = app hi (fsD lo ζ) := by
          conv => lhs; rw [← e]
          exact fsD_app hi hlo0 ζ
        have hflt : head (fsD lo ζ) < psi (succ s) z z := by
          have h1 := (hok lo hloot hHlo).2
          have h2 : head lo < psi (succ s) z z := split_snd_head_lt hlo0
          have h3 : lo < psi (succ s) z z := by
            cases hlc : lo with
            | z => exact absurd hlc hlo0
            | psi a' b' c' =>
              rw [hlc] at h2
              exact lt_of_head_lt h2
          exact lt_of_le_of_lt (head_le_self _) (lt_trans h1 h3)
        have hsplit : split (fsD b ζ) (psi (succ s) z z) = (hi, fsD lo ζ) := by
          rw [hfb]; exact split_app_of (split_fst_ge _ b) (Or.inr hflt)
        apply omega_fsD_lo hY hE hlo hfx (by rw [← hfx]; exact hYot')
        · intro hE'
          obtain ⟨hsz, hlt⟩ := below_E0 hE'
          subst hsz
          apply hE
          -- `Y ≥ E0` forces a summand of `b` at least `Ω_1`, which `fsD b ζ` keeps
          exfalso
          have hhiz : hi ≠ z := by
            intro hz
            rw [hz] at e
            simp only [app] at e
            have h3 : b < psi (succ z) z z := by
              rw [← e]
              cases hlc : lo with
              | z => exact absurd hlc hlo0
              | psi a' b' c' =>
                have h2 : head lo < psi (succ z) z z := split_snd_head_lt hlo0
                rw [hlc] at h2
                exact lt_of_head_lt h2
            apply hE
            unfold E0; rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h3⟩
          have hhi1 : ¬ hi < psi (succ z) z z := not_lt_of_lo_z hhiz (by
            rw [hhi]
            have := split_app_of (t := psi (succ z) z z) (B := hi) (X := z) (split_fst_ge _ b)
              (Or.inl rfl)
            rw [app_z_right] at this
            rw [this])
          apply hhi1
          exact lt_of_le_of_lt (le_app_self hi _) (by rw [← hfb]; exact hlt)
        · unfold hiOf; rw [hsplit]
        · unfold loOf; rw [hsplit]; exact fsD_ne_z_of_holeT hζz hHlo
        · exact hYs
    · have hHc := holeT_rest hc hH
      have hfx : fsD (psi s b c) ζ = psi s b (fsD c ζ) := by
        cases c with
        | z => exact absurd rfl hc
        | psi => rfl
      rw [hfx] at hYot'
      exact omega_fsD_rest hY hE hc (holeT_not_succ hHc) hYot' (fsD_ne_z_of_holeT hζz hHc)
        (DiagAt.fsD_not_succ hζz (DiagAt.rest_inv hc hD))

end Ytosk
