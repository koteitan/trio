/-
**3 行・t = 0: 書き換えの一致 trig_agree を G3 の切り口（cutsNSG、PH3cKindG）で（2026-10-12、t0-exp）。**

PH3c の切り口の文法 cutsNS は標準形で偽で、closure が G3（V3PDef の cutsNSG・PH3cG）に広げた。
trig_agree（V3T0RE）が使うのは「切り口は項以下」と「P + t の切り口は P の切り口か P + (t の切り口)」の
2 つだけなので、G3 でも同じ形で言える。
-/
import Ytosk.V3PKindG
import Ytosk.V3T0RE

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **A G3 cut of `P + t`** is a cut of `P` or `P` followed by a cut of `t`. -/
theorem cutsNSG_split {s t : T} : ∀ {P B : T}, B ∈ cutsNSG s (app P t) →
    B ∈ cutsNSG s P ∨ ∃ κ ∈ cutsNSG s t, B = app P κ
  | z, B, h => Or.inr ⟨B, by simpa using h, by simp [app]⟩
  | psi a x c, B, h => by
    have h' : B ∈ cutsNSG s (psi a x (app c t)) := h
    rcases mem_cutsNSG_psi.mp h' with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact Or.inl (mem_cutsNSG_psi.mpr (Or.inl ⟨u, hu, rfl⟩))
    · exact Or.inl (mem_cutsNSG_psi.mpr (Or.inr (Or.inl ⟨u, hu, rfl⟩)))
    · rcases cutsNSG_split hu with h2 | ⟨κ, hκ, rfl⟩
      · exact Or.inl (mem_cutsNSG_psi.mpr (Or.inr (Or.inr ⟨u, h2, rfl⟩)))
      · exact Or.inr ⟨κ, hκ, rfl⟩

/-- **A rewriting frame keeps rewriting** (G3 cut) when its argument changes only at the right end. -/
theorem trig_agreeG {a B s y y' : T} (hRE : REr y y')
    (hK : B ≠ z → PH3cKindG B (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s)
    (hcut : (split y (psi (succ s) z z)).2 = z → B ≠ z → ∀ P a' x T', y = app P (psi a' x z) → y' = app P T' →
      ∀ κ ∈ cutsNSG s (psi a' x z), B = app P κ → κ < T')
    (htr : lt B y = true ∧ lt (psi a z z) (psi s y z) = true) :
    lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true := by
  obtain ⟨P, a', x, T', rfl, rfl, hT⟩ := hRE
  have hPT : P < app P T' := lt_app_ne hT
  have hBlt : B < app P T' := by
    by_cases hB : B = z
    · rw [hB]; exact lt_of_le_of_lt (z_le P) hPT
    set θ := psi (succ s) z z
    have e := split_app θ (app P (psi a' x z))
    rcases hK hB with ⟨heq, hlo⟩ | ⟨_, (⟨R, hR, hhi⟩ | ⟨_, hc⟩)⟩
    · rw [heq] at e
      obtain ⟨R0, hR0⟩ := prefix_of_app_single e hlo
      rw [hR0, app_assoc]
      exact lt_app_ne (app_ne_z_right hT)
    · rw [hhi, app_assoc] at e
      obtain ⟨R0, hR0⟩ := prefix_of_app_single e (fun h => hR (app_eq_z h).1)
      rw [hR0, app_assoc]
      exact lt_app_ne (app_ne_z_right hT)
    · by_cases hlo : (split (app P (psi a' x z)) θ).2 = z
      · have e' := e
        rw [hlo, app_z_right] at e'
        rw [e'] at hc
        rcases cutsNSG_split hc with h | ⟨κ, hκ, hBk⟩
        · exact lt_of_le_of_lt (cutsNSG_le h) hPT
        · rw [hBk]; exact app_lt_app_left P (hcut hlo hB P a' x T' rfl rfl κ hκ hBk)
      · obtain ⟨R0, hR0⟩ := prefix_of_app_single e hlo
        have hle : (split (app P (psi a' x z)) θ).1 ≤ P := by
          have := le_app_self (split (app P (psi a' x z)) θ).1 R0; rwa [← hR0] at this
        exact lt_of_le_of_lt (le_trans (cutsNSG_le hc) hle) hPT
  refine ⟨hBlt, ?_⟩
  have h2 : psi a z z < psi s (app P (psi a' x z)) z := htr.2
  show psi a z z < psi s (app P T') z
  rcases psi_lt_psi_z_iff.mp h2 with h | ⟨rfl, _⟩
  · exact psi_lt_psi_z_iff.mpr (Or.inl h)
  · exact psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, lt_of_le_of_lt (z_le _) hPT⟩)

end Ytosk
