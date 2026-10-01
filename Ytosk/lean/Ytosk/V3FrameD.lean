/-
**3 行: 枠の交換の条件 FrameD を、書き換えの持続 (W) と低い部分の保存 (L) から出す（項の側）。**

2 行の `frameD_path` を割り当てから切り離した形。子の値 c = ψ_s(y) と状態 b について、
- 書き換えない枠: b ++ c が標準形（親の値の標準形から出る）なら、後ろに足すのは fsD の後も同じ（`hleaf` は y = 0 のとき）、
- 書き換える枠: (W) b < y⟨ζ⟩ と (L) 低い部分の有無が保たれるなら交換する。
-/
import Ytosk.V3Agree
import Ytosk.TwoRowF

namespace Ytosk

open T

/-- **The frame condition from (W) and (L)**, for any frame. -/
theorem frameD_gen {a b s y ζ : T} (hcot : isOT (psi s y z) = true)
    (hok : isOT (fsD (psi s y z) ζ) = true ∧ fsD (psi s y z) ζ < psi s y z)
    (hcns : isSucc (psi s y z) = false)
    (hns : y ≠ z → isSucc y = false)
    (hleaf : y = z → ∀ s' y', psi s' y' z ∈ summands (fsD (psi s y z) ζ) → y' ≤ b ∨ s' < a)
    (hW : lt b y = true → lt (psi a z z) (psi s y z) = true → lt b (fsD y ζ) = true)
    (hL : lt b y = true → lt (psi a z z) (psi s y z) = true →
      ((split y (psi (succ s) z z)).2 ≠ z → fsD (split y (psi (succ s) z z)).2 ζ ≠ z) ∧
      ((split y (psi (succ s) z z)).2 = z → (split (fsD y ζ) (psi (succ s) z z)).2 = z))
    (hbc : ¬ (lt b y = true ∧ lt (psi a z z) (psi s y z) = true) →
      isOT (app b (psi s y z)) = true) :
    FrameD a b (psi s y z) ζ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [spArg_single]
    rcases step_cases (a := a) (b := b) hcot with ⟨B, hB⟩ | ⟨h1, _, h3, _⟩
    · rw [hB]; intro h'; exact absurd (app_eq_z h').2 (by simp)
    · rw [h1]; exact h3
  · rw [spArg_single]
    rcases step_cases (a := a) (b := b) hcot with ⟨B, hB⟩ | ⟨h1, _, h3, _⟩
    · rw [hB, isSucc_app B (by simp)]; exact hcns
    · rw [h1]; exact hns h3
  · by_cases htr : lt b y = true ∧ lt (psi a z z) (psi s y z) = true
    · have hy : y ≠ z := by rintro rfl; simp [lt] at htr
      have hys := hns hy
      by_cases hlo : (split y (psi (succ s) z z)).2 = z
      · exact frame_fsD_trig0' hcot hys hok htr hlo ((hL htr.1 htr.2).2 hlo) (hW htr.1 htr.2)
      · exact frame_fsD_trig' hcot hys hok htr hlo ((hL htr.1 htr.2).1 hlo) (hW htr.1 htr.2)
    · have hno : y ≤ b ∨ s < a := by
        by_cases h1 : lt b y = true
        · have h2 : ¬ lt (psi a z z) (psi s y z) = true := fun h2 => htr ⟨h1, h2⟩
          rcases not_trig_cases h2 with h3 | h3
          · exact Or.inr h3
          · left; rw [h3]; exact z_le _
        · left
          rcases lt_trichotomy' y b with h3 | h3 | h3
          · exact Or.inl h3
          · exact Or.inr h3
          · exact absurd h3 h1
      apply frame_fsD_notrig' hok hno (hbc htr)
      intro s' y' hq
      by_cases hy : y = z
      · exact hleaf hy s' y' hq
      · have hys := hns hy
        rw [fsD_psi hy hys] at hq hok
        simp only [summands, List.mem_cons, List.mem_nil_iff, or_false, psi.injEq] at hq
        obtain ⟨rfl, rfl, _⟩ := hq
        have hylt : fsD y ζ < y := by
          have := hok.2; rw [psi_lt_psi_z_iff] at this
          rcases this with h' | ⟨_, h'⟩
          · exact absurd h' (lt_irrefl' _)
          · exact h'
        rcases hno with h' | h'
        · exact Or.inl (le_of_lt (lt_of_lt_of_le hylt h'))
        · exact Or.inr h'

end Ytosk
