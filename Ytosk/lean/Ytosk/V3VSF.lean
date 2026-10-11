/-
**VSmallF の、添字が変わった子の枠（t = 0 の T0VSResD・t = 1 の VSFRes2 と共通の核）。**

枠 i の子 c が Ω_s = ψ_s(0) から Ω_{s′}（s′ ◁ s）に替わるとき、新しい添字の段 a の成分は Ω_{s′} 以下か状態 B 以下:
- B ≠ 0: s′ ◁ s の試しに C = s をとると成分は s の成分か 0 で押さえられ、古い VSmallF で Ω_s 以下か B 以下。
  B の加数はどれも Ω_s 以上なので Ω_s ≤ B。
- B = 0: 古い o(i) = ψ_a(Ω_s) が標準形で Ω_{s′} ◁ Ω_s なので ψ_a(Ω_{s′}) も標準形（ot_parent_lhd）。
  s′ ≥ a なら s′ の成分は Ω_{s′} の成分で Ω_{s′} より小さい。s′ < a なら成分はない。
-/
import Ytosk.V3DropNode
import Ytosk.V3DropV
import Ytosk.V3Seed

namespace Ytosk

open T

/-- A nonzero `B` whose summands are all at least `t` is at least `t`. -/
theorem le_of_summands_ge {t B : T} (hB : B ≠ z) (h : ∀ q ∈ summands B, t ≤ q) : t ≤ B :=
  le_trans (h _ (head_mem_summands hB)) (head_le_self B)

/-- **The components of a changed subscript** (a leaf child `ψ_s(0)` replaced by `ψ_{s′}(0)`, `s′ ◁ s`). -/
theorem vs_changed_bound {a B s s' : T} (hs'ot : isOT s' = true) (hl : Lhd z s' s)
    (hBc : ∀ q ∈ summands B, psi s z z ≤ q)
    (hsub : ∀ g ∈ comps a s, g ≤ psi s z z ∨ g ≤ B)
    (hot : isOT (psi a (step a B s z z) z) = true) :
    ∀ g ∈ comps a s', g ≤ psi s' z z ∨ g ≤ B := by
  intro g hg
  by_cases hB : B = z
  · subst hB
    have hst : step a z s z z = psi s z z := by
      unfold step; rw [if_neg (fun h => T.not_lt_z _ h.1)]; rfl
    rw [hst] at hot
    have hot' := ot_parent_lhd hot (isOT_psi_zz hs'ot) (Or.inr (lhd_psi_sub hl))
    by_cases hsa : s' < a
    · rw [comps_nil_of_lt hs'ot hsa] at hg; simp at hg
    · have hall := ((isOT_psi_iff).mp hot').2.2.2.2
      left
      apply le_of_lt
      apply hall g
      rw [comps_psi_z_of_ge hsa]
      simp [hg]
  · right
    obtain ⟨d, hd, hgd⟩ := hl.2 a s hl.1 (le_refl s) g hg
    rcases List.mem_append.mp hd with hd | hd
    · rcases hsub d hd with h | h
      · exact le_trans hgd (le_trans h (le_of_summands_ge hB hBc))
      · exact le_trans hgd h
    · simp [Gc, comps] at hd
      rw [hd] at hgd
      exact le_trans hgd (z_le _)

end Ytosk
