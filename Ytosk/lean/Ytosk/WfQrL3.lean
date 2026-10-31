/-
**WfQrL3 (2026-11-01): the high part is kept by `DQ`** (the side condition `hHi` of `WfQrL2.omega_DQ_arg`).

If `b` is standard and has a low part below `θ = Ω_{a+1}`, then its last summand `l` is below `θ`; the re-exposed
summands `Q` and the new last summand `l_N` are below `l`; so `split` stops at the same place in `b` and `b_N`:
`hiOf a b_N = hiOf a b`, and `b_N` keeps a low part.  The only remaining side condition of `omega_DQ` is then
`hLo` (no low part appears), which is `lo_keep_DQ` + `TPLoQ` (WfQrL2).
-/
import Ytosk.WfQrL2

namespace Ytosk.WfQrL3
open T Ytosk Ytosk.WfQrL2

/-- **The last summand of a standard sum is at most every summand.** -/
theorem last_le_summands {s y : T} : ∀ {B : T}, isOT (app B (psi s y z)) = true →
    ∀ q ∈ summands B, psi s y z ≤ q
  | z, _, q, hq => by simp [summands] at hq
  | psi a b c, h, q, hq => by
    simp only [app_psi] at h
    have hc := isOT_rest h
    have ih := last_le_summands hc
    have hhead : head (app c (psi s y z)) ≤ psi a b z := (isOT_psi_iff.mp h).2.2.2.1
    have hl : psi s y z ≤ head (app c (psi s y z)) := by
      cases hcz : c with
      | z => simp [app, head]
      | psi a' b' c' =>
        have := ih (psi a' b' z) (by rw [hcz]; simp [summands])
        simpa [app, head] using this
    simp only [summands, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact le_trans hl hhead
    · exact ih q hq

/-- **`split` before a tail below `θ`.** -/
theorem split_app_low {θ : T} : ∀ {B Y : T}, head Y < θ → Y ≠ z →
    split (app B Y) θ = ((split B θ).1, app (split B θ).2 Y)
  | z, Y, hY, hYz => by
    cases Y with
    | z => exact absurd rfl hYz
    | psi a1 b1 c1 =>
      simp only [app_z, split]
      rw [if_pos (show lt (psi a1 b1 z) θ = true from hY)]
  | psi a1 b1 B', Y, hY, hYz => by
    simp only [app_psi, split]
    by_cases h : lt (psi a1 b1 z) θ = true
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h, split_app_low hY hYz]

/-- A low part in a standard `b = B ++ l` forces `l < θ`. -/
theorem last_lt_of_lo {θ B s y : T} (hb : isOT (app B (psi s y z)) = true)
    (hlo : (split (app B (psi s y z)) θ).2 ≠ z) : psi s y z < θ := by
  by_contra hn
  apply hlo
  apply split_snd_z_of_ge
  intro q hq
  rw [summands_app] at hq
  rcases List.mem_append.mp hq with hq | hq
  · intro hqt
    exact hn (lt_of_le_of_lt (last_le_summands hb q hq) hqt)
  · simp only [summands, List.mem_cons, List.mem_nil_iff, or_false] at hq
    subst hq; exact hn

/-- **The high part is kept by `DQ`**, and a low part stays. -/
theorem hi_keep_DQ {η b bN θ : T} (hb : isOT b = true) (h : DQ η true b bN)
    (hlo : (split b θ).2 ≠ z)
    (hlNz : ∀ B l lN Q, b = app B l → bN = app B (app Q lN) → lN ≠ z)
    (hlNh : ∀ B l lN Q, b = app B l → bN = app B (app Q lN) → head lN ≤ lN) :
    (split bN θ).1 = (split b θ).1 ∧ (split bN θ).2 ≠ z := by
  obtain ⟨B, l, lN, Q, s, y, eb, ebN, hl, hd, hQ⟩ := DQ.true_inv h
  have hlz := hlNz B l lN Q eb ebN
  have hlh := hlNh B l lN Q eb ebN
  subst eb ebN hl
  have hlt : psi s y z < θ := last_lt_of_lo hb hlo
  have hlNlt : lN < psi s y z := hd.lt
  have hY : head (app Q lN) < θ := by
    cases hQc : Q with
    | z => simpa [app] using lt_of_le_of_lt hlh (lt_trans hlNlt hlt)
    | psi a1 b1 c1 =>
      have := (hQ (psi a1 b1 z) (by rw [hQc]; simp [summands])).2
      simpa [app, head] using lt_trans this hlt
  have hYz : app Q lN ≠ z := fun he => hlz (app_eq_z he).2
  rw [split_app_low hY hYz, split_app_low (show head (psi s y z) < θ from hlt) (by simp)]
  refine ⟨rfl, fun he => hYz (app_eq_z he).2⟩

end Ytosk.WfQrL3
