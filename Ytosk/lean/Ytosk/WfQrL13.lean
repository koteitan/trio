/-
**WfQrL13 (2026-11-01): the `ω` exchange through a `DQ` sum and the bump term** (towards `hBW` of `qr_engineDQ`).

The bump term of a bump frame is `ω^{P + ω^G}` with `G = K + o(k)` (sum of the children of `j`) and `P` the earlier
bump terms; in `M[n]` only `o(k)` changes.  Two `ω` layers:
  * `G → G_N` is `DQ.snoc` of the step `o(k) → o_N(k)`;
  * `omega_DQ_true`: `DQ` on a sum passes through `ω` (rest case: `omega_DQ_rest`; single case: `omega_DQ`
    when no summand is re-exposed at the top, `hQ0`);
  * `bumpW_DQ`: both layers, the side conditions of `omega_DQ` (`hLo`: no low part appears, `hB`: the old
    exchange at a base step) given as hypotheses at each layer.
-/
import Ytosk.WfQrL12

namespace Ytosk.WfQrL13
open T Ytosk Ytosk.WfQrL2

/-- A sum with a single last summand is not `0`. -/
theorem app_single_ne_z {B s y : T} : app B (psi s y z) ≠ z := by
  cases B <;> simp [app]

/-- **`DQ` on a sum through `ω`.** -/
theorem omega_DQ_true {η Y YN : T} (h : DQ η true Y YN) (hY : isOT Y = true) (hYN : isOT YN = true)
    (hsm : (Y < E0 ∧ YN < E0) ∨ (¬ Y < E0 ∧ ¬ YN < E0))
    (hQ0 : ∀ s b, Y = psi s b z → ∀ B l lN Q, Y = app B l → YN = app B (app Q lN) → Q = z)
    (hLo : ∀ a b bN, Y = psi a b z → YN = psi a bN z → b ≠ z →
      (loOf a b = z → loOf a bN = z) ∧ (loOf a b ≠ z → hiOf a bN = hiOf a b ∧ loOf a bN ≠ z))
    (hB : YN = fsD Y η → fsD (omega Y) η = omega (fsD Y η) ∧ fsD (omega Y) η < omega Y) :
    DQ η false (omega Y) (omega YN) := by
  rcases hsm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact omega_DQ_small h1 h2 h
  cases Y with
  | z =>
    exfalso
    obtain ⟨B, l, lN, Q, s, y, eY, _, hl, _, _⟩ := DQ.true_inv h
    rw [hl] at eY; exact app_single_ne_z eY.symm
  | psi a b c =>
    by_cases hc : c = z
    · subst hc
      obtain ⟨B, l, lN, Q, s, y, eY, eYN, hl, hd, _⟩ := DQ.true_inv h
      have hQz := hQ0 a b rfl B l lN Q eY eYN
      subst hQz
      have hB0 : B = z := by
        cases B with
        | z => rfl
        | psi a1 b1 c1 =>
          simp only [app_psi] at eY
          injection eY with _ _ h3
          rw [hl] at h3
          exact absurd h3.symm app_single_ne_z
      subst hB0
      have hlY : l = psi a b z := by simpa [app] using eY.symm
      have hYN' : YN = lN := by simpa [app] using eYN
      subst hYN'
      rw [hlY] at hd
      exact omega_DQ hd hY hYN h1 h2 hLo hB
    · exact omega_DQ_rest hc hY hYN h1 h2 h

/-- The side conditions of `omega_DQ_true` at one layer `Y → Y_N`. -/
def OmSide (η Y YN : T) : Prop :=
  isOT Y = true ∧ isOT YN = true ∧ ((Y < E0 ∧ YN < E0) ∨ (¬ Y < E0 ∧ ¬ YN < E0)) ∧
  (∀ s b, Y = psi s b z → ∀ B l lN Q, Y = app B l → YN = app B (app Q lN) → Q = z) ∧
  (∀ a b bN, Y = psi a b z → YN = psi a bN z → b ≠ z →
    (loOf a b = z → loOf a bN = z) ∧ (loOf a b ≠ z → hiOf a bN = hiOf a b ∧ loOf a bN ≠ z)) ∧
  (YN = fsD Y η → fsD (omega Y) η = omega (fsD Y η) ∧ fsD (omega Y) η < omega Y)

/-- **The bump term, two `ω` layers**: `ω^{P + ω^{K + o(k)}}` → `ω^{P + ω^{K + o_N(k)}}` from `o(k) → o_N(k)`. -/
theorem bumpW_DQ {η P0 K0 ok oN : T} (hok : ∃ s y, ok = psi s y z) (hd : DQ η false ok oN)
    (h1 : OmSide η (app K0 ok) (app K0 oN))
    (h2 : OmSide η (app P0 (omega (app K0 ok))) (app P0 (omega (app K0 oN)))) :
    DQ η false (omega (app P0 (omega (app K0 ok)))) (omega (app P0 (omega (app K0 oN)))) := by
  obtain ⟨hY1, hYN1, hsm1, hQ1, hLo1, hB1⟩ := h1
  obtain ⟨hY2, hYN2, hsm2, hQ2, hLo2, hB2⟩ := h2
  have d1 := DQ.snoc K0 hok hd
  have d2 := omega_DQ_true d1 hY1 hYN1 hsm1 hQ1 hLo1 hB1
  have hs : ∃ s y, omega (app K0 ok) = psi s y z := (single_omega hY1).2
  have d3 := DQ.snoc P0 hs d2
  exact omega_DQ_true d3 hY2 hYN2 hsm2 hQ2 hLo2 hB2

end Ytosk.WfQrL13
