/-
**帯の条件 BandS: 添字 μ の節点 ψ_μ(b) はどれも b ≥ Ω_{μ+1}。**

t = 1 の種の条件で使うのは「帯 [Ω_μ, ψ_μ(Ω_{μ+1})) に部分項がない」ことだけ（lt_Om_of_levFree の結論）。
groupA の LevFree μ V（添字 μ の節点がない）はこれを含むが、LevFree・LevLeafInv は標準形で偽
（groupA の t = 2 の族 M[2] = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,0)(2,2,1)(3,2,1)(4,1,0)(5,2,0)(3,2,0)(4,3,1)(5,3,1)(6,1,0)(7,2,0)、
v = ψ_1(Ω_2) の節点）。BandS はその族でも成り立つ。順序は添字を先に比べるので、節点ごとの条件で帯が空になる。
-/
import Ytosk.V3ExpT1A
import Ytosk.V3PhiGapT2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **The band condition at `μ`**: every node with subscript `μ` has argument at least `Ω_{μ+1}`. -/
def BandS (μ V : T) : Prop := ∀ b c, SubT (psi μ b c) V → ¬ b < psi (succ μ) z z

theorem bandS_of_levFree {μ V : T} (h : LevFree μ V) : BandS μ V :=
  fun b c hs _ => h μ b c hs rfl

theorem bandS_z (μ : T) : BandS μ z := fun _ _ h => by cases h

/-- **The band `[Ω_μ, ψ_μ(Ω_{μ+1}))` is empty.** -/
theorem lt_Om_of_bandS {μ V u : T} (h : BandS μ V) (hu : SubS V u) (hlt : u < etaOm μ) :
    u < psi μ z z := by
  obtain ⟨w, hw, hu'⟩ := hu
  have node : ∀ a b c, u = psi a b c → (∃ c', SubT (psi a b c') V) → u < psi μ z z := by
    intro a b c hue hn
    obtain ⟨c', hs⟩ := hn
    subst hue
    unfold etaOm at hlt
    rcases T.psi_lt_psi.mp hlt with h1 | ⟨rfl, h2⟩ | ⟨_, _, h3⟩
    · exact T.psi_lt_psi.mpr (Or.inl h1)
    · exact absurd h2 (h b c' hs)
    · exact absurd h3 (T.not_lt_z _)
  rcases hu' with hue | ⟨a, b, c, hwe, hue⟩
  · subst hue
    cases u with
    | z => exact T.z_lt_psi _ _ _
    | psi a b c => exact node a b c rfl ⟨c, hw⟩
  · subst hwe
    exact node a b z hue ⟨c, hw⟩

theorem bandS_add {μ A X : T} (hA : BandS μ A) (hX : BandS μ X) : BandS μ (add A X) := by
  obtain ⟨P, hP, hs⟩ := add_eq_app_prefix A X
  rw [hP]
  intro b c h
  rcases subT_app_cases P X _ h with h | ⟨a', b', R, hq, hw⟩
  · exact hX b c h
  · obtain ⟨c1, hc1⟩ := subT_of_summand (hs _ hq)
    rcases hw with he | hw | hw
    · cases he; exact hA b c1 hc1
    · exact hA b c (SubT.trans hw (SubT.sub (.refl a') |>.trans hc1))
    · exact hA b c (SubT.trans hw (SubT.arg (.refl b') |>.trans hc1))

/-- **The seed condition from `BandS`.** -/
theorem seedCond_of_bandS {μ V ζ θ : T} (hL : BandS μ V) (hz : psi μ z z ≤ fsD ζ θ) :
    SeedCond V ζ (etaOm μ) θ :=
  fun _ hu _ h0 => lt_of_lt_of_le (lt_Om_of_bandS hL hu h0) hz

end Ytosk
