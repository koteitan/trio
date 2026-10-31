/-
**WfQrH4 (2026-11-01): the `ω` layer step reduced to the single-summand case.**
An `ω` layer `Y → Y_N` (`DQ η true Y Y_N`) needs no shape hypothesis when both are below `ε₀` (`omega_DQ_small`)
or when both are `≥ ε₀` and `Y` has more than one summand (`omega_DQ_rest`).  `LayerF` adds these two cases to
`LayerOK`, asks `OmSide` only at the `η` of the given `DQ`, and fixes its `hQ0` (`OmSide1`; the original is
unsatisfiable on a single layer: `not_omSide_single`); `layer_step` and `bumpW_DQ3` are `layer_DQ` / `bumpW_DQ2` (WfQrL16) with `LayerF`.
-/
import Ytosk.WfQrL17

namespace Ytosk.WfQrH4
open T Ytosk Ytosk.WfQrL1 Ytosk.WfQrL2 Ytosk.WfQrL13 Ytosk.WfQrL16 Ytosk.WfQrL17

/-- **`OmSide` is unsatisfiable on a single layer**: its `hQ0` quantifies over every decomposition, and
`Y_N = 0 ++ (Y_N ++ 0)` forces `Y_N = 0`.  (frames.py tested the weaker "`Y` single → `Y_N` single".)  So `LayerOK`
(WfQrL16) holds on a single layer only through the `ε₀` / node shapes; `OmSide1` below fixes `hQ0`. -/
theorem not_omSide_single {η s b YN : T} (hYN : YN ≠ z) : ¬ OmSide η (psi s b z) YN := by
  rintro ⟨-, -, -, hQ0, -, -⟩
  have := hQ0 s b rfl z (psi s b z) z YN (by simp [app]) (by simp [app])
  exact hYN this

/-- `OmSide` with `hQ0` only for the single-last decomposition of the `DQ`. -/
def OmSide1 (η Y YN : T) : Prop :=
  isOT Y = true ∧ isOT YN = true ∧ ((Y < E0 ∧ YN < E0) ∨ (¬ Y < E0 ∧ ¬ YN < E0)) ∧
  (∀ s b, Y = psi s b z → ∀ B l lN Q, Y = app B l → (∃ s0 y0, l = psi s0 y0 z) → YN = app B (app Q lN) →
    DQ η false l lN → Q = z) ∧
  (∀ a b bN, Y = psi a b z → YN = psi a bN z → b ≠ z →
    (loOf a b = z → loOf a bN = z) ∧ (loOf a b ≠ z → hiOf a bN = hiOf a b ∧ loOf a bN ≠ z)) ∧
  (YN = fsD Y η → fsD (omega Y) η = omega (fsD Y η) ∧ fsD (omega Y) η < omega Y)

/-- **`omega_DQ_true` with `OmSide1`.** -/
theorem omega_DQ_true1 {η Y YN : T} (h : DQ η true Y YN) (hO : OmSide1 η Y YN) :
    DQ η false (omega Y) (omega YN) := by
  obtain ⟨hY, hYN, hsm, hQ0, hLo, hB⟩ := hO
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
      have hQz := hQ0 a b rfl B l lN Q eY ⟨s, y, hl⟩ eYN hd
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

/-- The layer fields: small, multi-summand, or one of the three shapes of `LayerOK`. -/
def LayerF (Y YN : T) : Prop :=
  (Y < E0 ∧ YN < E0) ∨
  (isOT Y = true ∧ isOT YN = true ∧ ¬ Y < E0 ∧ ¬ YN < E0 ∧ ∃ a b c, Y = psi a b c ∧ c ≠ z) ∨
  (∀ η, DQ η true Y YN → OmSide1 η Y YN) ∨
  -- the `ε₀` crossing and the node shape of `LayerOK`
  ((Y = E0 ∧ YN < E0 ∧ isOT E0 = true) ∨
    (∃ a B bN, Y = psi a (app B (psi (succ a) z z)) z ∧ YN = psi a bN z ∧
      isOT (psi a (app B (psi (succ a) z z)) z) = true ∧ isOT (psi a bN z) = true ∧
      ¬ psi a (app B (psi (succ a) z z)) z < E0 ∧ ¬ psi a bN z < E0 ∧
      loOf a (app B (psi (succ a) z z)) = z ∧ loOf a bN ≠ z ∧ hiOf a bN = B ∧ psi a bN z < psi (succ a) z z))

/-- **An `ω` layer step from `LayerF`.** -/
theorem layer_step {Y YN : T} (hd : ∃ η, DQ η true Y YN) (h : LayerF Y YN) :
    ∃ η', DQ η' false (omega Y) (omega YN) := by
  obtain ⟨η, hη⟩ := hd
  rcases h with ⟨h1, h2⟩ | ⟨hY, hYN, h1, h2, a, b, c, rfl, hc⟩ | hO | h
  · exact ⟨η, omega_DQ_small h1 h2 hη⟩
  · exact ⟨η, omega_DQ_rest hc hY hYN h1 h2 hη⟩
  · exact ⟨η, omega_DQ_true1 hη (hO η hη)⟩
  · exact layer_DQ ⟨η, hη⟩ (Or.inr h)

/-- **The bump term, two `ω` layers, each with `LayerF`.** -/
theorem bumpW_DQ3 {P0 K0 ok oN : T} (hok : ∃ s y, ok = psi s y z) (hd : ∃ η, DQ η false ok oN)
    (hG : isOT (app K0 ok) = true)
    (L1 : LayerF (app K0 ok) (app K0 oN))
    (L2 : LayerF (app P0 (omega (app K0 ok))) (app P0 (omega (app K0 oN)))) :
    ∃ η', DQ η' false (omega (app P0 (omega (app K0 ok)))) (omega (app P0 (omega (app K0 oN)))) := by
  obtain ⟨η, hη⟩ := hd
  obtain ⟨η1, d2⟩ := layer_step ⟨η, DQ.snoc K0 hok hη⟩ L1
  have hs : ∃ s y, omega (app K0 ok) = psi s y z := (single_omega hG).2
  exact layer_step ⟨η1, DQ.snoc P0 hs d2⟩ L2

/-- **The bump step of the engine from the two layer shapes** (`hBW2` of `qr_engineDQ2`). -/
theorem bump_step3 {M : Mat} {ρ : Valn} {i j k : Nat} {L K : List Nat} {oN : T}
    (hch : children M i = L ++ [j]) (hjb : col M j = bump M i) (hchj : children M j = K ++ [k])
    (hok : ∃ s y, ρ.o k = psi s y z)
    (hsL : ∀ t ∈ L.map (bumpTerm M ρ i), t = z ∨ Single t)
    (hsK : ∀ t ∈ K.map ρ.o ++ [ρ.o k], Single t) (hpK : (K.map ρ.o ++ [ρ.o k]).Pairwise (fun a b => b ≤ a))
    (hsK' : ∀ t ∈ K.map ρ.o ++ [oN], Single t) (hpK' : (K.map ρ.o ++ [oN]).Pairwise (fun a b => b ≤ a))
    (hpp : (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))]).Pairwise (fun a b => b ≤ a))
    (hgt : ∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [ρ.o k]))], one < t)
    (hpp' : (nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [oN]))]).Pairwise (fun a b => b ≤ a))
    (hgt' : ∀ t ∈ nzs (L.map (bumpTerm M ρ i)) ++ [omega (sumN (K.map ρ.o ++ [oN]))], one < t)
    (L1 : LayerF (app (sumN (K.map ρ.o)) (ρ.o k)) (app (sumN (K.map ρ.o)) oN))
    (L2 : LayerF (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (app (sumN (K.map ρ.o)) (ρ.o k))))
      (app (sumN (nzs (L.map (bumpTerm M ρ i)))) (omega (app (sumN (K.map ρ.o)) oN))))
    (hd : ∃ η, DQ η false (ρ.o k) oN) :
    ∃ η', DQ η' false (bumpW M ρ i) (bumpWQ M ρ i L K oN) := by
  rw [bumpW_eq_bumpWQ hch hjb hchj, bumpWQ_app hsL hsK hpK hpp hgt, bumpWQ_app hsL hsK' hpK' hpp' hgt']
  have hG : isOT (app (sumN (K.map ρ.o)) (ρ.o k)) = true := by
    rw [← sumN_snoc_dec hsK hpK]; exact (sumN_dec _ hsK hpK).1
  exact bumpW_DQ3 hok hd hG L1 L2

end Ytosk.WfQrH4
